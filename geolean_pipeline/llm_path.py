"""
A3 — LLM path (kernel-gated). For lemmas the deterministic transliterator can't
do, build a scaffold prompt from the oracle + port_map, call `claude -p`, and gate
the result through the SAME `#print axioms` kernel verifier.

Design (post prof-review, 2026-07-08):
  * Extraction hardening — only the proof BODY is spliced into a fixed theorem
    header; any top-level declaration keyword (`axiom`/`theorem`/`def`/…) in the
    model output is rejected, so the LLM cannot smuggle in its own axiom.
  * olean-precompiled fast verify — the candidate is checked in a tiny file that
    *imports* the prebuilt `Ch10` olean (final chapter, transitively pulls in the
    whole Ch02..Ch10 chain — every prior `<name>_c` in scope) instead of
    recompiling 511 lemmas each time.
  * Ltac in the prompt — the human-readable Coq tactic script (not just the
    machine `Show Proof` term) is shown; it maps almost 1-1 to Lean tactics.
  * Two attempts — attempt 1 MIRRORS the Coq proof term (faithful); attempt 2+
    is FREE-FORM idiomatic tactic mode (correct, not necessarily structure-
    preserving). The returned `mode` labels which, so the thesis' faithfulness
    claim stays pinned to the deterministic path + mirror successes.
  * First-error feedback + targeted premise injection — only the first Lean error
    (they cascade) is fed back; an `unknown identifier X` pulls X's signature into
    the next prompt.

The LLM never bypasses the kernel: a proof is accepted only if it compiles
axiom-clean (allowed: propext / Classical.choice / Quot.sound).
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import re, subprocess
import translit as T
import orchestrator as O
from src.oracle import (run_proof, extract_lemma_source, default_q_paths,
                        collect_geocoq_lemma_names)
from src.port_map import get_lean_signature

KNOWN = collect_geocoq_lemma_names(os.path.join(os.getcwd(), "theories"))
ID = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
LEAN_ROOT = "lean/geocoq_translate"
TRY_MOD = "GeocoqTranslate/Tarski_dev/LLMTry"
CLIMB_MOD = "GeocoqTranslate.Tarski_dev.Ch10"          # final chapter — imports the
                                                          # whole Ch02..Ch10 chain, so
                                                          # verify_one() sees every fold

# Top-level declaration keywords the model must NOT emit — the body is spliced
# into a fixed `theorem <name>_llm ... :=` header, so anything that opens a new
# declaration is an escape attempt (or a mistake) and is rejected outright.
FORBIDDEN = re.compile(
    r"(?<![\w'])(axiom|theorem|lemma|def|abbrev|instance|macro|"
    r"structure|class|opaque|partial|unsafe|@\[[^\]]*\]|sorry|admit|native_decide)"
    r"(?![\w'])")

PROMPT = """Translate this GeoCoq (Coq) proof to a Lean 4 proof.

Context: namespace `GeocoqTranslate.Tarski.Base`, with `open Tarski_neutral_dimensionless` \
and `open Tarski_neutral_dimensionless_with_decidable_point_equality`. Every earlier Tarski \
lemma is in scope under its `<coqname>_c` name (e.g. `cong_symmetry_c`), plus the Tarski \
axioms / class fields.

Prove exactly this theorem:
  theorem {name} {tail} := <YOUR PROOF>

{mode_instr}

Coq tactic script (the intent — maps almost 1-1 to Lean: destruct→rcases, assert→have, \
apply..with→exact ..):
{ltac}
{term_block}
Lean definitions of the predicates involved (unfold by building/destructing these anonymous \
constructors — e.g. `obtain ⟨h1, h2, T, hT⟩ := h` / `exact ⟨…⟩`):
{defs}

Lean signatures of lemmas you may use (implicit `{{}}` args are inferred — do NOT pass them; \
append `_c` to Coq lemma names for the ported versions):
{sigs}

Coq->Lean hypothesis names: {bmap}

Rules:
- Output ONLY what goes after `:=` — either a term or a `by` tactic block.
- NO markdown fences, NO explanation, NO `theorem`/`lemma`/`axiom`/`def` line, NO `sorry`.
- Use only the lemmas listed above (with `_c` suffix where ported), Lean/Mathlib basics \
(Or, And, Ne.symm, rcases, obtain, refine, exact, subst, intro), and the Tarski axioms.
- For an n-way `∧` goal use `by refine ⟨?_, ?_, …⟩` (one `?_` per conjunct — ∧ is \
right-nested) and prove each goal separately; when destructing use `obtain ⟨h1, h2, h3⟩ := h`.
- To rewrite with an equality prefer `rw [h] at …` over `subst` (controls direction).
- The theorem's binders/hypotheses are ALREADY bound in the signature — do NOT start with \
`fun` re-binding them (that shadows them); prove the conclusion directly (start with `by`).{extra}{err}"""

MIRROR_INSTR = ("STRATEGY: mirror the structure of the Coq proof term below as closely as "
                "possible (faithful translation).")
FREEFORM_INSTR = ("STRATEGY: the term-mirror attempt failed. Now write the SHORTEST correct "
                  "idiomatic Lean tactic proof you can (rcases/obtain/refine/exact). It need "
                  "NOT mirror the Coq term — only be correct and use the listed lemmas.")

# Tarski axioms / class fields (not `Lemma`s, absent from port_map) — shown so the
# scaffold can reference them.
AXIOM_SIGS = {
    "between_identity": "between_identity (A B : Tpoint) : Bet A B A → A = B",
    "inner_pasch": "inner_pasch (A B C P Q : Tpoint) : Bet A P C → Bet B Q C → ∃ X, Bet P X B ∧ Bet Q X A",
    "segment_construction": "segment_construction (A B C D : Tpoint) : ∃ E, Bet A B E ∧ Cong B E C D",
    "cong_identity": "cong_identity (A B C : Tpoint) : Cong A B C C → A = B",
    "five_segment": "five_segment (A A' B B' C C' D D' : Tpoint) : Cong A B A' B' → … (5-segment)",
    "point_equality_decidability": "point_equality_decidability (A B : Tpoint) : A = B ∨ A ≠ B",
}


CLIMB_PATH = os.path.join(LEAN_ROOT, "GeocoqTranslate/Tarski_dev/Climb_All.lean")
DEFS_PATH = os.path.join(LEAN_ROOT, "GeocoqTranslate/Tarski/Definitions.lean")
_CLIMB_SIGS = None
_DEFS = None


def _defs():
    """name -> full Lean `def` text from Tarski/Definitions.lean."""
    global _DEFS
    if _DEFS is None:
        _DEFS = {}
        src = open(DEFS_PATH).read()
        for blk in re.split(r"(?=^def )", src, flags=re.M):
            m = re.match(r"def (\w+)", blk)
            if m:
                _DEFS[m.group(1)] = blk.strip().split("\n\n")[0].strip()
    return _DEFS


def _defs_for(tail, ltac):
    """Definitions of every predicate in the statement/Ltac, transitively closed
    (OS mentions TS -> include TS too). The Ch09 hard-bucket failures were all
    unfold-class: the LLM cannot unfold a predicate it has never seen."""
    ds = _defs()
    want, frontier = set(), set(ID.findall(tail)) | set(ID.findall(ltac))
    while True:
        new = {t for t in frontier if t in ds} - want
        if not new:
            break
        want |= new
        frontier = set()
        for n in new:
            frontier |= set(ID.findall(ds[n]))
    return "\n".join(ds[n] for n in sorted(want))


def _climb_sigs():
    """name -> exact `<name>_c <signature>` one-liner, read from Climb_All itself.
    This is THE authoritative arg-order/explicitness source — showing it stops the
    LLM from guessing `_c` signatures (the dominant round-1/2 failure mode)."""
    global _CLIMB_SIGS
    if _CLIMB_SIGS is None:
        _CLIMB_SIGS = {}
        src = open(CLIMB_PATH).read()
        for blk in re.split(r"(?=^theorem \w+_c\b)", src, flags=re.M):
            m = re.match(r"theorem (\w+)_c\b", blk)
            if m and ":=" in blk:
                sig = " ".join(blk.split(":=", 1)[0].split())
                _CLIMB_SIGS[m.group(1)] = sig.replace("theorem ", "", 1)
    return _CLIMB_SIGS


def _sig_of(u):
    """Best-effort one-line signature for a Coq lemma / axiom name (as `_c` if ported)."""
    cs = _climb_sigs()
    if u in cs:
        return "  " + cs[u]                    # exact ported signature from Climb_All
    ms = get_lean_signature(u)["matches"]
    cone = [m for m in ms if any(cf in m["file"] for cf in T.CONE_FILES)]
    if cone:
        return "  " + cone[0]["signature"]
    if u in AXIOM_SIGS:
        return "  " + AXIOM_SIGS[u]
    if u in T.NAME_MAP and T.NAME_MAP[u] in AXIOM_SIGS:
        return "  " + AXIOM_SIGS[T.NAME_MAP[u]]
    if u in KNOWN:
        return f"  {u}_c  (ported Tarski lemma, in scope)"
    if u in T.ALLOW_AXIOMS or u in T.NAME_MAP:
        return f"  {T.NAME_MAP.get(u, u)}  (Tarski axiom / class field, in scope)"
    return None


def _sigs_for(pt, ltac=""):
    toks = set(ID.findall(pt)) | set(ID.findall(ltac))
    used = sorted(toks & (KNOWN | T.ALLOW_AXIOMS | set(T.NAME_MAP)))
    return "\n".join(s for s in (_sig_of(u) for u in used) if s)


def scaffold_prompt(coq_file, name, tail, binders, *, mode="mirror",
                    prev_error=None, extra_sigs=None):
    pt = run_proof(coq_file, name, default_q_paths())
    try:
        ltac = extract_lemma_source(coq_file, name)
    except Exception:
        ltac = "(tactic script unavailable)"
    try:                                       # binder map is best-effort — never fatal
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        bmap = str(dict(zip(ast[1] if ast[0] == "fun" else [], binders)))
    except Exception:
        bmap = "the theorem's hypotheses, in order: " + ", ".join(binders)

    if mode == "mirror" and len(pt) <= 4000:
        mode_instr = MIRROR_INSTR
        term_block = f"\nCoq's proof term (mirror this structure):\n{pt}\n"
    elif mode == "mirror":
        # giant terms (reflective machinery) blow the prompt and time out claude -p;
        # mirror the *tactic script* instead
        mode_instr = MIRROR_INSTR
        term_block = "\n(proof term too large to show — mirror the tactic script above)\n"
    else:
        mode_instr = FREEFORM_INSTR
        term_block = ""                        # free-form: skip the giant term blob
    extra = f"\n- Also available: {extra_sigs}" if extra_sigs else ""
    err = (f"\n\nYour previous attempt FAILED with this Lean error:\n{prev_error}\nFix it."
           if prev_error else "")
    return PROMPT.format(name=name, tail=tail, mode_instr=mode_instr, ltac=ltac,
                        term_block=term_block, defs=_defs_for(tail, ltac),
                        sigs=_sigs_for(pt, ltac), bmap=bmap, extra=extra, err=err)


def _sanitize(out):
    """Strip fences / stray headers, then reject any forbidden top-level construct.
    Returns (body, reason). reason is None on success."""
    blocks = re.findall(r"```(?:[a-zA-Z]+)?\s*\n?(.*?)```", out, re.S)
    if blocks:
        out = blocks[-1].strip()
    out = re.sub(r"(?s)^\s*(?:theorem|lemma)\s+\S+.*?:=\s*", "", out).strip()
    if not out:
        return None, "empty output"
    m = FORBIDDEN.search(out)
    if m:
        return None, f"forbidden token in output: {m.group(1)!r}"
    return out, None


def call_claude(prompt, timeout=540):
    """Returns (body, reason, meta). meta carries token usage / wallclock for the
    measurement ledger. Uses --output-format json so usage is machine-readable."""
    import json
    r = subprocess.run(["claude", "-p", "--output-format", "json", prompt],
                       capture_output=True, text=True, timeout=timeout)
    meta = {"in_tok": 0, "out_tok": 0, "ms": 0}
    text = r.stdout.strip()
    try:
        j = json.loads(text)
        text = j.get("result", "") or ""
        u = j.get("usage", {}) or {}
        meta = {"in_tok": u.get("input_tokens", 0),
                "out_tok": u.get("output_tokens", 0),
                "ms": j.get("duration_ms", 0)}
    except Exception:
        pass                                    # non-JSON (older CLI) -> raw text, zero usage
    body, why = _sanitize(text)
    return body, why, meta


def _first_error(out, name):
    """First Lean error block (they cascade — later ones are noise) + any unknown id."""
    lines = out.splitlines()
    idxs = [i for i, l in enumerate(lines) if re.search(r":\d+:\d+: error", l)]
    if not idxs:
        # axiom-clean line? then no error. else raw tail.
        return None, None
    start = idxs[0]
    end = idxs[1] if len(idxs) > 1 else len(lines)
    block = "\n".join(lines[start:end]).strip()[:800]
    unk = re.search(r"[Uu]nknown (?:identifier|constant) [`']([\w'.]+)[`']", block)
    return block, (unk.group(1) if unk else None)


def verify_one(name, tail, proof):
    """Compile the candidate as `<name>_llm` importing the prebuilt Climb_All olean
    (full cross-chapter context). Returns (ok, first_error, unknown_id).
    Per-lemma try-file (LLMTry_<name>.lean) so verifies can run in parallel."""
    try_mod = f"GeocoqTranslate/Tarski_dev/LLMTry_{name}"
    path = os.path.join(LEAN_ROOT, try_mod + ".lean")
    kw = ":= by" if proof.lstrip().startswith("by") else ":="
    pbody = proof.lstrip()[2:] if proof.lstrip().startswith("by") else "  " + proof
    src = [
        f"import {CLIMB_MOD}",
        "namespace GeocoqTranslate.Tarski.Base",
        "open Tarski_neutral_dimensionless",
        "open Tarski_neutral_dimensionless_with_decidable_point_equality",
        "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]",
        "", f"theorem {name}_llm {tail} {kw}", pbody, "",
        f"#print axioms GeocoqTranslate.Tarski.Base.{name}_llm",
        "end GeocoqTranslate.Tarski.Base",
    ]
    open(path, "w").write("\n".join(src))
    try:
        r = subprocess.run(["lake", "env", "lean", try_mod + ".lean"], cwd=LEAN_ROOT,
                           capture_output=True, text=True, timeout=600)
    finally:
        try:
            os.remove(path)
        except OSError:
            pass
    out = r.stdout + r.stderr
    # ANY error disqualifies — `#print axioms` can still print a sorryAx-free list
    # while the kernel rejected the declaration (e.g. "declaration has metavariables"),
    # which previously produced a false-CLEAN. Errors first, axioms second.
    if (r.returncode == 0 and not re.search(r"error", out)
            and re.search(rf"'\S+{name}_llm' (?:depends on axioms: \[(?!.*sorryAx)[^\]]*\]|does not depend)",
                          out.replace("\n", " "))):
        return True, None, None
    err, unk = _first_error(out, name)
    return False, err or out[:400], unk


LEDGER = os.path.join(REPO, "geolean_pipeline", ".llm_ledger.jsonl")
_LEDGER_LOCK = __import__("threading").Lock()


def _log_ledger(rec):
    import json
    with _LEDGER_LOCK:
        with open(LEDGER, "a") as f:
            f.write(json.dumps(rec) + "\n")


def llm_translate(coq_file, name, tail, binders, retries=3, extra0=None):
    """Attempt 1 = mirror (faithful); attempt 2+ = free-form idiomatic.
    Returns (proof, attempts, mode) or (None, attempts, None). Appends a per-lemma
    record (attempts, tokens, wallclock, mode, outcome) to the measurement ledger.
    extra0: extra signature/hint text injected into every prompt (e.g. the col-helper
    lemmas that Coq's reflective ColR tactic abbreviates)."""
    prev, extra = None, extra0
    in_tok = out_tok = ms = 0
    ptoks = len(T.tok(run_proof(coq_file, name, default_q_paths())))   # proof-term size
    for attempt in range(retries + 1):
        mode = "mirror" if attempt == 0 else "freeform"
        body, why, meta = call_claude(scaffold_prompt(
            coq_file, name, tail, binders, mode=mode, prev_error=prev, extra_sigs=extra))
        in_tok += meta["in_tok"]; out_tok += meta["out_tok"]; ms += meta["ms"]
        if body is None:                       # sanitizer rejected the output
            prev = why
            continue
        ok, err, unk = verify_one(name, tail, body)
        if ok:
            m = "mirror-faithful" if attempt == 0 else "freeform"
            _log_ledger(dict(name=name, outcome="clean", mode=m, attempts=attempt + 1,
                             ptoks=ptoks, in_tok=in_tok, out_tok=out_tok, ms=ms))
            return body, attempt + 1, m
        prev = err
        if unk:                                # targeted premise injection for next try
            s = _sig_of(unk.split(".")[-1].removesuffix("_c"))
            extra = s.strip() if s else None
    _log_ledger(dict(name=name, outcome="fail", mode=None, attempts=retries + 1,
                     ptoks=ptoks, in_tok=in_tok, out_tok=out_tok, ms=ms))
    return None, retries + 1, None


if __name__ == "__main__":
    import json
    coq = "theories/Main/Tarski_dev/Ch05_bet_le.v"
    lean = f"{LEAN_ROOT}/GeocoqTranslate/Tarski_dev/Ch05_bet_le.lean"
    stubs = O.parse_stubs(lean)
    targets = [n for n in ["le_cases", "l5_5_2"] if n in stubs]
    for n in targets:
        tail, binders = stubs[n]
        proof, tries, mode = llm_translate(coq, n, tail, binders)
        if proof:
            print(f"✅ {n}: VERIFIED clean [{mode}] in {tries} attempt(s)")
            print("     " + proof.replace("\n", "\n     ")[:300])
        else:
            print(f"❌ {n}: no clean proof in {tries} attempts")
        print()
