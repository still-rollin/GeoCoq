"""
Cascade-first / escalate-on-leverage pipeline for filling sorries in
Ch11+ upper chapters.

Step 1 (translate statements) is already done elsewhere (gen_stubs / translit's
deterministic stub generation) -- every Ch11-16a theorem already has a real
Lean statement, `:= sorry` or a real body. This file starts at Step 2.

Step 2 (fill via automation): for each still-`sorry` lemma, first try pure
automation with NO Coq consultation at all:
  (a) `Tfinish` / `TfinishA` / `aesop` directly after `intro` -- the ported
      reflective closers (colr/cong_r/assert_diffs) plus angle-congruence
      closure, zero LLM cost;
  (b) if that fails, ONE single-shot "sledgehammer" LLM call -- goal +
      available lemma signatures + automation macros, no Coq proof shown, no
      retries. This is the closest analog to Isabelle's sledgehammer: throw
      the goal and the toolbox at the model once and see if it lands without
      any deeper reasoning about Coq's actual derivation.

Step 3 (escalate on failure): pull ONLY the witness / point-construction steps
out of Coq's real proof term (`ex_intro` nodes -- an auxiliary point built via
`segment_construction`, `symmetric_point_construction`, etc.). These are
exactly what blind automation can never invent on its own. Feed them as
stepping stones to a fuller LLM pass (a real "agentic" attempt: tactic script
+ witness hints + lemma signatures + automation macros), retried a few times
with the actual Lean error fed back each round.

Step 4 (repeat): loop Step 2+3 across the WHOLE chapter, round after round,
until a round closes nothing new. Closing one lemma can unlock automation or
a shorter LLM proof for something that depends on it later in the file --
cascade-first, not one-shot-per-lemma.

Every accepted proof is kernel-gated exactly like the rest of this project:
`#print axioms`, only propext/Classical.choice/Quot.sound allowed, never
sorryAx. Nothing is trusted on "it compiled" alone.
"""
import os, sys, re, json, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "geolean_oracle"))

import climb_upper as C
import llm_path as L
import translit as T
from src.oracle import run_proof, default_q_paths

LEDGER = os.path.join(C.REPO, "geolean_pipeline", ".cascade_ledger.jsonl")


def _log(rec):
    rec["ts"] = time.time()
    with open(LEDGER, "a") as f:
        f.write(json.dumps(rec) + "\n")


# --------------------------------------------------------------------------
# Step 2a -- blind automation, zero LLM cost
# --------------------------------------------------------------------------

BLIND_TEMPLATES = [
    ("finish",
     "first\n  | Tfinish\n  | TfinishA\n  | aesop"),
    ("or-split+finish",
     "first\n  | (left; first | Tfinish | TfinishA | aesop)\n"
     "  | (right; first | Tfinish | TfinishA | aesop)"),
    ("constructor+finish",
     "constructor <;> first | Tfinish | TfinishA | aesop"),
    ("exfalso+finish",
     "exfalso\n  first\n  | Tfinish\n  | TfinishA\n  | aesop"),
    ("or-split+exfalso+finish",
     "first\n"
     "  | (left; first | Tfinish | TfinishA | aesop | (exfalso; first | Tfinish | TfinishA | aesop))\n"
     "  | (right; first | Tfinish | TfinishA | aesop | (exfalso; first | Tfinish | TfinishA | aesop))"),
]


def blind_automation_attempt(name, tail, nb, climb_mod, tier_var):
    """Step 2a -- no Coq consultation, no LLM. Tries several zero-cost tactic
    SHAPES in sequence (plain closer, disjunction-introduction + closer,
    constructor-split + closer, exfalso + closer, and combinations), each
    kernel-verified independently. Widened 2026-07-15: the original
    single-shape version never tried `left`/`right` before dispatching to
    Tfinish/TfinishA/aesop, so any `_ ∨ _`-shaped goal whose true disjunct was
    directly closeable by colr/cong_r/Tconga forward-closure was invisible to
    it -- a real, recoverable gap on lemmas like `... -> Out B C C' \\/ TS A B
    C C'`, NOT a fix for genuinely deep proofs needing a fresh witness
    construction (those still need Step 3 or interactive work). Returns
    (body, nb) on the first kernel-clean template, else None."""
    print(f"    [2a] blind automation ({len(BLIND_TEMPLATES)} shapes, no LLM)...", end=" ", flush=True)
    bnames = " ".join(f"b{i}" for i in range(nb))
    last_err = None
    for label, tactic in BLIND_TEMPLATES:
        body = f"by\n  intro {bnames}\n  {tactic}"
        ok, err, _unk = L.verify_one(name, tail, body, climb_mod=climb_mod, nb=nb, tier_var=tier_var)
        if ok:
            print(f"CLOSED via [{label}]", flush=True)
            return (body, nb)
        last_err = err
    print(f"failed all {len(BLIND_TEMPLATES)} shapes: "
          f"{(last_err or '').splitlines()[0][:120] if last_err else 'no automation matched'}", flush=True)
    return None


# --------------------------------------------------------------------------
# Step 2b -- single-shot "sledgehammer" LLM (no Coq proof shown, one attempt)
# --------------------------------------------------------------------------

SLEDGEHAMMER_PROMPT = """Prove this Lean 4 theorem. This is a SINGLE blind attempt -- \
do not reason deeply about the specific derivation, just try the available automation \
and known lemmas directly, the way a sledgehammer/hammer tactic would.

theorem {name} {tail} := <YOUR PROOF>

The theorem's binders/hypotheses are NOT bound yet -- start with \
`by intro <name for each binder/hypothesis, in order>` as your FIRST tactic.

Automation available: `Tfinish` (closes Col/Cong/≠ goals from hypotheses already in \
context via collinearity+congruence closure), `TfinishA` (same, plus CongA/LeA/LtA/OS/TS \
angle-congruence closure), plain `aesop`. Try one of these directly after `intro`, or a \
short `obtain`/`exact` sequence using ONLY the lemmas listed below if the goal needs one \
extra step first.

Lean DEFINITIONS of any compound predicate in the goal (unfold by destructuring/building \
these exact ∧/∃ shapes -- do NOT guess the field order from the name alone, deeply nested \
predicates like `CongA`/`InAngle`/`SuppA` have non-obvious layouts):
{defs}

Lean signatures of lemmas you may use (append `_c` to Coq lemma names for the ported \
versions, implicit `{{}}` args are inferred -- do NOT pass them):
{sigs}

Rules:
- Output ONLY what goes after `:=` -- a `by` tactic block.
- NO markdown fences, NO explanation, NO `theorem`/`lemma`/`axiom`/`def` line, NO `sorry`.
"""


def sledgehammer_attempt(coq_path, name, tail, nb, climb_mod, tier_var):
    """One single-shot LLM call with the goal + toolbox, no Coq proof/tactic
    script shown at all. Returns (body, nb) on success, else None."""
    print(f"    [2b] sledgehammer (single-shot LLM, no Coq proof shown)...", end=" ", flush=True)
    pt = run_proof(coq_path, name, default_q_paths())
    sigs = L._sigs_for(pt, "")
    defs = L._defs_for(tail, "")
    prompt = SLEDGEHAMMER_PROMPT.format(name=name, tail=tail, sigs=sigs, defs=defs)
    body, why, meta = L.call_claude(prompt, timeout=180)
    if body is None:
        print(f"LLM gave no usable output ({why})", flush=True)
        return None
    ok, err, _unk = L.verify_one(name, tail, body, climb_mod=climb_mod, nb=nb, tier_var=tier_var)
    if ok:
        print("CLOSED", flush=True)
        return (body, nb)
    print(f"failed: {(err or '').splitlines()[0][:120] if err else 'kernel rejected'}", flush=True)
    return None


# --------------------------------------------------------------------------
# Step 3 -- escalate: pull witness/point-construction steps from Coq's real
# proof, feed them as stepping stones to a fuller, multi-attempt LLM pass.
# --------------------------------------------------------------------------

def extract_witness_hints(coq_path, name):
    """Only the `introduce witness: ...` lines from the full waypoint walk --
    automation can never invent an auxiliary point (segment_construction,
    symmetric_point_construction, ...); everything else in the proof (lemma
    calls, case splits) is either mechanical or already visible via the
    tactic script, so is deliberately NOT included here -- this is meant to
    be a short, high-leverage hint list, not a second roadmap."""
    try:
        pt = run_proof(coq_path, name, default_q_paths())
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        body = ast[2] if ast[0] == "fun" else ast
        lines = L._waypoint_lines(body, 0)
        return [l.strip("- ").strip() for l in lines if "introduce witness" in l]
    except Exception:
        return []


ESCALATE_PROMPT = """Translate this GeoCoq (Coq) proof to a Lean 4 proof. Blind automation \
already failed on this one -- it needs a real derivation.

Context: namespace `GeocoqTranslate.Tarski.Base`, every earlier Tarski lemma is in scope \
under its `<coqname>_c` name.

Prove exactly this theorem:
  theorem {name} {tail} := <YOUR PROOF>

The theorem's binders/hypotheses are NOT bound yet -- start with `by intro <name for each \
binder/hypothesis, in order>` as your FIRST tactic.
{witness_block}
Coq tactic script (the intent -- maps almost 1-1 to Lean: destruct->rcases, assert->have, \
apply..with->exact ..). WARNING: Coq lemma names in this script may use a double underscore \
(e.g. `acute_obtuse__lta`) -- the actual Lean identifier ALWAYS collapses this to a single `_` \
plus a `_c` suffix (e.g. `acute_obtuse_lta_c`). NEVER call a name with `__` in it; if you see \
one here, single it and append `_c`. Only use names from the signatures/examples lists below, \
which already have the correct Lean spelling:
{ltac}

Lean DEFINITIONS of any compound predicate in the goal/hypotheses (unfold by destructuring/ \
building these EXACT ∧/∃ shapes -- do NOT guess the field order from the name alone or from \
what a previous attempt assumed; deeply nested predicates like `CongA`/`InAngle`/`SuppA` have \
non-obvious layouts, e.g. `CongA A B C D E F` is `A≠B ∧ C≠B ∧ D≠E ∧ F≠E ∧ ∃ A' C' D' F', Bet B A A' \
∧ Cong A A' E D ∧ Bet B C C' ∧ Cong C C' E F ∧ Bet E D D' ∧ Cong D D' B A ∧ Bet E F F' ∧ \
Cong F F' B C ∧ Cong A' C' D' F'` -- an `obtain` for it needs exactly 4 distinctness names, \
4 point names, then alternating Bet/Cong proof names matching that order, one flat pattern, \
no extra nesting):
{defs}

Lean signatures of lemmas you may use (append `_c` to Coq lemma names, implicit `{{}}` args \
inferred -- do NOT pass them):
{sigs}

Rules:
- Use `obtain`/`rcases` to destructure hypotheses, `have h : P := ...` for intermediate \
facts. Use `colr`, `cong_r`, `Tfinish`, or `TfinishA` to close any Col/Cong/≠/CongA sub-goal \
that follows mechanically from what's already in context -- do NOT hand-chain \
`col_permutation_i_c`/`cong_*_c` lemmas when one of these closes it directly.
- Output ONLY what goes after `:=` -- a `by` tactic block.
- NO markdown fences, NO explanation, NO `theorem`/`lemma`/`axiom`/`def` line, NO `sorry`.
{teacher_hint}{err}"""


# --------------------------------------------------------------------------
# Step 3.5 -- teacher: after every BATCH of failed attempts, a SEPARATE LLM
# call diagnoses the ROOT CAUSE across the whole batch (not just the last
# attempt's local error) and produces one actionable hint for the next
# batch. Local error-feedback alone can loop on the same mistake forever --
# confirmed live on `bet_conga_bet_c`: 6 independent escalate attempts, each
# only shown ITS OWN previous error, all failed on variants of the exact
# same root cause (mis-destructuring CongA's nested existential) without
# ever self-correcting. A pass that looks at the PATTERN across several
# attempts at once can name that root cause explicitly, the way the
# after-the-fact human analysis in this session's case study did.
# --------------------------------------------------------------------------

TEACHER_PROMPT = """You are reviewing {n} FAILED attempts at a Lean 4 proof, each shown \
with its exact kernel error. Your job is NOT to write the proof -- it is to diagnose the \
ROOT CAUSE shared across these attempts (if there is one) and give ONE short, concrete, \
actionable hint that would help a fresh attempt avoid it. Look for a PATTERN across \
attempts, not just the most recent error.

IMPORTANT: you have NO tool access and cannot look anything up -- you can only reason from \
the theorem statement, the attempts, and their errors shown below. Never suggest an action \
like "check X using tool Y" or "verify the definition with the hover/search tool" -- the \
model reading your hint next has no tools either and will get confused trying to follow a \
suggestion it cannot execute. If you don't have enough information to state the exact fix \
(e.g. you'd need to see a definition that isn't shown to you), say what's MISSING instead of \
telling the next attempt to go look it up itself.

Theorem being proved:
  theorem {name} {tail} := <PROOF>

{attempts_block}

If the attempts share a structural misunderstanding (e.g. consistently getting a \
destructuring/`obtain` pattern wrong for a specific definition, misordering arguments to a \
specific lemma, missing a needed intermediate fact), state EXACTLY what the correct \
pattern/fact is, using only what's visible in the attempts/errors above. If the failures \
look unrelated (different causes each time, no shared pattern), say so plainly instead of \
inventing a pattern that isn't there.

Output ONLY the hint itself (2-5 sentences, or a short code fragment if that's clearer) -- \
no preamble, no "Looking at these attempts...", just the diagnosis and fix."""


def teacher_diagnose(name, tail, batch):
    """batch: list of (proof_body_or_None, error_or_reason) tuples from one
    failed batch. Returns a hint string, or "" if the call itself fails
    (never blocks the cascade -- a missing hint just means the next batch
    runs with plain error-feedback, same as before this feature existed)."""
    blocks = []
    for i, (body, err) in enumerate(batch, 1):
        b = body if body else "(no proof produced)"
        blocks.append(f"--- Attempt {i} ---\nProof:\n{b}\n\nError:\n{err}\n")
    print(f"    [teacher] diagnosing {len(batch)} failed attempts...", end=" ", flush=True)
    prompt = TEACHER_PROMPT.format(n=len(batch), name=name, tail=tail,
                                   attempts_block="\n".join(blocks))
    try:
        r = subprocess.run(["claude", "-p", "--output-format", "json", prompt],
                           capture_output=True, text=True, timeout=180)
        j = json.loads(r.stdout.strip())
        hint = (j.get("result") or "").strip()
    except Exception as e:
        print(f"teacher call failed ({e}), continuing without a hint", flush=True)
        return ""
    if not hint:
        print("no hint produced", flush=True)
        return ""
    print("done", flush=True)
    print(f"    [teacher] hint: {hint[:300]}", flush=True)
    return hint


def escalate_attempt(coq_path, name, tail, nb, climb_mod, tier_var, retries=5, batch_size=3):
    """Multi-attempt LLM pass with witness hints pulled from Coq's real proof
    as stepping stones. Runs in BATCHES of `batch_size`; after each failed
    batch, Step 3.5 (teacher_diagnose) reviews the whole batch and produces
    one hint injected into every prompt in the next batch, on top of the
    usual single-previous-error feedback."""
    witnesses = extract_witness_hints(coq_path, name)
    print(f"    [3] escalate: witnesses from Coq oracle = "
          f"{witnesses if witnesses else '(none found -- no auxiliary points in this proof)'}",
          flush=True)
    witness_block = (
        "\nWitness/auxiliary-point steps Coq's proof constructs (automation can't invent "
        "these -- you likely need `obtain`/`have` for each, using segment_construction-style "
        "lemmas):\n" + "\n".join(f"- {w}" for w in witnesses) + "\n"
        if witnesses else "")
    try:
        ltac = L.extract_lemma_source(coq_path, name)
    except Exception:
        ltac = "(tactic script unavailable)"
    pt = run_proof(coq_path, name, default_q_paths())
    sigs = L._sigs_for(pt, ltac)
    defs = L._defs_for(tail, ltac)
    prev_err = None
    teacher_hint = ""
    batch = []
    for attempt in range(retries + 1):
        print(f"    [3] escalate attempt {attempt + 1}/{retries + 1}...", end=" ", flush=True)
        err_block = (f"\nYour previous attempt FAILED with this Lean error:\n{prev_err}\nFix it.\n"
                     if prev_err else "")
        hint_block = (f"\nHint from reviewing earlier failed attempts as a batch:\n{teacher_hint}\n"
                     if teacher_hint else "")
        prompt = ESCALATE_PROMPT.format(name=name, tail=tail, witness_block=witness_block,
                                        ltac=ltac, sigs=sigs, defs=defs, err=err_block,
                                        teacher_hint=hint_block)
        body, why, meta = L.call_claude(prompt)
        if body is None:
            print(f"LLM gave no usable output ({why})", flush=True)
            prev_err = why
            batch.append((None, why))
            continue
        ok, err, unk = L.verify_one(name, tail, body, climb_mod=climb_mod, nb=nb, tier_var=tier_var)
        if ok:
            print("CLOSED", flush=True)
            return (body, nb)
        print(f"failed: {(err or '').splitlines()[0][:120] if err else 'kernel rejected'}", flush=True)
        prev_err = err
        batch.append((body, err))
        if len(batch) >= batch_size and attempt < retries:
            teacher_hint = teacher_diagnose(name, tail, batch)
            batch = []
    return None


# --------------------------------------------------------------------------
# Per-lemma dispatcher: Step 2a -> 2b -> 3, first success wins
# --------------------------------------------------------------------------

def det_mirror_attempt(coq_path, name, tail, nb, climb_mod, tier_var):
    """Step 1.5 -- deterministic mirror of Coq's OWN elaborated proof term
    (translit.py's det_attempt), kernel-verified before trusting it. Free (no
    LLM). Coq's term is already fully resolved (no eapply/metavariables left
    -- Coq's elaborator settled those during Show Proof), so when translit's
    emitter can mirror it faithfully this closes the lemma with zero guessing
    of any kind. Confirmed live 2026-07-15: `bet_conga_bet_c` resisted 18+ LLM
    attempts across three prompt-architecture iterations, then closed via
    this path alone once a translit.py bug (over-eager colr/cong_r collapse
    hiding a real nested lemma call) was fixed -- the blocker was never the
    LLM's reasoning, it was the deterministic translator silently discarding
    a derivation it could have mirrored correctly."""
    print(f"    [1.5] deterministic mirror (Coq's own resolved term, no LLM)...",
          end=" ", flush=True)
    try:
        body_nb = C.det_attempt(coq_path, name)
    except Exception as e:
        print(f"det_attempt raised ({e})", flush=True)
        return None
    if body_nb is None:
        print("translit could not mirror this term", flush=True)
        return None
    body, det_nb = body_nb
    ok, err, _unk = L.verify_one(name, tail, body, climb_mod=climb_mod, nb=det_nb, tier_var=tier_var)
    if ok:
        print("CLOSED", flush=True)
        return (body, det_nb)
    print(f"mirrored but kernel rejected it: {(err or '').splitlines()[0][:120] if err else '?'}",
          flush=True)
    return None


def attempt_lemma(coq_path, name, tail, climb_mod, tier_var):
    t0 = time.time()
    print(f"\n>>> {name}_c :: {tail.strip()[:140]}", flush=True)
    pt = run_proof(coq_path, name, default_q_paths())
    ast = T.parse_term(T.P(T.tok(pt)), stop={None})
    while ast[0] == "paren":
        ast = ast[1]
    nb = len(ast[1]) if ast[0] == "fun" else 0

    r = det_mirror_attempt(coq_path, name, tail, nb, climb_mod, tier_var)
    if r:
        _log(dict(name=name, stage="1.5-det-mirror", outcome="clean"))
        print(f"=== {name}_c CLOSED via 1.5-det-mirror ({time.time()-t0:.1f}s) ===", flush=True)
        return r, "1.5-det-mirror"

    r = blind_automation_attempt(name, tail, nb, climb_mod, tier_var)
    if r:
        _log(dict(name=name, stage="2a-blind-automation", outcome="clean"))
        print(f"=== {name}_c CLOSED via 2a-blind-automation ({time.time()-t0:.1f}s) ===", flush=True)
        return r, "2a-blind-automation"

    r = sledgehammer_attempt(coq_path, name, tail, nb, climb_mod, tier_var)
    if r:
        _log(dict(name=name, stage="2b-sledgehammer", outcome="clean"))
        print(f"=== {name}_c CLOSED via 2b-sledgehammer ({time.time()-t0:.1f}s) ===", flush=True)
        return r, "2b-sledgehammer"

    r = escalate_attempt(coq_path, name, tail, nb, climb_mod, tier_var)
    if r:
        _log(dict(name=name, stage="3-escalate-witness", outcome="clean"))
        print(f"=== {name}_c CLOSED via 3-escalate-witness ({time.time()-t0:.1f}s) ===", flush=True)
        return r, "3-escalate-witness"

    _log(dict(name=name, stage="all", outcome="fail"))
    print(f"=== {name}_c FAILED all stages ({time.time()-t0:.1f}s) ===", flush=True)
    return None, None


# --------------------------------------------------------------------------
# Step 4 -- cascade: repeat rounds over the whole chapter until dry
# --------------------------------------------------------------------------

def run_chapter(coq_stem: str, lean_stem: str, tier: str, max_rounds: int = 6):
    coq_path = f"{C.COQ_ROOT}/{coq_stem}.v"
    lean_path = f"{C.LEAN}/{lean_stem}.lean"
    climb_mod = C._module_of(lean_path)
    tier_var = C.TIER_VARS[tier]

    for name, stmt in C.parse_stub_blocks(lean_path).items():
        T.LOCAL_SIGS.setdefault(name, T.lean_binder_kinds(f"theorem {name}_c : {stmt}"))
    L.seed_upper_sigs(sorted(__import__("glob").glob(f"{C.LEAN}/*.lean")))

    coq_text = open(coq_path).read()
    coq_names_raw = re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w[\w']*)",
                               coq_text, re.M)
    coq_names = [n.replace("__", "_") for n in coq_names_raw]

    total_closed = 0
    for rnd in range(1, max_rounds + 1):
        stub_blocks = C.parse_stub_blocks(lean_path)
        still_sorry = sorted(stub_blocks.keys())
        if not still_sorry:
            print(f"{lean_stem}: nothing left to attempt, stopping.", flush=True)
            break
        print(f"{lean_stem}: round {rnd}, {len(still_sorry)} still sorry", flush=True)

        bodies = {}
        by_stage = {}
        closed_so_far = 0
        for i, n in enumerate(still_sorry, 1):
            print(f"\n[{i}/{len(still_sorry)} this round, {closed_so_far} closed so far]", flush=True)
            coq_name = C._resolve_coq_name(n, coq_names_raw)
            tail = ":" + stub_blocks[n]
            try:
                result, stage = attempt_lemma(coq_path, coq_name, tail, climb_mod, tier_var)
            except Exception as e:
                result, stage = None, f"EXC:{e}"
                print(f"=== {n}_c EXCEPTION: {e} ===", flush=True)
            if result:
                bodies[n] = result
                by_stage[n] = stage
                closed_so_far += 1

        if not bodies:
            print(f"{lean_stem}: round {rnd} closed 0 -- dry, stopping cascade.", flush=True)
            break

        all_blocks = C.parse_all_blocks(lean_path)
        preserved = {n: all_blocks[n] for n in coq_names if n in all_blocks and n not in stub_blocks}
        ambient = C.ambient_prelude(coq_path)
        lean_text_now = open(lean_path).read()
        extra_imports = [m.group(1) for m in re.finditer(r"^import (\S+)\s*$", lean_text_now, re.M)
                         if m.group(1) != f"GeocoqTranslate.Tarski_dev.{coq_stem}"]
        if "GeocoqTranslate.Tarski_dev.TarskiFinish" not in extra_imports:
            extra_imports.append("GeocoqTranslate.Tarski_dev.TarskiFinish")
        if lean_stem != "Ch11" and "GeocoqTranslate.Tarski_dev.TarskiConA" not in extra_imports:
            extra_imports.append("GeocoqTranslate.Tarski_dev.TarskiConA")
        prev_lean = re.search(r"^import GeocoqTranslate\.Tarski_dev\.(\w+)\s*$",
                              lean_text_now, re.M).group(1)

        clean, tainted, hole, rounds, rescued = C.fold_and_verify(
            lean_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved,
            ambient, isolate=True, extra_imports=extra_imports)
        if rounds is None:
            print(f"{lean_stem}: round {rnd} repair loop did not converge, stopping.", flush=True)
            break

        newly_closed = [n for n in bodies if n in clean]
        total_closed += len(newly_closed)
        for n in newly_closed:
            print(f"  closed {n} via {by_stage.get(n)}", flush=True)
        print(f"{lean_stem}: round {rnd} closed {len(newly_closed)} "
              f"(attempted {len(still_sorry)}, cascade_rescued={rescued})", flush=True)
        if not newly_closed:
            print(f"{lean_stem}: round {rnd} nothing survived the repair loop, stopping.", flush=True)
            break

    print(f"{lean_stem}: cascade done, {total_closed} total closed.", flush=True)
    return total_closed


if __name__ == "__main__":
    chapter = sys.argv[1] if len(sys.argv) > 1 else "Ch11"
    entry = next(c for c in C.CHAPTERS if c[1] == chapter)
    coq_stem, lean_stem, tier = entry
    run_chapter(coq_stem, lean_stem, tier)
