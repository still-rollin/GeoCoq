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
                        collect_geocoq_lemma_names, extract_resolved_calls)
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
apply..with→exact ..). WARNING: Coq lemma names here may use a double underscore (e.g. \
`acute_obtuse__lta`) — the real Lean identifier ALWAYS collapses this to a single `_` plus a \
`_c` suffix (e.g. `acute_obtuse_lta_c`). NEVER call a name with `__` in it; if you see one \
here, single it and append `_c`. Only use names from the signatures/examples lists below, \
which already have the correct Lean spelling:
{ltac}
{term_block}{waypoints}
Lean definitions of the predicates involved (unfold by building/destructing these anonymous \
constructors — e.g. `obtain ⟨h1, h2, T, hT⟩ := h` / `exact ⟨…⟩`):
{defs}

Lean signatures of lemmas you may use (implicit `{{}}` args are inferred — do NOT pass them; \
append `_c` to Coq lemma names for the ported versions):
{sigs}

Worked examples — how THIS Coq proof actually called each lemma at least once, in Coq's own \
argument order (Coq's own count can differ from the Lean signature above since implicits are \
dropped there — match each argument by its ROLE/POSITION among the points, not by literal \
count):
{examples}

Coq->Lean hypothesis names: {bmap}

Rules:
- Output ONLY what goes after `:=` — either a term or a `by` tactic block.
- NO markdown fences, NO explanation, NO `theorem`/`lemma`/`axiom`/`def` line, NO `sorry`.
- Use only the lemmas listed above (with `_c` suffix where ported), Lean/Mathlib basics \
(Or, And, Ne.symm, rcases, obtain, refine, exact, subst, intro), and the Tarski axioms.
- For an n-way `∧` goal use `by refine ⟨?_, ?_, …⟩` (one `?_` per conjunct — ∧ is \
right-nested) and prove each goal separately; when destructing use `obtain ⟨h1, h2, h3⟩ := h`.
- To rewrite with an equality prefer `rw [h] at …` over `subst` (controls direction).
- {bound_rule}{extra}{err}"""

MIRROR_INSTR = ("STRATEGY: mirror the structure of the Coq proof term below as closely as "
                "possible (faithful translation).")
FREEFORM_INSTR = ("STRATEGY: the term-mirror attempt failed. Now write the SHORTEST correct "
                  "idiomatic Lean tactic proof you can (rcases/obtain/refine/exact). It need "
                  "NOT mirror the Coq term — only be correct and use the listed lemmas.")
# Julien's two-step methodology (validated on real lemmas — see JulienTest_*.lean in this
# same directory): (1) blind automation FIRST, no Coq consultation — often just closes it;
# (2) only when that fails, read Coq's proof for its WITNESS/insight (the thing automation
# can never invent on its own, e.g. "extend segment C-A beyond A by |CA|" or "the point Y from
# destructuring Orth") and write a normal obtain/have-based Lean proof around that witness,
# leaning on `colr`/`cong_r`/`Tfinish`/`TfinishA` for every mechanical Col/Cong/distinctness
# sub-step instead of hand-chaining permutation lemmas.
JULIEN_INSTR = ("STRATEGY (try this first): Step 1 — after your `intro`, try closing the goal "
                "with pure automation and nothing else: `Tfinish` (closes Col/Cong/≠ goals from "
                "hypotheses already in context via collinearity+congruence closure), `TfinishA` "
                "(same, plus angle-congruence closure — try this if CongA/LeA/LtA/OS/TS is "
                "involved), or plain `aesop`. If one of these alone finishes the proof, USE ONLY "
                "THAT — you are done, do not add anything else.\n"
                "Step 2 — if no single automation call closes it (this is common when the goal "
                "needs a WITNESS automation cannot invent, e.g. an auxiliary point from "
                "`segment_construction`/`symmetric_point_construction`, or a case split), look at "
                "Coq's tactic script and proof term below to find that witness/insight, then write "
                "a normal Lean tactic proof: `obtain`/`rcases` to destructure hypotheses (mirrors "
                "Coq's `destruct`/`ex_and`), `have h : P := ...` for intermediate facts (mirrors "
                "`assert`), and — critically — use `colr`, `cong_r`, `Tfinish`, or `TfinishA` to "
                "close any Col/Cong/≠/CongA sub-goal that follows mechanically from what's already "
                "in context, INSTEAD of manually chaining `col_permutation_i_c`/`cong_*_c` lemmas "
                "by hand. Keep the proof idiomatic and as short as correctness allows — it does "
                "NOT need to mirror Coq's exact tactic sequence, only its key idea.")

# Ch02-10 stubs pre-bind every binder/hypothesis as an actual theorem parameter
# (`theorem NAME (A B : T) (h : P) : Concl`); Ch11+ stubs are an unbound Pi-type
# (`theorem NAME : forall A B, P -> Concl`) with nothing bound yet. These are the
# two mutually-exclusive instructions for those two shapes -- picking the wrong
# one either shadows already-bound names (BOUND_RULE on a Ch11+ tail) or leaves
# every hypothesis name undefined (UNBOUND_RULE's absence on a Ch11+ tail).
BOUND_RULE = ("The theorem's binders/hypotheses are ALREADY bound in the signature — do NOT "
              "start with `fun` re-binding them (that shadows them); prove the conclusion "
              "directly (start with `by`).")
UNBOUND_RULE = ("The theorem's binders/hypotheses are NOT bound yet — the goal is "
                "`forall A B .., P1 -> P2 -> Concl`. Start with `by intro <name for each "
                "binder/hypothesis, in order>` (e.g. `by intro A B C h1 h2`) as your FIRST "
                "tactic, THEN prove the conclusion.")

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


def seed_upper_sigs(chapter_lean_paths):
    """Merge `<name>_c <signature>` one-liners from upper-chapter .lean files
    (Ch11+, Ch10Line2Extra, ...) into the same cache _climb_sigs() populates, so
    _sig_of() gives Ch11+ callers a real signature instead of falling through to
    the content-free `(ported Tarski lemma, in scope)` placeholder. _climb_sigs()
    only ever reads Climb_All.lean, a frozen Ch02-10 snapshot -- this is the
    Ch11+ analogue: identical one-liner extraction, applied to caller-supplied
    files, merged into the SAME dict rather than a parallel one (so callers keep
    using plain _sig_of()/_sigs_for() unchanged). Safe to call repeatedly / with
    files that don't exist yet (skipped)."""
    global _CLIMB_SIGS
    if _CLIMB_SIGS is None:
        _CLIMB_SIGS = dict(_climb_sigs())          # keep Ch02-10 coverage too
    for path in chapter_lean_paths:
        if not os.path.exists(path):
            continue
        src = open(path).read()
        for blk in re.split(r"(?=^theorem \w+_c\b)", src, flags=re.M):
            m = re.match(r"theorem (\w+)_c\b", blk)
            if m and ":=" in blk:
                sig = " ".join(blk.split(":=", 1)[0].split())
                _CLIMB_SIGS[m.group(1)] = sig.replace("theorem ", "", 1)


def _sig_of(u):
    """Best-effort one-line signature for a Coq lemma / axiom name (as `_c` if ported)."""
    cs = _climb_sigs()
    if u in cs:
        # `_climb_sigs()` reads the FROZEN Climb_All.lean snapshot, which predates
        # tonight's double-underscore-to-single rename in the real (non-frozen)
        # chain files -- its own declared names can be stale (confirmed live
        # 2026-07-15: `bet_neq12__neq_c` here vs the real `bet_neq12_neq_c` in
        # Ch03.lean). Collapse identifier-internal `__` before showing it, same
        # fix as the KNOWN-fallback branch below.
        return "  " + re.sub(r"(\w)__(\w)", r"\1_\2", cs[u])
    ms = get_lean_signature(u)["matches"]
    cone = [m for m in ms if any(cf in m["file"] for cf in T.CONE_FILES)]
    if cone:
        return "  " + re.sub(r"(\w)__(\w)", r"\1_\2", cone[0]["signature"])
    if u in AXIOM_SIGS:
        return "  " + AXIOM_SIGS[u]
    if u in T.NAME_MAP and T.NAME_MAP[u] in AXIOM_SIGS:
        return "  " + AXIOM_SIGS[T.NAME_MAP[u]]
    if u in KNOWN:
        # Coq's `P__Q` double-underscore convention collapses to single `_` on the
        # Lean side (established across this whole codebase tonight) -- showing the
        # RAW Coq name here as if it were the real Lean identifier fed the LLM a
        # name that doesn't exist (confirmed live 2026-07-15: `acute_obtuse__lta_c`/
        # `bet__obtuse_c` shown as "in scope", used verbatim, both unknown
        # identifiers -- this fallback branch was the actual source, not the LLM
        # guessing on its own).
        return f"  {u.replace('__', '_')}_c  (ported Tarski lemma, in scope)"
    if u in T.ALLOW_AXIOMS or u in T.NAME_MAP:
        return f"  {T.NAME_MAP.get(u, u)}  (Tarski axiom / class field, in scope)"
    return None


def _sigs_for(pt, ltac=""):
    toks = set(ID.findall(pt)) | set(ID.findall(ltac))
    used = sorted(toks & (KNOWN | T.ALLOW_AXIOMS | set(T.NAME_MAP)))
    return "\n".join(s for s in (_sig_of(u) for u in used) if s)


def _resolved_examples(coq_file, name, max_examples=15, max_arg_len=24):
    """Concrete worked examples of how COQ'S OWN PROOF (the one being translated)
    actually called each lemma it references -- one line per DISTINCT lemma
    name, first occurrence only.

    Why this is a different, complementary signal from _sig_of()/_sigs_for():
    those give the abstract LEAN-side TYPE signature ("in general this lemma
    needs a Perp X1 X2 A B"); pilot diagnosis this session found that alone
    insufficient -- the dominant real-build-error pattern on multi-argument
    lemmas (col_cop2_perp2__col_c: 6 points + 4 hyps) was argument-order/
    -position confusion even with the correct signature shown. This gives the
    exact positional binding Coq's proof used at least once, closer to "copy
    this shape" than "derive the right call from a type alone".

    Best-effort, never raises (matches every other prompt-context helper
    here); capped in both count and per-arg length to bound prompt bloat --
    a proof with many distinct sub-calls, or one passing a large nested
    sub-expression as an argument, won't blow up the prompt."""
    try:
        r = extract_resolved_calls(coq_file, name, default_q_paths())
    except Exception:
        return ""
    seen, lines = set(), []
    for c in r.resolved_calls:
        if c.name in seen or c.name not in KNOWN:
            continue
        seen.add(c.name)
        args = [a if len(a) <= max_arg_len else a[:max_arg_len] + "…" for a in c.args]
        # Show the actual Lean identifier (double-underscore collapsed + `_c`
        # suffix), not Coq's raw name -- this used to print e.g.
        # `acute_obtuse__lta(A, B, ...)` verbatim, which the LLM reasonably read
        # as a literally-callable name and copied straight into its proof,
        # producing "unknown identifier" (confirmed live 2026-07-15). The point
        # of this list is Coq's ARGUMENT ORDER/POSITIONING, not its identifier
        # spelling -- only the name needed fixing, the positions are unchanged.
        lean_name = c.name.replace("__", "_") + "_c"
        lines.append(f"  {lean_name}({', '.join(args)})")
        if len(lines) >= max_examples:
            break
    return "\n".join(lines)


# --------------------------------------------------------------------------
# Waypoint extraction — a "proof roadmap" reader, not a second Lean emitter.
#
# _sigs_for above is a flat, alphabetically-sorted regex token scan over the
# raw proof-term/tactic-script TEXT: good recall (a lemma that's really used
# will show up as a token) but zero structure -- no invocation order, no
# case-split shape, no witness-introduction info. translit.py's parser
# already builds a full order-preserving AST for exactly this term (used by
# emit()/emit_tactic() to produce Lean text); this walks that SAME AST to
# produce a compact, ordered summary instead of Lean syntax -- reusing T's
# parser and classification constants (COL_FAMILY, CONG_FAMILY, ELIMS,
# KNOWN_LEMMAS, PRIM, NAME_MAP, ALLOW_AXIOMS), never calling or modifying
# T.emit/T.emit_tactic/T.emit_match or any other translit.py function body.
#
# COL_FAMILY/CONG_FAMILY-headed subtrees are collapsed, not descended into --
# matching how emit() already treats them. Coq's Show Proof term for a
# ColR-closed subgoal is a large tree of collect_diffs/ss_ok_empty/permutation
# calls with zero correspondence to distinct Lean actions; walking into it
# would produce noisy, misleading waypoints exactly for the lemmas this is
# meant to help most (see docs/TARSKI_STATUS.md's ColR-leak discussion).
# --------------------------------------------------------------------------

def _render_atom(node, maxlen=40):
    """Shallow, best-effort display string for a witness/scrutinee -- NOT lemma
    resolution (no choose_variant/get_lean_signature calls), display only."""
    node = T._unparen(node)
    if node[0] == "var":
        return node[1]
    if node[0] == "app":
        h = _render_atom(node[1], maxlen)
        a = " ".join(_render_atom(x, maxlen) for x in node[2][:3])
        s = f"{h} {a}" if a else h
        return s if len(s) <= maxlen else s[:maxlen] + "…"
    return "…"


# Dotted names (e.g. `tarski_to_col_theory.Tarski_is_a_Col_theory`) are never a
# local hypothesis in this corpus -- Coq's auto-generated intro names are always
# bare identifiers. A dotted head, or these specific reflective-tactic-internal
# names, mean a reflective tactic was invoked inline (not via a named lemma) and
# its raw decision-procedure machinery is what's in the term -- see the ColR-leak
# investigation this session (BinNums.xO/interp/tarski_to_col_theory.*).
_REFLECTIVE_INTERNAL = {"interp", "BinNums"}


def _waypoint_lines(node, depth=0):
    pad = "  " * depth
    node = T._unparen(node)
    k = node[0]
    if k == "let":
        _, _name, val, body, _ty = node
        return _waypoint_lines(val, depth) + _waypoint_lines(body, depth)
    if k == "fun":
        return _waypoint_lines(node[2], depth)
    if k == "match":
        _scrut, branches = node[1], node[2]
        lines = [f"{pad}- case split ({len(branches)}-way)"]
        for _ctor, _vars, body in branches:
            lines += _waypoint_lines(body, depth + 1)
        return lines
    if k != "app":
        return []
    head, args = node[1], node[2]
    if head[0] != "var":
        return _waypoint_lines(head, depth) + [l for a in args for l in _waypoint_lines(a, depth)]
    f = head[1]
    if f in ("eq_ind", "eq_ind_r"):
        lines = [f"{pad}- rewrite using an equality"]
        return lines + [l for a in args for l in _waypoint_lines(a, depth)]
    if f in T.ELIMS:                                # ex_ind / and_ind / or_ind
        branches = args[:-1] if len(args) >= 2 else args
        # ex_ind/and_ind destructure ONE thing (an exists/and) into its parts --
        # matching emit_tactic's own `obtain` (single branch, one binder group
        # or more). or_ind is a genuine N-way disjunction case split -> `rcases`.
        label = (f"case split ({len(branches)}-way)" if f == "or_ind"
                else "destructure (obtain)")
        lines = [f"{pad}- {label}"]
        for br in branches:
            br = T._unparen(br)
            body = br[2] if br[0] == "fun" else br
            lines += _waypoint_lines(body, depth + 1)
        return lines
    if f == "ex_intro" and len(args) >= 3:
        lines = [f"{pad}- introduce witness: {_render_atom(args[1])}"]
        return lines + _waypoint_lines(args[2], depth)
    if f in T.COL_FAMILY:
        return [f"{pad}- collinearity closure step (Col)"]
    if f in T.CONG_FAMILY:
        return [f"{pad}- congruence closure step (Cong)"]
    if "." in f or f in _REFLECTIVE_INTERNAL:
        return [f"{pad}- reflective-tactic closure step (goal auto-decided, not by a named lemma)"]
    if f in KNOWN or f in T.PRIM or f in T.NAME_MAP or f in T.ALLOW_AXIOMS:
        lines = [f"{pad}- apply lemma: {f}"]
        return lines + [l for a in args for l in _waypoint_lines(a, depth)]
    # local hypothesis applied as a function, or genuinely unrecognized -- not
    # worth reporting as a "call", but still descend for nested witnesses/splits
    return [l for a in args for l in _waypoint_lines(a, depth)]


def extract_waypoints(coq_file, name):
    """Ordered 'proof roadmap' for a Coq lemma -- lemma invocations, witness
    introductions, case-split shape, reflective-closure points -- as compact
    text for the prompt. Best-effort like scaffold_prompt's bmap: never raises,
    returns "" on any failure (missing lemma, parse edge case, etc.) rather
    than blocking the rest of the prompt."""
    try:
        pt = run_proof(coq_file, name, default_q_paths())
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        body = ast[2] if ast[0] == "fun" else ast
        lines = _waypoint_lines(body, 0)
        return "\n".join(lines)
    except Exception:
        return ""


def scaffold_prompt(coq_file, name, tail, binders, *, mode="mirror",
                    prev_error=None, extra_sigs=None, nb=0, waypoint_mode="additive"):
    """waypoint_mode: "additive" (default) shows the extract_waypoints() roadmap
    alongside the existing term/tactic-script context; "replace" substitutes it
    for term_block in freeform mode (freeform already omits the raw term to
    avoid prompt bloat -- whether the compact roadmap reintroduces that problem
    isn't decidable without pilot data, hence a flag, not a hardcoded choice);
    "off" disables it (for A/B comparison against today's baseline)."""
    pt = run_proof(coq_file, name, default_q_paths())
    try:
        ltac = extract_lemma_source(coq_file, name)
    except Exception:
        ltac = "(tactic script unavailable)"
    wp_text = ""
    try:                          # binder map + waypoints -- best-effort, never fatal
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        bmap = str(dict(zip(ast[1] if ast[0] == "fun" else [], binders)))
        if waypoint_mode != "off":
            body = ast[2] if ast[0] == "fun" else ast
            wp_text = "\n".join(_waypoint_lines(body, 0))
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
    elif mode == "julien":
        # automation-first, witness-informed idiomatic proof (see JULIEN_INSTR) -- doesn't
        # need the raw term (freeform-style), the tactic script (always shown via {ltac}
        # below) plus the automation macros are the point here.
        mode_instr = JULIEN_INSTR
        term_block = ""
    else:
        mode_instr = FREEFORM_INSTR
        term_block = ""                        # free-form: skip the giant term blob
    waypoints = (f"\nProof roadmap (order of steps Coq's proof actually took — a guide, "
                f"not a template to copy literally):\n{wp_text}\n"
                if wp_text and waypoint_mode != "off" else "")
    if waypoint_mode == "replace" and mode != "mirror":
        term_block = ""                        # roadmap stands in for the raw term/script
    extra = f"\n- Also available: {extra_sigs}" if extra_sigs else ""
    err = (f"\n\nYour previous attempt FAILED with this Lean error:\n{prev_error}\nFix it."
           if prev_error else "")
    bound_rule = UNBOUND_RULE if nb else BOUND_RULE
    return PROMPT.format(name=name, tail=tail, mode_instr=mode_instr, ltac=ltac,
                        bound_rule=bound_rule, waypoints=waypoints,
                        term_block=term_block, defs=_defs_for(tail, ltac),
                        sigs=_sigs_for(pt, ltac),
                        examples=_resolved_examples(coq_file, name),
                        bmap=bmap, extra=extra, err=err)


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


def verify_one(name, tail, proof, climb_mod=None, nb=0, tier_var=None):
    """Compile the candidate as `<name>_llm` importing the prebuilt Climb_All olean
    (full cross-chapter context). Returns (ok, first_error, unknown_id).
    Per-lemma try-file (LLMTry_<name>.lean) so verifies can run in parallel.

    climb_mod: upstream module to import (defaults to CLIMB_MOD, the Ch02..Ch10
    chain). Pass a later chapter's module for upper-chapter (Ch11+) callers so
    same-chapter/earlier-upper-chapter dependencies are actually in scope.

    tier_var: the `variable {Tpoint ..} [...]` line for the CALLER's tier
    (climb_upper.py's TIER_VARS[tier] -- "neutral"/"euclidean"/"2D"). Defaults
    to the bare neutral-only line, which was PREVIOUSLY the only option ever
    used here regardless of caller -- confirmed via live diagnostic 2026-07-14
    that this silently fails EVERY euclidean/2D-tier proof (9 of 15 upper
    chapters: Ch12b/Ch13e/Ch13f need Tarski_euclidean; Ch14a-c/Ch15a-b/Ch16a
    need Tarski_2D+Tarski_euclidean) with `failed to synthesize instance of
    type class Tarski_2D/Tarski_euclidean`, no matter how correct the LLM's
    Lean proof is -- a structural verifier gap, not a proof-quality problem.

    nb: binder count for an UNBOUND-Pi-type tail. Ch11+ stubs are
    `theorem NAME : forall .., P1 -> P2 -> Concl` -- nothing pre-bound, unlike
    Ch02-10's `theorem NAME (A B : T) (h : P) : Concl`. When nb > 0, the proof
    is tactic-mode, AND the proof does NOT already open with its own `intro`
    (UNBOUND_RULE asks the model to write one, using meaningful names like
    `intro A B C h` rather than `b0 b1 b2 b3` -- confirmed working on every
    accepted term-mode proof in the pilot), `intro b0 .. b{nb-1}` is
    synthesized as a fallback, mirroring write_chapter()'s
    `if nb: out.append(f"  intro {bnames}")` in climb_upper.py.

    IMPORTANT: synthesizing on top of a model-written `intro` (rather than
    only as a fallback) double-introduces and Lean's `introN` fails with
    "There are no additional binders ... to introduce" -- confirmed as the
    root cause of every single tactic-mode pilot failure (5/5 in one
    diagnostic round), while every term-mode success was unaffected (its own
    `fun` already binds everything, this whole branch never runs for it)."""
    climb_mod = climb_mod or CLIMB_MOD
    try_mod = f"GeocoqTranslate/Tarski_dev/LLMTry_{name}"
    path = os.path.join(LEAN_ROOT, try_mod + ".lean")
    kw = ":= by" if proof.lstrip().startswith("by") else ":="
    pbody = proof.lstrip()[2:] if proof.lstrip().startswith("by") else "  " + proof
    if nb and kw == ":= by" and not re.match(r"\s*intro\b", pbody):
        bnames = " ".join(f"b{i}" for i in range(nb))
        pbody = f"\n  intro {bnames}" + pbody
    # `tier_var` is only ever passed by climb_upper.py's Ch11+ callers -- reuse it as the
    # signal to also pull in the Tfinish/TfinishA automation macros (JULIEN_INSTR proofs
    # reference them), since only 3 of 15 upper chapters happen to already import these
    # themselves. TarskiConA imports Ch11, so it's always safe here: every climb_mod this
    # branch can see is Ch11 itself or a later chapter that already transitively has it.
    julien_imports = (["import GeocoqTranslate.Tarski_dev.TarskiFinish",
                        "import GeocoqTranslate.Tarski_dev.TarskiConA"] if tier_var else [])
    src = [
        f"import {climb_mod}", *julien_imports,
        "namespace GeocoqTranslate.Tarski.Base",
        "open Tarski_neutral_dimensionless",
        "open Tarski_neutral_dimensionless_with_decidable_point_equality",
        tier_var or "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]",
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


def llm_translate(coq_file, name, tail, binders, retries=3, extra0=None,
                  climb_mod=None, nb=0, source=None, waypoint_mode="additive",
                  tier_var=None, try_julien_first=False):
    """Attempt order: [julien?], mirror, freeform x retries.
    Returns (proof, attempts, mode) or (None, attempts, None). Appends a per-lemma
    record (attempts, tokens, wallclock, mode, outcome) to the measurement ledger.
    extra0: extra signature/hint text injected into every prompt (e.g. the col-helper
    lemmas that Coq's reflective ColR tactic abbreviates).
    climb_mod/nb/tier_var: forwarded to verify_one -- see its docstring (Ch11+
    callers need all three: a non-Ch10 upstream import, a synthesized `intro`
    for the unbound tail, and the chapter's real typeclass instances).
    source: opt-in tag stamped on ledger records (e.g. "upper") so pilot/experiment
    runs don't commingle un-distinguishably with unrelated ledger writers' entries.
    waypoint_mode: forwarded to scaffold_prompt -- see its docstring.
    try_julien_first: opt-in, default False (preserves the exact mirror->freeform
    behavior every existing caller, incl. cascade_llm.py's Ch02-10 pipeline, already
    relies on). When True, tries JULIEN_INSTR mode FIRST -- automation-first
    (Tfinish/TfinishA/aesop alone after intro), then a witness-informed idiomatic
    proof if that fails -- validated on real lemmas in JulienTest_*.lean. Pass True
    only from climb_upper.py's Ch11+ callers."""
    prev, extra = None, extra0
    in_tok = out_tok = ms = 0
    ptoks = len(T.tok(run_proof(coq_file, name, default_q_paths())))   # proof-term size
    modes = (["julien"] if try_julien_first else []) + ["mirror"] + ["freeform"] * retries
    for attempt, mode in enumerate(modes):
        body, why, meta = call_claude(scaffold_prompt(
            coq_file, name, tail, binders, mode=mode, prev_error=prev, extra_sigs=extra,
            nb=nb, waypoint_mode=waypoint_mode))
        in_tok += meta["in_tok"]; out_tok += meta["out_tok"]; ms += meta["ms"]
        if body is None:                       # sanitizer rejected the output
            prev = why
            continue
        ok, err, unk = verify_one(name, tail, body, climb_mod=climb_mod, nb=nb, tier_var=tier_var)
        if ok:
            _log_ledger(dict(name=name, outcome="clean", mode=mode, attempts=attempt + 1,
                             ptoks=ptoks, in_tok=in_tok, out_tok=out_tok, ms=ms,
                             source=source))
            return body, attempt + 1, mode
        prev = err
        if unk:                                # targeted premise injection for next try
            s = _sig_of(unk.split(".")[-1].removesuffix("_c"))
            extra = s.strip() if s else None
    _log_ledger(dict(name=name, outcome="fail", mode=None, attempts=len(modes),
                     ptoks=ptoks, in_tok=in_tok, out_tok=out_tok, ms=ms, source=source))
    return None, len(modes), None


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
