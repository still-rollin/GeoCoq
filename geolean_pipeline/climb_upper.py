"""
climb_upper — deterministic-then-LLM proof filling for the UPPER chapters
(Ch11..Ch16b, the 973 statement-stubs generated this session), architected
as a sibling to `climb.py` (which does the same job for Ch02..Ch10).

Per chapter, in dependency order:
  1. DETERMINISTIC pass: oracle (Show Proof) + translit.py transliterates
     every `:= sorry` hole into a real Lean proof attempt. No LLM, no cost.
  2. REPAIR LOOP: fold attempts into the chapter file (in small batches --
     `BATCH_SIZE`), `lake build`, and on error re-verify each flagged name in
     its OWN isolated scratch file (`isolate_verify`/`triage_bad`) before
     demoting it back to a tracked `:= sorry` -- Lean's error recovery can
     emit spurious diagnostics on unrelated declarations after a genuinely
     broken one, and demoting on that naive line-bisection alone silently
     wipes correct proofs (see `fold_and_verify`'s docstring). Repeat until
     the file is error-free (bounded, with an explicit non-convergence
     report instead of silently giving up).
  3. KERNEL GATE: `lake env lean` + `#print axioms` classifies every
     attempted lemma as clean (no sorryAx) or tainted (compiles, but
     depends on a hole) — never trust "compiles" alone.
  4. LLM pass (opt-in, `use_llm=True`): whatever is STILL a hole after step 3
     goes through the same kernel-gated LLM cascade `cascade_llm.py` already
     uses for Ch02..Ch10 (llm_path.llm_translate -> verify -> fold).
  5. Grow the cross-chapter pool (`translit.LOCAL_SIGS`) with this chapter's
     newly-clean names so later chapters can reference them, then move on.

Every round is logged to `.climb_upper_ledger.jsonl` (one line per chapter
per phase) so a run can be resumed/audited without re-deriving state from
build logs.

Usage:
  python geolean_pipeline/climb_upper.py                 # deterministic only, all chapters
  python geolean_pipeline/climb_upper.py Ch11             # deterministic only, one chapter
  python geolean_pipeline/climb_upper.py Ch11 llm         # + LLM on the deterministic residue
  python geolean_pipeline/climb_upper.py --resume         # skip chapters already in the ledger
  python geolean_pipeline/climb_upper.py Ch11 --no-isolate  # A/B: old unsafe demote-on-faith path
"""
from __future__ import annotations
import os, sys, re, json, subprocess, time, glob

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
sys.path.insert(0, os.path.join(REPO, "transpiler"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

from src.oracle import run_proof, default_q_paths
import geolean_transpile as GT
import translit as T

LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"
COQ_ROOT = "theories/Main/Tarski_dev"
BASE_CHAPTERS = ["Ch02", "Ch03", "Ch04", "Ch05", "Ch06", "Ch07", "Ch08", "Ch09", "Ch10"]
LEDGER = ".climb_upper_ledger.jsonl"

# (coq stem, lean stem, tier) — chained exactly as gen_stubs.py emitted them.
CHAPTERS = [
    ("Ch11_angles",                     "Ch11",  "neutral"),
    ("Ch12_parallel",                   "Ch12",  "neutral"),
    ("Ch12_parallel_inter_dec",         "Ch12b", "euclidean"),
    ("Ch13_1",                          "Ch13a", "neutral"),
    ("Ch13_2_length",                   "Ch13b", "neutral"),
    ("Ch13_3_angles",                   "Ch13c", "neutral"),
    ("Ch13_4_cos",                      "Ch13d", "neutral"),
    ("Ch13_5_Pappus_Pascal",            "Ch13e", "euclidean"),
    ("Ch13_6_Desargues_Hessenberg",     "Ch13f", "euclidean"),
    ("Ch14_sum",                        "Ch14a", "2D"),
    ("Ch14_prod",                       "Ch14b", "2D"),
    ("Ch14_order",                      "Ch14c", "2D"),
    ("Ch15_lengths",                    "Ch15a", "2D"),
    ("Ch15_pyth_rel",                   "Ch15b", "2D"),
    ("Ch16_coordinates",                "Ch16a", "2D"),
    ("Ch16_coordinates_with_functions", "Ch16b", "2D"),
]
TIER_VARS = {
    "neutral":   "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]",
    "euclidean": "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_euclidean Tpoint]",
    "2D":        "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]",
}
MAX_REPAIR_ROUNDS = 20


def _log(rec: dict):
    rec["ts"] = time.time()
    with open(LEDGER, "a") as f:
        f.write(json.dumps(rec) + "\n")


def seed_base_pool():
    """LOCAL_SIGS <- every `_c` signature in the existing 511-lemma base
    (Ch02..Ch10) plus CoplanarPermExtra, so cross-chapter deps into the
    foundations resolve."""
    for ch in BASE_CHAPTERS + ["CoplanarPermExtra", "Ch10Line2Extra"]:
        text = open(f"{LEAN}/{ch}.lean").read()
        for m in re.finditer(r"^theorem (\w+)_c\b([^\n]*(?:\n(?!theorem)[^\n]*)*)", text, re.M):
            name, mid = m.group(1), m.group(2)
            sig_text = "theorem " + name + "_c " + mid.split(":=")[0]
            T.LOCAL_SIGS[name] = T.lean_binder_kinds(sig_text)


def ambient_prelude(coq_path: str) -> str:
    """Section-level `Definition`/`Variable` declarations (e.g. Ch14+'s
    `Variable O E E' : Tpoint.` / `Variable grid_ok : ~ Col O E E'.`) that
    every later theorem in the file implicitly depends on. gen_stubs.py's
    ORIGINAL stub generation included these; write_chapter regenerating the
    file from scratch did not reproduce them, which is exactly what left
    O/E/E' as unresolved auto-bound implicits and broke Ch14a's build."""
    text = open(coq_path).read()
    lines = []
    for m in re.finditer(r"^Definition\s+(\w[\w']*)\s*:=\s*(PA|PB|PC)\s*\.\s*$", text, re.M):
        lines.append(f"def {m.group(1)} : Tpoint := {m.group(2)}")
    for m in re.finditer(r"^Variable\s+([\w\s']+?)\s*:\s*Tpoint\s*\.\s*$", text, re.M):
        lines.append(f"variable ({m.group(1).strip()} : Tpoint)")
    for m in re.finditer(r"^Variable\s+(\w[\w']*)\s*:\s*([^\n]+?)\s*\.\s*$", text, re.M):
        ty = m.group(2)
        if ty.strip() == "Tpoint":
            continue
        lines.append(f"variable ({m.group(1)} : {GT.translate_type(ty)})")
    return "\n".join(lines)


def parse_stub_blocks(lean_path: str) -> dict[str, str]:
    """name -> statement text, for every `theorem name_c : <stmt> := sorry`.
    Bounded so a non-sorry (already-solved) theorem sitting between two stubs
    can't get swallowed into the next stub's non-greedy match -- without the
    lookahead, `(.*?)` would happily cross into and past a solved theorem's
    real body to reach a LATER `:= sorry`, corrupting that solved theorem's
    entry and silently dropping every stub in between."""
    text = open(lean_path).read()
    out = {}
    for m in re.finditer(r"(?ms)^theorem (\w+)_c\s*:\s*\n?((?:(?!^theorem \w+_c\s*:).)*?):= sorry\n", text):
        out[m.group(1)] = m.group(2).strip()
    return out


def det_attempt(coq_path: str, name: str):
    """One deterministic transliteration attempt. Returns (body, n_binders)
    or None (translit flagged an UNRESOLVED/LEAK/parse failure)."""
    try:
        pt = run_proof(coq_path, name, default_q_paths())
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        notes = []
        if ast[0] == "fun":
            coq_binders = ast[1]
            use = [f"b{i}" for i in range(len(coq_binders))]
            body = T.emit_body(ast[2], dict(zip(coq_binders, use)), notes)
            nb = len(coq_binders)
        else:
            body = T.emit_body(ast, {}, notes)
            nb = 0
        if any("UNRESOLVED" in n or "NON-LEMMA" in n or "LEAK" in n for n in notes):
            return None
        return (body, nb)
    except Exception:
        return None


def parse_all_blocks(lean_path: str) -> dict[str, str]:
    """name -> this theorem's exact CURRENT source block (statement +
    whatever body it has right now -- sorry or real), for every declared
    `theorem name_c :` in the file. Used so write_chapter can carry already-
    solved entries forward VERBATIM: it regenerates the whole file from
    scratch every call, so anything not explicitly re-supplied is lost --
    this is what silently dropped 31 already-solved theorems on 2026-07-10.

    Must also split on `^#print axioms` (matching demote()'s boundary set),
    not just `^theorem ... :` -- otherwise the LAST theorem in the file has
    no following boundary until EOF, so its captured block silently swallows
    the entire trailing print-axioms epilogue and the file's real `end`
    statement. If that block later gets cached into `preserved` (name was
    transiently clean/tainted at the time) and outlives a subsequent
    demote() of that same name (demote rewrites the file on disk but never
    invalidates this already-cached dict entry), the next write_chapter call
    re-emits the embedded epilogue+end in the middle of the file, on top of
    write_chapter's own fresh one -- a dangling second `end` with no matching
    scope, breaking the whole module's build. Confirmed root cause of the
    double-epilogue corruption in Ch11.lean, 2026-07-14."""
    if not os.path.exists(lean_path):
        return {}
    text = open(lean_path).read()
    blocks = re.split(r"(?=^theorem \w+_c :)|(?=^#print axioms)", text, flags=re.M)
    out = {}
    for b in blocks:
        m = re.match(r"theorem (\w+)_c :", b)
        if m:
            out[m.group(1)] = b.rstrip("\n")
    return out


def write_chapter(out_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved, ambient="",
                   extra_imports=()):
    """coq_names: full chapter name list in original file order (drives
    output order -- must match so within-chapter forward/backward refs still
    resolve top-to-bottom like Lean requires). preserved: {name: raw block
    text} carried forward verbatim for names NOT being (re)attempted this
    call -- never silently dropped, unlike a plain `names`-only regenerate.
    ambient: Section-level `variable`/`def` lines (see ambient_prelude) that
    must be re-emitted every time -- dropping them silently breaks every
    later theorem that mentions an ambient point like Ch14+'s O/E/E'.
    extra_imports: bare module names (no `import ` prefix) the file needs
    beyond the single `prev_lean` one this function always writes -- e.g.
    `GeocoqTranslate.Tarski_dev.TarskiFinish`, needed for `Tfinish`/`colr`/
    `cong_r`. climb_chapter discovers these once from the file's CURRENT
    content and threads them through here so a regenerate never silently
    drops them (this is exactly what broke every Tfinish-using theorem in
    Ch11 the first time this ran without the fix -- see 2026-07-14 incident)."""
    out = [f"import GeocoqTranslate.Tarski_dev.{prev_lean}"]
    out += [f"import {imp}" for imp in extra_imports]
    out += ["",
           "namespace GeocoqTranslate.Tarski.Base",
           "open Tarski_neutral_dimensionless",
           "open Tarski_neutral_dimensionless_with_decidable_point_equality", "",
           TIER_VARS[tier], ""]
    if ambient:
        out.append(ambient); out.append("")
    all_names = [n for n in coq_names if n in preserved or n in stub_blocks]
    for n in all_names:
        if n in preserved:
            out.append(preserved[n])
            continue
        stmt = stub_blocks[n]
        entry = bodies.get(n)
        if entry is None:
            out.append(f"theorem {n}_c :\n    {stmt} := sorry\n")
            continue
        b, nb = entry
        bnames = " ".join(f"b{i}" for i in range(nb))
        if b.startswith("by\n"):
            out.append(f"theorem {n}_c :\n    {stmt} := by")
            rest = b[3:]
            # Mirror verify_one's guard: an LLM tactic-mode proof asked to write its OWN
            # `intro` (UNBOUND_RULE, meaningful names) already binds everything -- prepending
            # another synthesized `intro b0 b1 ..` unconditionally here (as this used to do)
            # double-introduces and Lean's introN rejects it with "no additional binders to
            # introduce", silently demoting an already verify_one-CONFIRMED-clean proof back
            # to sorry on the real-file fold. det_attempt's own bodies never hit this (they're
            # generated using the b0/b1/.. names this line supplies, never their own intro),
            # which is why this asymmetry was invisible before the LLM tier existed.
            if nb and not re.match(r"\s*intro\b", rest):
                out.append(f"  intro {bnames}")
            out.append(rest)
            out.append("")
        else:
            out.append(f"theorem {n}_c :\n    {stmt} :=")
            # Same double-binder bug as the tactic-mode branch above, mirror image: an LLM
            # term-mode proof asked to self-bind (UNBOUND_RULE) already opens with its own
            # `fun A1 A2 .. =>`; unconditionally wrapping another `fun b0 b1 .. =>` around it
            # (as this used to do) changes the term's type from `T1 -> .. -> Concl` to
            # `T1 -> .. -> (T1 -> .. -> Concl)` -- a real arity/type mismatch, not a cosmetic
            # issue -- silently demoting an already verify_one-CONFIRMED-clean proof back to
            # sorry on the real-file fold (confirmed live: inter__npar clean in the ledger
            # twice, still `sorry` in Ch12b.lean both times, 2026-07-14). det_attempt's bodies
            # never hit this for the same reason as the tactic-mode case: they're built with
            # the b0/b1/.. names this line supplies, never their own leading `fun`.
            if nb and not re.match(r"\s*fun\b", b):
                out.append(f"  fun {bnames} =>\n  {b}\n")
            else:
                out.append(f"  {b}\n")
    for n in all_names:
        out.append(f"#print axioms GeocoqTranslate.Tarski.Base.{n}_c")
    out.append("end GeocoqTranslate.Tarski.Base")
    open(out_path, "w").write("\n".join(out))


def _resolve_coq_name(lean_name: str, coq_names: list[str]) -> str:
    """Coq source names can use GeoCoq's `P__Q` double-underscore convention
    (e.g. `inter__npar`); the Lean stub generator collapses that to a single
    `_` (`inter_npar_c`). run_proof/oracle calls need the RAW Coq name or they
    raise "lemma not found" -- silently and PERMANENTLY blocking both det_attempt
    and the LLM tier for every such lemma, no matter how many sweep rounds run
    (confirmed live 2026-07-15: `inter_npar_c` never closed across 3+ full Ch12b
    passes for exactly this reason -- every attempt's exception was swallowed by
    `_one`'s broad `except Exception: body = None`). Falls back to lean_name
    itself when no double-underscore variant exists (the common case)."""
    if lean_name in coq_names:
        return lean_name
    for cn in coq_names:
        if cn.replace("__", "_") == lean_name:
            return cn
    return lean_name


def _module_of(out_path: str) -> str:
    rel = out_path.split(f"{LEAN}/")[-1][:-len(".lean")]
    return f"GeocoqTranslate.Tarski_dev.{rel}"


class UpstreamBuildError(Exception):
    """Raised when `lake build` fails because of errors in a file OTHER than
    the one we're repairing (a broken earlier chapter in the import chain).
    Demoting lemmas in the CURRENT file can never fix this -- silently
    treating "no errors in MY file" as "converged" here is exactly what let
    Ch14a's break silently misclassify all of Ch14b..Ch16b as empty holes."""
    def __init__(self, foreign_errors: list[str]):
        self.foreign_errors = foreign_errors
        super().__init__(f"{len(foreign_errors)} error(s) in upstream file(s): "
                          + "; ".join(foreign_errors[:5]))


def build_errors(out_path: str, names: list[str]) -> set[str]:
    module = _module_of(out_path)
    r = subprocess.run(["lake", "build", module], cwd="lean/geocoq_translate",
                        capture_output=True, text=True, timeout=900)
    log = r.stdout + r.stderr
    lean = open(out_path).read()
    starts = sorted([(lean.count("\n", 0, m.start()) + 1, m.group(1))
                      for m in re.finditer(r"^theorem (\w+)_c :", lean, re.M)])

    def owner(errline):
        o = None
        for ln, name in starts:
            if ln <= errline:
                o = name
            else:
                break
        return o

    rel = out_path.split(f"{LEAN}/")[-1]
    all_err_lines = re.findall(r"^error: (GeocoqTranslate/Tarski_dev/[^:\s]+):(\d+):", log, re.M)
    own_prefix = f"GeocoqTranslate/Tarski_dev/{rel}"
    foreign = [f"{path}:{ln}" for path, ln in all_err_lines if path != own_prefix]
    if foreign and r.returncode != 0:
        raise UpstreamBuildError(sorted(set(foreign)))
    err_lines = [int(ln) for path, ln in all_err_lines if path == own_prefix]
    bad = {owner(l) for l in err_lines}
    bad.discard(None)
    return bad


def demote(out_path: str, names_to_kill: set[str]):
    lean = open(out_path).read()
    blocks = re.split(r"(?=^theorem \w+_c :)|(?=^#print axioms)", lean, flags=re.M)
    out = []
    for blk in blocks:
        m = re.match(r"theorem (\w+)_c :", blk)
        if m and m.group(1) in names_to_kill:
            m2 = re.match(r"theorem (\w+)_c :\s*\n?\s*(.*?):=", blk, re.S)
            stmt = m2.group(2).strip() if m2 else None
            out.append(f"theorem {m.group(1)}_c :\n    {stmt} := sorry\n" if stmt else blk)
        else:
            out.append(blk)
    open(out_path, "w").write("".join(out))


def kernel_check(out_path: str, names: list[str]) -> dict[str, str]:
    module = _module_of(out_path).replace("GeocoqTranslate.Tarski_dev.", "")
    rel = f"GeocoqTranslate/Tarski_dev/{module}.lean"
    r = subprocess.run(["lake", "env", "lean", rel], cwd="lean/geocoq_translate",
                        capture_output=True, text=True, timeout=900)
    log = r.stdout + r.stderr
    # `lake env lean` only compiles THIS file, so a missing upstream .olean (e.g. a
    # concurrent `lake build` elsewhere mid-rewriting an earlier chapter) surfaces as
    # an import-failure diagnostic ON THIS FILE, not a separate foreign-path error like
    # `build_errors` sees -- without this check every name silently misclassifies as
    # "hole" (zero axiom-lines at all), exactly like the cascading Ch14a..16b bug.
    missing = re.search(r"error:.*?(\S+\.olean)[^\n]*does not exist", log)
    if missing:
        raise UpstreamBuildError([f"missing build artifact (likely a concurrent build "
                                   f"elsewhere): {missing.group(1)}"])
    ax = {}
    for m in re.finditer(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)_c' "
                         r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log):
        if m.group(1) in names:
            ax[m.group(1)] = m.group(2) or ""
    return ax


def _isolate_path(lean_path: str, name: str | None = None) -> str:
    """name=None: the legacy single shared scratch path (still used by the
    two best-effort startup/shutdown cleanup calls). name=<candidate>: a
    PER-CANDIDATE path -- required for triage_bad's isolate_verify calls to
    run concurrently (ThreadPoolExecutor); the old single shared path meant
    two candidates isolated at once would race to write/build the SAME
    file, corrupting both checks."""
    base = lean_path[:-len(".lean")] + "__isolate"
    return f"{base}_{name}.lean" if name else f"{base}.lean"


def isolate_verify(lean_path, prev_lean, tier, coq_names, stub_blocks,
                    name, body, preserved, ambient="", extra_imports=()):
    """Build a scratch file containing `name`'s real attempted `body` as the
    ONLY non-inert, not-yet-verified content: every other declaration is
    either already-`preserved` (real code, kernel-checked earlier) or an
    inert `:= sorry` stub (write_chapter's existing entry-is-None fallback,
    which also keeps every OTHER name's real statement type in scope so
    same-chapter references -- forward or backward -- still resolve exactly
    as they do in the shared batch file). A bare `sorry` has no tactic
    content and cannot itself be the source of a parser-recovery cascade,
    and `preserved` blocks were already proven correct in an earlier
    isolated/batch check -- so `name` is the ONLY thing in this file that
    can be at fault. Any build error anywhere in it is unambiguously `name`'s,
    with no line-bisection/owner() guesswork needed and no way to blame an
    innocent neighbor, because there are no other live candidates present to
    misattribute onto.
    Returns ("broken" | "clean" | "tainted" | "hole", axioms_str_or_None).
    Propagates UpstreamBuildError untouched -- an isolated build can still be
    blocked by a genuinely broken upstream file, and that must never be
    misread as "this candidate is broken."
    """
    iso_path = _isolate_path(lean_path, name)
    write_chapter(iso_path, prev_lean, tier, coq_names, stub_blocks, {name: body}, preserved, ambient,
                  extra_imports)
    try:
        module = _module_of(iso_path)
        r = subprocess.run(["lake", "build", module], cwd="lean/geocoq_translate",
                            capture_output=True, text=True, timeout=900)
        log = r.stdout + r.stderr
        rel = iso_path.split(f"{LEAN}/")[-1]
        own_prefix = f"GeocoqTranslate/Tarski_dev/{rel}"
        all_err_lines = re.findall(r"^error: (GeocoqTranslate/Tarski_dev/[^:\s]+):(\d+):", log, re.M)
        foreign = [f"{path}:{ln}" for path, ln in all_err_lines if path != own_prefix]
        if foreign and r.returncode != 0:
            raise UpstreamBuildError(sorted(set(foreign)))
        if any(path == own_prefix for path, _ln in all_err_lines):
            return "broken", None
        ax = kernel_check(iso_path, [name])
        if name not in ax:
            return "hole", None
        return ("tainted", ax[name]) if "sorryAx" in ax[name] else ("clean", ax[name])
    finally:
        try:
            os.remove(iso_path)   # per-candidate scratch file -- unlike the old
        except OSError:            # single shared path, these don't get overwritten
            pass                    # by the next call, so must be cleaned up here


def triage_bad(lean_path, prev_lean, tier, coq_names, stub_blocks,
                bad, bodies, preserved, ambient="", extra_imports=()):
    """Isolate every name in `bad` independently against the same `preserved`
    baseline (order between them doesn't matter -- each check is self-
    contained). Returns (broken, innocent): `innocent` names were cascade
    victims of a genuinely broken batch-mate, not broken themselves, and
    their real body in `bodies` is still correct and must not be discarded.

    Parallelized: each isolate_verify call now writes/builds its OWN uniquely-
    named scratch file (`_isolate_path(lean_path, name)`), so concurrent calls
    for different names can no longer race on a shared file the way they
    would have under the old single fixed `__isolate.lean` path -- this was
    previously the single biggest observed wall-clock cost in a repair round
    (one full-file `lake build` per flagged candidate, strictly sequential)."""
    import concurrent.futures as cf
    broken, innocent = set(), set()
    to_check = [n for n in bad if bodies.get(n) is not None]
    # names with body=None: already `sorry` / no real attempt -- can't be
    # "broken" and nothing to rescue, skip without spending a build on them.
    MAX_ISOLATE_WORKERS = 6

    def _one(n):
        status, _ax = isolate_verify(lean_path, prev_lean, tier, coq_names, stub_blocks,
                                      n, bodies[n], preserved, ambient, extra_imports)
        return n, status

    with cf.ThreadPoolExecutor(max_workers=MAX_ISOLATE_WORKERS) as ex:
        for n, status in ex.map(_one, to_check):
            (broken if status == "broken" else innocent).add(n)
    return broken, innocent


def fold_and_verify(lean_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved,
                     ambient="", isolate=True, extra_imports=()):
    """Write `bodies` into the chapter file (plus `preserved` carried forward
    verbatim), repair-loop to an error-free build, then kernel-gate over
    EVERY declaration in the file (preserved + freshly attempted), not just
    this round's subset -- otherwise already-solved entries silently drop
    out of the reported clean/tainted counts too.
    Returns (clean, tainted, hole, rounds_or_None, rescued). `rounds is None`
    means the repair loop did NOT converge — the file is left in its last
    (still-erroring) state for manual follow-up rather than silently
    reporting a wrong zero. `rescued` counts names that build_errors' naive
    line-bisection flagged as suspects but isolate_verify (when `isolate`
    is True) confirmed were innocent cascade victims, not actually broken --
    directly measuring how many the OLD (pre-isolation) code would have
    wrongly wiped."""
    write_chapter(lean_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved, ambient,
                  extra_imports)
    all_names = [n for n in coq_names if n in preserved or n in stub_blocks]
    rescued = 0

    for rounds in range(1, MAX_REPAIR_ROUNDS + 1):
        bad_raw = build_errors(lean_path, all_names)
        # `preserved` names are ALREADY kernel-verified from an earlier step -- build_errors'
        # naive line-bisection can misattribute a cascading error (Lean's recovery emitting
        # spurious diagnostics on declarations AFTER the real culprit) to one of them just
        # because it happens to sit downstream in the file. Never let demote() touch those:
        # doing so silently regresses previously-clean proofs back to `sorry` (confirmed
        # empirically -- 14 already-solved Ch11 lemmas got wiped this way in one run).
        bad = bad_raw - set(preserved.keys())
        if not bad_raw:
            ax = kernel_check(lean_path, all_names)
            clean = [n for n in all_names if n in ax and "sorryAx" not in ax[n]]
            tainted = [n for n in all_names if n in ax and "sorryAx" in ax[n]]
            hole = [n for n in all_names if n not in clean and n not in tainted]
            return clean, tainted, hole, rounds, rescued
        if not bad:
            # Every flagged line lands on an already-`preserved` name and nothing new was
            # attempted this round that could explain it (a stray/unattributable diagnostic,
            # or two individually-fine preserved entries only conflicting together). There is
            # no live candidate left to demote, so looping again changes nothing -- report the
            # current state instead of burning rounds against a phantom.
            ax = kernel_check(lean_path, all_names)
            clean = [n for n in all_names if n in ax and "sorryAx" not in ax[n]]
            tainted = [n for n in all_names if n in ax and "sorryAx" in ax[n]]
            hole = [n for n in all_names if n not in clean and n not in tainted]
            print(f"WARNING: unattributed build error(s) landed only on preserved name(s) "
                  f"{sorted(bad_raw)} -- no live candidate to blame, stopping here", flush=True)
            return clean, tainted, hole, rounds, rescued
        if isolate:
            broken, innocent = triage_bad(lean_path, prev_lean, tier, coq_names,
                                           stub_blocks, bad, bodies, preserved, ambient, extra_imports)
        else:
            broken, innocent = bad, set()
        rescued += len(innocent)
        demote(lean_path, broken)
        for n in broken:
            bodies[n] = None
    return [], [], list(all_names), None, rescued


def climb_chapter(coq_stem: str, lean_stem: str, tier: str, prev_lean: str,
                   use_llm: bool = False, isolate: bool = True) -> dict:
    coq_path = f"{COQ_ROOT}/{coq_stem}.v"
    lean_path = f"{LEAN}/{lean_stem}.lean"
    for stale in glob.glob(_isolate_path(lean_path, "*")) + [_isolate_path(lean_path)]:
        if os.path.exists(stale):
            os.remove(stale)   # best-effort: drop any stale scratch file(s) from a
                                 # previous interrupted run -- per-candidate isolate
                                 # files (glob) as well as the legacy shared one
    stub_blocks = parse_stub_blocks(lean_path)
    for name, stmt in stub_blocks.items():
        T.LOCAL_SIGS.setdefault(name, T.lean_binder_kinds(f"theorem {name}_c : {stmt}"))

    # Also seed every OTHER declaration already in this chapter's file -- including
    # ones solved in an earlier, separate `climb_upper.py` run -- so same-chapter
    # refs to already-solved lemmas resolve. LOCAL_SIGS is a fresh, empty dict every
    # process invocation; without this, each additional run only knows about the
    # current round's still-sorry stubs and progressively loses visibility into
    # everything a prior run already solved.
    # Discover any hand-added `import ...` lines beyond the single `prev_lean` one
    # write_chapter always writes (e.g. `import ...TarskiFinish`, needed for
    # `Tfinish`/`colr`/`cong_r`) -- a regenerate must carry these forward verbatim,
    # never silently drop them (same "preserved, not regenerated from a narrower
    # assumption" principle as the theorem-body preservation below). Confirmed by a
    # 2026-07-14 incident: without this, a det-only run on Ch11 silently dropped the
    # TarskiFinish import and broke every Tfinish-using theorem in the file, including
    # ones untouched by that round's attempts.
    extra_imports = []
    if os.path.exists(lean_path):
        lean_text_now = open(lean_path).read()
        expected_import = f"GeocoqTranslate.Tarski_dev.{prev_lean}"
        for m in re.finditer(r"^import (\S+)\s*$", lean_text_now, re.M):
            if m.group(1) != expected_import:
                extra_imports.append(m.group(1))
        for m in re.finditer(r"(?ms)^theorem (\w+)_c\s*:\s*\n?(.*?):=", lean_text_now):
            T.LOCAL_SIGS.setdefault(m.group(1), T.lean_binder_kinds(f"theorem {m.group(1)}_c : {m.group(2)}"))

    coq_text = open(coq_path).read()
    # GeoCoq source names can use the `P__Q` double-underscore convention (e.g.
    # `out2__conga`); the Lean stub generator collapses that to a single `_`
    # (`out2_conga_c`). Every downstream set-membership check below (`n in
    # stub_blocks`, `n in preserved`, `n in all_blocks`) compares against Lean-
    # side (collapsed) keys -- if `coq_names` keeps the raw double-underscore
    # form, any such lemma matches NEITHER `preserved` NOR `stub_blocks` and
    # silently vanishes from `all_names` (write_chapter's own emission list),
    # even though it's declared and (possibly) already solved. Confirmed live,
    # 2026-07-15: this is exactly what dropped 15 already-declared Ch11
    # theorems from the file entirely (not just reverted to sorry -- GONE),
    # while stale call sites elsewhere (inside `preserved`, protected from
    # blame/demotion by design) kept referencing them, breaking the whole
    # chapter's build and cascading to block every later chapter in the import
    # chain. `coq_names_raw` keeps the original form for oracle/run_proof
    # calls (`_resolve_coq_name` reverses the collapse there); `coq_names`
    # itself is now normalized so every match against Lean-side dicts works.
    coq_names_raw = re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w[\w']*)", coq_text, re.M)
    coq_names = [n.replace("__", "_") for n in coq_names_raw]
    ambient = ambient_prelude(coq_path)
    all_blocks = parse_all_blocks(lean_path)
    names = [n for n in coq_names if n in stub_blocks]                 # freshly attempted this round
    preserved = {n: all_blocks[n] for n in coq_names                   # carried forward verbatim,
                 if n in all_blocks and n not in stub_blocks}           # never silently dropped
    if not names:
        rec = dict(chapter=lean_stem, phase="det", total=len(preserved), clean=0, tainted=0, hole=0,
                    note="nothing left to attempt; all declared lemmas already solved or absent")
        _log(rec)
        return rec

    # --- phase 1: deterministic transliteration attempts ---------------
    bodies: dict[str, tuple[str, int] | None] = {}
    for name in names:
        bodies[name] = det_attempt(coq_path, _resolve_coq_name(name, coq_names_raw))
        if bodies[name] is not None:
            T.LOCAL_SIGS[name] = T.lean_binder_kinds(f"theorem {name}_c : {stub_blocks[name]}")

    # --- phases 2+3: BATCHED repair loop + kernel gate -------------------
    # Folding every fresh attempt into ONE giant build lets a single genuinely-broken
    # lemma's error cascade (Lean's error recovery emitting spurious diagnostics on
    # UNRELATED later declarations) get mis-attributed by build_errors' naive line-
    # bisection to innocent neighbors. `BATCH_SIZE` alone only contains the blast
    # radius to a 15-lemma window; it was NOT sufficient on its own (confirmed
    # empirically: 69/100 textually-clean Ch11 attempts were getting collaterally
    # demoted this way even with batching, and reran deterministically the same every
    # time). `isolate=True` (the default) is what actually makes this safe now:
    # fold_and_verify re-checks every flagged name in its own scratch file before
    # trusting the blame (see isolate_verify/triage_bad), so BATCH_SIZE is purely a
    # throughput knob at this point, not a correctness one.
    BATCH_SIZE = 15
    cur_preserved = dict(preserved)
    batch_clean, batch_tainted, total_rounds, total_rescued = [], [], 0, 0
    for i in range(0, len(names), BATCH_SIZE):
        batch = names[i:i + BATCH_SIZE]
        batch_bodies = {n: bodies[n] for n in batch}
        try:
            clean, tainted, hole, rounds, rescued = fold_and_verify(
                lean_path, prev_lean, tier, coq_names, stub_blocks, batch_bodies, cur_preserved,
                ambient, isolate=isolate, extra_imports=extra_imports)
        except UpstreamBuildError as e:
            rec = dict(chapter=lean_stem, phase="det", total=None, clean=0, tainted=0, hole=None,
                        error=f"BLOCKED by broken upstream file(s), not this chapter's own bug: "
                              f"{'; '.join(e.foreign_errors[:5])}")
            _log(rec)
            print(f"{lean_stem}: BLOCKED -- upstream file(s) broken, not attempted: "
                  f"{'; '.join(e.foreign_errors[:3])}", flush=True)
            return rec
        total_rescued += rescued
        if rounds is None:
            print(f"{lean_stem}: batch {i // BATCH_SIZE + 1} did not converge in "
                  f"{MAX_REPAIR_ROUNDS} rounds -- its names stay sorry", flush=True)
            continue
        total_rounds += rounds
        all_blocks_now = parse_all_blocks(lean_path)
        for n in batch:
            if n in clean or n in tainted:
                cur_preserved[n] = all_blocks_now[n]
        batch_clean += [n for n in clean if n in batch]
        batch_tainted += [n for n in tainted if n in batch]

    # Final aggregate pass: every batch converged on its own, but re-check the WHOLE
    # file once more before trusting that -- cheap, and catches any cross-batch
    # interaction the per-batch checks couldn't see. Routed through fold_and_verify
    # (bodies={}, nothing new attempted) rather than a hand-rolled build_errors/demote
    # pair, so this pass gets the SAME preserved-protection and isolation-on-ambiguity
    # guarantees as every other round -- the old hand-rolled version here had NEITHER,
    # making it actually less safe than the per-batch loop above it.
    try:
        clean, tainted, hole, rounds, rescued = fold_and_verify(
            lean_path, prev_lean, tier, coq_names, stub_blocks, {}, cur_preserved,
            ambient, isolate=isolate, extra_imports=extra_imports)
    except UpstreamBuildError as e:
        rec = dict(chapter=lean_stem, phase="det", total=None, clean=0, tainted=0, hole=None,
                    error=f"BLOCKED by broken upstream file(s) during final pass: "
                          f"{'; '.join(e.foreign_errors[:5])}")
        _log(rec)
        return rec
    total_rescued += rescued
    preserved = cur_preserved
    rounds = total_rounds if rounds is not None else None

    for n in clean:
        T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n}_c : {stub_blocks[n]}") if n in stub_blocks \
            else T.lean_binder_kinds(re.match(r"theorem \w+_c :\s*\n?(.*?):=", preserved[n], re.S).group(1))

    new_clean = len([n for n in clean if n in names])   # of what THIS round attempted, how many landed clean
    rec = dict(chapter=lean_stem, phase="det", total=len(clean) + len(tainted) + len(hole),
               clean=len(clean), tainted=len(tainted), hole=len(hole),
               new_clean_this_round=new_clean, attempted_this_round=len(names), rounds=rounds,
               cascade_rescued=total_rescued, isolate=isolate)
    _log(rec)
    print(f"{lean_stem}: det clean={len(clean)}/{len(clean)+len(tainted)+len(hole)} "
          f"tainted={len(tainted)} hole={len(hole)} "
          f"(+{new_clean} new this round, rounds={rounds}, cascade_rescued={total_rescued})", flush=True)

    # --- phase 4: LLM on the residue (opt-in) ----------------------------
    # `hole` (fold_and_verify's return) means "name absent from the axiom-check
    # output entirely" -- on any successfully-converged build EVERY declared
    # name gets axiom-checked, including untouched `:= sorry` ones (sorry
    # itself prints `sorryAx`), so they land in `tainted`, never `hole`. Gating
    # phase 4 on `hole` meant it essentially never fired through normal
    # climb_chapter/main() usage -- confirmed empirically 2026-07-14: a det+llm
    # run produced identical output to a det-only run, no "llm folded" line at
    # all, on a chapter with 4 real remaining sorries. The correct residue is
    # whatever is STILL a literal stub in the file right now.
    still_sorry = set(parse_stub_blocks(lean_path))
    if use_llm and still_sorry:
        import llm_path as L   # `glob` is now a module-level import (see top of file) --
        import concurrent.futures as cf   # a local `import glob` here would shadow it for
                                            # this WHOLE function (Python makes any name
                                            # imported/assigned anywhere in a function local
                                            # to the entire function), breaking the earlier
                                            # glob.glob(...) call in the cleanup block above.
        # _sig_of()'s authoritative-signature lookup (the mechanism that stops the
        # LLM guessing wrong `_c` arg order) only ever reads Climb_All.lean, a
        # frozen Ch02-10 snapshot -- without this, every Ch11+ dependency falls
        # through to a content-free placeholder hint. Cheap (once per chapter run,
        # not per lemma); harmless to include Ch02-10 files too (last-write-wins,
        # names are unique across the codebase).
        L.seed_upper_sigs(sorted(glob.glob(f"{LEAN}/*.lean")))
        climb_mod = _module_of(lean_path)          # this chapter's own module --
                                                     # not the hardcoded Ch10 default,
                                                     # so same-chapter/earlier-upper-
                                                     # chapter deps are actually in scope
        llm_bodies = dict(bodies)
        attempted = 0

        def _one(n):
            # Ch11+ stubs are an UNBOUND Pi-type (`stub_blocks[n]` has no colon --
            # parse_stub_blocks' regex consumes it before capture starts -- and
            # nothing is pre-bound as a theorem parameter, unlike Ch02-10). Both
            # llm_path's prompt and verify_one need the colon back and the real
            # binder count (nb) -- same source det_attempt already uses (count the
            # elaborated proof term's outer `fun` binders), computed independently
            # here since det_attempt returned None for exactly these holes.
            nb = 0
            coq_name = _resolve_coq_name(n, coq_names_raw)   # coq_names itself is now
                                                                # normalized (collapsed __ -> _,
                                                                # see its definition above) so it
                                                                # can no longer recover the raw
                                                                # double-underscore form -- must
                                                                # search coq_names_raw instead
            try:
                pt = run_proof(coq_path, coq_name, default_q_paths())
                ast = T.parse_term(T.P(T.tok(pt)), stop={None})
                while ast[0] == "paren":
                    ast = ast[1]
                if ast[0] == "fun":
                    nb = len(ast[1])
            except Exception:
                nb = 0
            try:
                body, _attempts, _mode = L.llm_translate(
                    coq_path, coq_name, ":" + stub_blocks[n], [], retries=2,
                    climb_mod=climb_mod, nb=nb, source="upper",
                    tier_var=TIER_VARS[tier], try_julien_first=True)
            except Exception:
                body = None
            return n, (body, nb) if body else None

        # Parallelized: each call is subprocess-isolated end to end -- `call_claude`
        # shells out per-call, `verify_one` writes a per-NAME scratch file
        # (`LLMTry_{name}.lean`, never shared across names) and its own `lake env
        # lean` subprocess, and `run_proof` opens its own `SerAPI`/sertop process
        # per call (see geolean_oracle/src/oracle.py's `with SerAPI(...) as s:`).
        # No file-level collision is possible between concurrent names. The one
        # shared mutable state is `T.LOCAL_SIGS` (a plain dict); worst case under
        # a race is a redundant/overwritten cache entry, never corruption -- the
        # GIL keeps individual dict ops atomic. LLM round-trips dominate wall-
        # clock (10-20s each per the pilot ledger), so this is the highest-
        # leverage place to parallelize given real time pressure: sequential over
        # a chapter's full hole-set could otherwise run for hours.
        MAX_LLM_WORKERS = 6
        with cf.ThreadPoolExecutor(max_workers=MAX_LLM_WORKERS) as ex:
            for n, result in ex.map(_one, still_sorry):
                attempted += 1
                llm_bodies[n] = result

        # try_julien_first=True (above) means accepted proofs may reference Tfinish/
        # TfinishA -- only 3 of 15 upper chapters happen to already import those
        # themselves, so guarantee them here too (dedup: write_chapter just emits
        # whatever's in this list, a harmless repeat if the chapter already had one).
        # TarskiConA imports Ch11 -- adding it to Ch11's OWN extra_imports is a genuine
        # circular import (confirmed live: this exact bug crashed Ch11's build across
        # an entire overnight sweep, 2026-07-15, before being caught the next morning).
        # Safe for every OTHER upper chapter (Ch12+), which already transitively import
        # Ch11 and so can't cycle back through it.
        julien_extras = ["GeocoqTranslate.Tarski_dev.TarskiFinish"]
        if lean_stem != "Ch11":
            julien_extras.append("GeocoqTranslate.Tarski_dev.TarskiConA")
        llm_extra_imports = list(dict.fromkeys(list(extra_imports) + julien_extras))
        clean2, tainted2, hole2, rounds2, rescued2 = fold_and_verify(
            lean_path, prev_lean, tier, coq_names, stub_blocks, llm_bodies, preserved,
            ambient, isolate=isolate, extra_imports=llm_extra_imports)
        if rounds2 is not None:
            for n in clean2:
                T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n}_c : {stub_blocks[n]}") if n in stub_blocks \
                    else T.LOCAL_SIGS.get(n)
            folded = len(clean2) - len(clean)
            rec2 = dict(chapter=lean_stem, phase="llm", attempted=attempted,
                        folded=folded, total_clean=len(clean2), total=len(clean2)+len(tainted2)+len(hole2),
                        cascade_rescued=rescued2, isolate=isolate)
            _log(rec2)
            print(f"{lean_stem}: llm folded {folded} more -> "
                  f"clean={len(clean2)}/{len(clean2)+len(tainted2)+len(hole2)}", flush=True)
        else:
            rec2 = dict(chapter=lean_stem, phase="llm", attempted=attempted,
                        error="post-LLM repair loop did not converge")
            _log(rec2)

    for stale in glob.glob(_isolate_path(lean_path, "*")) + [_isolate_path(lean_path)]:
        if os.path.exists(stale):
            os.remove(stale)   # best-effort scratch-file cleanup (glob covers any
                                 # per-candidate isolate files a crashed round left behind)
    return rec


def main():
    args = sys.argv[1:]
    resume = "--resume" in args
    args = [a for a in args if a != "--resume"]
    use_llm = "llm" in args
    args = [a for a in args if a != "llm"]
    # --no-isolate: disable per-lemma isolated re-verification of build_errors'
    # blame before demoting (see isolate_verify/triage_bad) -- reverts to the old,
    # faster-but-unsafe behavior. Only meant for A/B measurement of the fix, e.g.:
    #   python climb_upper.py Ch11 --no-isolate   then   python climb_upper.py Ch11
    # and diff the `clean`/`cascade_rescued` fields of the two logged ledger records.
    no_isolate = "--no-isolate" in args
    args = [a for a in args if a != "--no-isolate"]
    only = args[0] if args else None

    done = set()
    if resume and os.path.exists(LEDGER):
        for line in open(LEDGER):
            rec = json.loads(line)
            if rec.get("phase") == "det" and "error" not in rec:
                done.add(rec["chapter"])

    seed_base_pool()
    prev_lean = "Ch10Line2Extra"   # Ch10 + coplanar_perm_N (CoplanarPermExtra) +
                                    # Ch10_line_reflexivity_2.v's 31 lemmas (Ch10Line2Extra);
                                    # Ch11 imports through here now.
    for coq_stem, lean_stem, tier in CHAPTERS:
        if only and lean_stem != only:
            prev_lean = lean_stem
            continue
        if lean_stem in done:
            print(f"{lean_stem}: skipping (already in ledger)", flush=True)
            prev_lean = lean_stem
            continue
        climb_chapter(coq_stem, lean_stem, tier, prev_lean, use_llm=use_llm, isolate=not no_isolate)
        prev_lean = lean_stem
        if only:
            break


if __name__ == "__main__":
    main()
