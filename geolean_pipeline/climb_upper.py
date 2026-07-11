"""
climb_upper — deterministic-then-LLM proof filling for the UPPER chapters
(Ch11..Ch16b, the 973 statement-stubs generated this session), architected
as a sibling to `climb.py` (which does the same job for Ch02..Ch10).

Per chapter, in dependency order:
  1. DETERMINISTIC pass: oracle (Show Proof) + translit.py transliterates
     every `:= sorry` hole into a real Lean proof attempt. No LLM, no cost.
  2. REPAIR LOOP: fold attempts into the chapter file, `lake build`, demote
     any lemma whose body doesn't compile back to a tracked `:= sorry`,
     repeat until the file is error-free (bounded, with an explicit
     non-convergence report instead of silently giving up).
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
"""
from __future__ import annotations
import os, sys, re, json, subprocess, time

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
    this is what silently dropped 31 already-solved theorems on 2026-07-10."""
    if not os.path.exists(lean_path):
        return {}
    text = open(lean_path).read()
    blocks = re.split(r"(?=^theorem \w+_c :)", text, flags=re.M)
    out = {}
    for b in blocks:
        m = re.match(r"theorem (\w+)_c :", b)
        if m:
            out[m.group(1)] = b.rstrip("\n")
    return out


def write_chapter(out_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved, ambient=""):
    """coq_names: full chapter name list in original file order (drives
    output order -- must match so within-chapter forward/backward refs still
    resolve top-to-bottom like Lean requires). preserved: {name: raw block
    text} carried forward verbatim for names NOT being (re)attempted this
    call -- never silently dropped, unlike a plain `names`-only regenerate.
    ambient: Section-level `variable`/`def` lines (see ambient_prelude) that
    must be re-emitted every time -- dropping them silently breaks every
    later theorem that mentions an ambient point like Ch14+'s O/E/E'."""
    out = [f"import GeocoqTranslate.Tarski_dev.{prev_lean}", "",
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
            if nb:
                out.append(f"  intro {bnames}")
            out.append(b[3:])
            out.append("")
        else:
            out.append(f"theorem {n}_c :\n    {stmt} :=")
            out.append(f"  fun {bnames} =>\n  {b}\n" if nb else f"  {b}\n")
    for n in all_names:
        out.append(f"#print axioms GeocoqTranslate.Tarski.Base.{n}_c")
    out.append("end GeocoqTranslate.Tarski.Base")
    open(out_path, "w").write("\n".join(out))


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


def fold_and_verify(lean_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved, ambient=""):
    """Write `bodies` into the chapter file (plus `preserved` carried forward
    verbatim), repair-loop to an error-free build, then kernel-gate over
    EVERY declaration in the file (preserved + freshly attempted), not just
    this round's subset -- otherwise already-solved entries silently drop
    out of the reported clean/tainted counts too.
    Returns (clean, tainted, hole, rounds_or_None). `rounds is None` means
    the repair loop did NOT converge — the file is left in its last
    (still-erroring) state for manual follow-up rather than silently
    reporting a wrong zero."""
    write_chapter(lean_path, prev_lean, tier, coq_names, stub_blocks, bodies, preserved, ambient)
    all_names = [n for n in coq_names if n in preserved or n in stub_blocks]

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
            return clean, tainted, hole, rounds
        demote(lean_path, bad)
        for n in bad:
            bodies[n] = None
    return [], [], list(all_names), None


def climb_chapter(coq_stem: str, lean_stem: str, tier: str, prev_lean: str,
                   use_llm: bool = False) -> dict:
    coq_path = f"{COQ_ROOT}/{coq_stem}.v"
    lean_path = f"{LEAN}/{lean_stem}.lean"
    stub_blocks = parse_stub_blocks(lean_path)
    for name, stmt in stub_blocks.items():
        T.LOCAL_SIGS.setdefault(name, T.lean_binder_kinds(f"theorem {name}_c : {stmt}"))

    # Also seed every OTHER declaration already in this chapter's file -- including
    # ones solved in an earlier, separate `climb_upper.py` run -- so same-chapter
    # refs to already-solved lemmas resolve. LOCAL_SIGS is a fresh, empty dict every
    # process invocation; without this, each additional run only knows about the
    # current round's still-sorry stubs and progressively loses visibility into
    # everything a prior run already solved.
    if os.path.exists(lean_path):
        for m in re.finditer(r"(?ms)^theorem (\w+)_c\s*:\s*\n?(.*?):=", open(lean_path).read()):
            T.LOCAL_SIGS.setdefault(m.group(1), T.lean_binder_kinds(f"theorem {m.group(1)}_c : {m.group(2)}"))

    coq_text = open(coq_path).read()
    coq_names = re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w[\w']*)", coq_text, re.M)
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
        bodies[name] = det_attempt(coq_path, name)
        if bodies[name] is not None:
            T.LOCAL_SIGS[name] = T.lean_binder_kinds(f"theorem {name}_c : {stub_blocks[name]}")

    # --- phases 2+3: BATCHED repair loop + kernel gate -------------------
    # Folding every fresh attempt into ONE giant build lets a single genuinely-broken
    # lemma's error cascade (Lean's error recovery emitting spurious diagnostics on
    # UNRELATED later declarations) get mis-attributed by build_errors' naive line-
    # bisection to innocent neighbors, which then get wrongly demoted -- and since
    # demote() never retries anything, they stay wrongly `sorry` for the rest of the
    # run (confirmed empirically: 69/100 textually-clean Ch11 attempts were getting
    # collaterally demoted this way, and reran deterministically the same every time).
    # Processing `names` in small batches contains each bad lemma's blast radius to
    # its own batch instead of the whole chapter.
    BATCH_SIZE = 15
    cur_preserved = dict(preserved)
    batch_clean, batch_tainted, total_rounds = [], [], 0
    for i in range(0, len(names), BATCH_SIZE):
        batch = names[i:i + BATCH_SIZE]
        batch_bodies = {n: bodies[n] for n in batch}
        try:
            clean, tainted, hole, rounds = fold_and_verify(
                lean_path, prev_lean, tier, coq_names, stub_blocks, batch_bodies, cur_preserved, ambient)
        except UpstreamBuildError as e:
            rec = dict(chapter=lean_stem, phase="det", total=None, clean=0, tainted=0, hole=None,
                        error=f"BLOCKED by broken upstream file(s), not this chapter's own bug: "
                              f"{'; '.join(e.foreign_errors[:5])}")
            _log(rec)
            print(f"{lean_stem}: BLOCKED -- upstream file(s) broken, not attempted: "
                  f"{'; '.join(e.foreign_errors[:3])}", flush=True)
            return rec
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

    # Final aggregate pass: every batch converged (build_errors == empty) on its own,
    # but re-check the WHOLE file once more before trusting that -- cheap, and catches
    # any cross-batch interaction the per-batch checks couldn't see.
    all_names = [n for n in coq_names if n in cur_preserved or n in stub_blocks]
    try:
        bad_final = build_errors(lean_path, all_names)
    except UpstreamBuildError as e:
        rec = dict(chapter=lean_stem, phase="det", total=None, clean=0, tainted=0, hole=None,
                    error=f"BLOCKED by broken upstream file(s) during final pass: "
                          f"{'; '.join(e.foreign_errors[:5])}")
        _log(rec)
        return rec
    if bad_final:
        demote(lean_path, bad_final)
    ax = kernel_check(lean_path, all_names)
    clean = [n for n in all_names if n in ax and "sorryAx" not in ax[n]]
    tainted = [n for n in all_names if n in ax and "sorryAx" in ax[n]]
    hole = [n for n in all_names if n not in clean and n not in tainted]
    preserved = cur_preserved
    rounds = total_rounds

    for n in clean:
        T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n}_c : {stub_blocks[n]}") if n in stub_blocks \
            else T.lean_binder_kinds(re.match(r"theorem \w+_c :\s*\n?(.*?):=", preserved[n], re.S).group(1))

    new_clean = len([n for n in clean if n in names])   # of what THIS round attempted, how many landed clean
    rec = dict(chapter=lean_stem, phase="det", total=len(clean) + len(tainted) + len(hole),
               clean=len(clean), tainted=len(tainted), hole=len(hole),
               new_clean_this_round=new_clean, attempted_this_round=len(names), rounds=rounds)
    _log(rec)
    print(f"{lean_stem}: det clean={len(clean)}/{len(clean)+len(tainted)+len(hole)} "
          f"tainted={len(tainted)} hole={len(hole)} "
          f"(+{new_clean} new this round, rounds={rounds})", flush=True)

    # --- phase 4: LLM on the residue (opt-in) ----------------------------
    if use_llm and hole:
        import llm_path as L
        llm_bodies = dict(bodies)
        attempted = 0
        for n in hole:
            attempted += 1
            try:
                body, _mode = L.llm_translate(coq_path, n, stub_blocks[n], [], retries=2)
            except Exception:
                body = None
            llm_bodies[n] = (body, 0) if body else None

        clean2, tainted2, hole2, rounds2 = fold_and_verify(
            lean_path, prev_lean, tier, coq_names, stub_blocks, llm_bodies, preserved, ambient)
        if rounds2 is not None:
            for n in clean2:
                T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n}_c : {stub_blocks[n]}") if n in stub_blocks \
                    else T.LOCAL_SIGS.get(n)
            folded = len(clean2) - len(clean)
            rec2 = dict(chapter=lean_stem, phase="llm", attempted=attempted,
                        folded=folded, total_clean=len(clean2), total=len(clean2)+len(tainted2)+len(hole2))
            _log(rec2)
            print(f"{lean_stem}: llm folded {folded} more -> "
                  f"clean={len(clean2)}/{len(clean2)+len(tainted2)+len(hole2)}", flush=True)
        else:
            rec2 = dict(chapter=lean_stem, phase="llm", attempted=attempted,
                        error="post-LLM repair loop did not converge")
            _log(rec2)

    return rec


def main():
    args = sys.argv[1:]
    resume = "--resume" in args
    args = [a for a in args if a != "--resume"]
    use_llm = "llm" in args
    args = [a for a in args if a != "llm"]
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
        climb_chapter(coq_stem, lean_stem, tier, prev_lean, use_llm=use_llm)
        prev_lean = lean_stem
        if only:
            break


if __name__ == "__main__":
    main()
