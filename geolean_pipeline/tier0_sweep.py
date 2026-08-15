"""Tier 0: blind one-shot closer sweep, run BEFORE det_attempt on every
still-`sorry` name in a chapter. Doesn't touch Coq at all -- just wraps the
existing Lean *statement* with a fixed battery of already-ported automation
(`Tfinish`/`TfinishA`: colr + cong_r + assert_diffs + Tconga aesop rule-set,
plus subst_vars/tauto fallbacks) and lets the SAME fold_and_verify/
isolate_verify safety net used by det_attempt decide what actually compiles.

Deliberately reuses climb_upper.py's write_chapter/fold_and_verify/
kernel_check UNCHANGED -- only the body-generation step differs from
det_attempt. Ch11 gets `Tfinish` (TarskiConA depends on Ch11, so TfinishA is
unavailable there without a cycle); Ch12+ gets `TfinishA` (needs
`GeocoqTranslate.Tarski_dev.TarskiConA` as an extra import, added once here).

Usage: python3 tier0_sweep.py [ChapterName]   -- omit to run all (excl. Ch16b)
"""
import os, sys, re, json, time

REPO = "/Users/ayaansiddiqui/GeoCoq"
sys.path.insert(0, os.path.join(REPO, "geolean_pipeline"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(os.path.join(REPO, "lean/geocoq_translate"))
sys.path.insert(0, os.path.join(REPO, "lean/geocoq_translate"))
os.chdir(REPO)

import climb_upper as C

LEDGER = "geolean_pipeline/.tier0_ledger.jsonl"

# (lean_stem, prev_lean) -- Ch16b intentionally excluded (currently broken,
# out of scope per explicit decision 2026-07-14).
CHAIN = [
    ("Ch11",  "Ch10Line2Extra"),
    ("Ch12",  "Ch11"),
    ("Ch12b", "Ch12"),
    ("Ch13a", "Ch12b"),
    ("Ch13b", "Ch13a"),
    ("Ch13c", "Ch13b"),
    ("Ch13d", "Ch13c"),
    ("Ch13e", "Ch13d"),
    ("Ch13f", "Ch13e"),
    ("Ch14a", "Ch13f"),
    ("Ch14b", "Ch14a"),
    ("Ch14c", "Ch14b"),
    ("Ch15a", "Ch14c"),
    ("Ch15b", "Ch15a"),
    ("Ch16a", "Ch15b"),
]
TIER_OF = {ls: t for (cs, ls, t) in C.CHAPTERS}
COQ_STEM_OF = {ls: cs for (cs, ls, t) in C.CHAPTERS}


def _log(rec):
    rec["ts"] = time.time()
    with open(LEDGER, "a") as f:
        f.write(json.dumps(rec) + "\n")


def tier0_bodies_for(lean_stem: str, stub_blocks: dict) -> dict:
    """name -> (body, nb) for every stub, using the blind closer battery."""
    bodies = {}
    for name, stmt in stub_blocks.items():
        nb = len(C.T.lean_binder_kinds(f"theorem {name}_c : {stmt}"))
        if lean_stem == "Ch11":
            body = ("by\n"
                    "  first\n"
                    "    | Tfinish\n"
                    "    | (subst_vars; first | assumption | Tfinish | tauto)\n"
                    "    | tauto\n")
        else:
            body = "by\n  TfinishA\n"
        bodies[name] = (body, nb)
    return bodies


def run_chapter(lean_stem: str, prev_lean: str):
    lean_path = f"{C.LEAN}/{lean_stem}.lean"
    tier = TIER_OF[lean_stem]
    stub_blocks = C.parse_stub_blocks(lean_path)
    for name, stmt in stub_blocks.items():
        C.T.LOCAL_SIGS.setdefault(name, C.T.lean_binder_kinds(f"theorem {name}_c : {stmt}"))

    if not stub_blocks:
        print(f"{lean_stem}: no stubs left, skipping Tier 0", flush=True)
        _log(dict(chapter=lean_stem, phase="tier0", total=0, clean=0, tainted=0, hole=0,
                   note="nothing to attempt"))
        return

    coq_path = f"{C.COQ_ROOT}/{COQ_STEM_OF[lean_stem]}.v"
    coq_text = open(coq_path).read()
    coq_names = re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w[\w']*)", coq_text, re.M)
    ambient = C.ambient_prelude(coq_path)
    all_blocks = C.parse_all_blocks(lean_path)
    preserved = {n: all_blocks[n] for n in coq_names if n in all_blocks and n not in stub_blocks}

    extra_imports = []
    lean_text_now = open(lean_path).read()
    expected_import = f"GeocoqTranslate.Tarski_dev.{prev_lean}"
    for m in re.finditer(r"^import (\S+)\s*$", lean_text_now, re.M):
        if m.group(1) != expected_import:
            extra_imports.append(m.group(1))
    if lean_stem != "Ch11":
        conA = "GeocoqTranslate.Tarski_dev.TarskiConA"
        if conA not in extra_imports:
            extra_imports.append(conA)

    bodies = tier0_bodies_for(lean_stem, stub_blocks)
    print(f"{lean_stem}: Tier 0 -- attempting {len(bodies)} stub(s) blind ({extra_imports=})", flush=True)

    try:
        clean, tainted, hole, rounds, rescued = C.fold_and_verify(
            lean_path, prev_lean, tier, coq_names, {n: stub_blocks[n] for n in coq_names if n in stub_blocks},
            dict(bodies), preserved, ambient, isolate=True, extra_imports=extra_imports)
    except C.UpstreamBuildError as e:
        rec = dict(chapter=lean_stem, phase="tier0", total=None, clean=0, tainted=0, hole=None,
                   error=f"BLOCKED by upstream: {'; '.join(e.foreign_errors[:5])}")
        _log(rec)
        print(f"{lean_stem}: Tier0 BLOCKED -- {'; '.join(e.foreign_errors[:3])}", flush=True)
        return

    # `tainted` (from fold_and_verify) means "has sorryAx in its axiom list" --
    # a name demoted back to a literal `:= sorry` during the repair loop is
    # STILL "tainted" by that definition (sorry itself prints sorryAx), so
    # `n in clean or n in tainted` is NOT evidence of a real body. The only
    # reliable signal is: is `n` still a literal stub in the file NOW?
    still_stub = set(C.parse_stub_blocks(lean_path))
    newly_closed = [n for n in bodies if n not in still_stub]
    newly_clean = [n for n in newly_closed if n in clean]
    newly_tainted = [n for n in newly_closed if n not in clean]
    rec = dict(chapter=lean_stem, phase="tier0", total=len(bodies), newly_closed=len(newly_closed),
               newly_clean=len(newly_clean), newly_tainted=len(newly_tainted), rounds=rounds, rescued=rescued)
    _log(rec)
    print(f"{lean_stem}: Tier 0 done -- {len(newly_closed)}/{len(bodies)} closed "
          f"({len(newly_clean)} clean, {len(newly_tainted)} tainted), rounds={rounds}", flush=True)
    if newly_closed:
        print(f"  closed: {sorted(newly_closed)}", flush=True)


if __name__ == "__main__":
    C.seed_base_pool()
    only = sys.argv[1] if len(sys.argv) > 1 else None
    for lean_stem, prev_lean in CHAIN:
        if only and lean_stem != only:
            continue
        run_chapter(lean_stem, prev_lean)
        if only:
            break
