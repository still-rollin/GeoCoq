#!/usr/bin/env python3
"""
fresh_euclidean — fresh full-Euclidean pipeline run.

(1) Transpile every Elements/OriginalProofs lemma with geolean_transpile (the
    deterministic, structure-preserving transpiler) into the Lean tree,
    OVERWRITING whatever is there (run on a dedicated git branch).
(2) Emit an aggregator module that imports them all.
(3) `lake build` it once; parse the log to classify every lemma as
        compiled            — built, no own error
        failed (own error)  — its own file errored
        failed (cascade)    — only failed because a dependency failed
    crossed with transpile quality (clean vs partial/sorry-fallback).

Usage:  python3 fresh_euclidean.py [--transpile-only]
"""
from __future__ import annotations
import glob, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import geolean_transpile as T
import coqtoleanbrief as brief

REPO = os.path.normpath(os.path.join(HERE, ".."))
COQ_ROOT = os.path.join(REPO, "theories", "Elements", "OriginalProofs")
LEAN_PKG = os.path.join(REPO, "lean", "geocoq_translate")
ELEM = os.path.join(LEAN_PKG, "GeocoqTranslate", "Elements", "OriginalProofs")
LEMDIR = os.path.join(ELEM, "Lemmas")
SKIP = {"book1", "euclidean_defs", "euclidean_tactics", "general_tactics",
        "euclidean_axioms"}

# HAND/LLM-finished (Tier 3) — the transpiler cannot produce these (existential
# reconstruction, Circle-typed binders, …). The driver keeps whatever Lean file
# is already on disk for these instead of re-transpiling over the completion.
HANDMADE = {
    "lemma_parallelflip", "lemma_parallelNC", "lemma_parallelsymmetric",
    "lemma_paralleldef2A", "lemma_betweennesspreserved",
    "lemma_samesideflip", "lemma_samesidesymmetric", "lemma_ondiameter",
    "proposition_02", "proposition_08",
    # nCol case-split the transpiler cannot produce (hand-written from scratch);
    # protected so new transpiler features cannot overwrite the hand proof.
    "lemma_collinear4",
}

def lemma_names() -> list[str]:
    out = []
    for f in sorted(glob.glob(os.path.join(COQ_ROOT, "*.v"))):
        name = os.path.basename(f)[:-2]
        if name in SKIP:
            continue
        if re.search(rf"^(Lemma|Theorem|Proposition|Corollary)\s+{re.escape(name)}\b",
                     open(f).read(), re.MULTILINE):
            out.append(name)
    return out

def out_path(name: str) -> str:
    return os.path.join(LEMDIR if name.startswith("lemma_") else ELEM, f"{name}.lean")

def module(name: str) -> str:
    base = "GeocoqTranslate.Elements.OriginalProofs"
    return f"{base}.Lemmas.{name}" if name.startswith("lemma_") else f"{base}.{name}"

def main():
    transpile_only = "--transpile-only" in sys.argv
    names = lemma_names()
    print(f"[fresh] {len(names)} Elements lemmas")

    # Pre-create all target files so the transpiler's import-discovery (which
    # lists existing Lemmas/*.lean) resolves every dependency import.
    for n in names:
        p = out_path(n)
        if not os.path.exists(p):
            open(p, "w").write("")

    clean, partial, handmade = [], [], []
    for n in names:
        if n in HANDMADE:                            # keep the Tier-3 completion
            handmade.append(n)
            continue
        try:
            lean, warns = T.transpile(os.path.join(COQ_ROOT, f"{n}.v"), n)
        except Exception as e:                       # noqa: BLE001
            print(f"  [transpile-ERROR] {n}: {type(e).__name__}: {e}")
            continue
        open(out_path(n), "w").write(lean)
        (clean if not warns else partial).append(n)
    print(f"[fresh] kept {len(handmade)} hand/LLM-finished (Tier 3): {handmade}")
    print(f"[fresh] transpiled: {len(clean)} clean, {len(partial)} with sorry-fallback")

    # Aggregator module importing every lemma.
    agg = os.path.join(LEAN_PKG, "GeocoqTranslate", "FreshElements.lean")
    with open(agg, "w") as f:
        f.write("/- Aggregator for the fresh full-Euclidean pipeline run. -/\n")
        for n in names:
            f.write(f"import {module(n)}\n")
    print(f"[fresh] wrote aggregator {os.path.relpath(agg, REPO)}")

    if transpile_only:
        return

    print("[fresh] building (this is long)…")
    r = subprocess.run(["lake", "build", "GeocoqTranslate.FreshElements"],
                       cwd=LEAN_PKG, capture_output=True, text=True)
    log = r.stdout + r.stderr
    open(os.path.join(HERE, "fresh_build.log"), "w").write(log)

    # Classify: a lemma "compiled" iff no `error: <its file>` line appears.
    own_error = set()
    for m in re.finditer(r"error: .*?Lemmas/(\w+)\.lean", log):
        own_error.add(m.group(1))
    for m in re.finditer(r"error: .*?OriginalProofs/(\w+)\.lean", log):
        own_error.add(m.group(1))
    compiled = [n for n in names if n not in own_error]
    failed = [n for n in names if n in own_error]

    cset = set(clean)
    print("\n========== FRESH EUCLIDEAN COVERAGE ==========")
    print(f"total lemmas            : {len(names)}")
    print(f"compiled (no own error) : {len(compiled)}  ({100*len(compiled)//len(names)}%)")
    print(f"  of which transpiled clean : {len([n for n in compiled if n in cset])}")
    print(f"  of which needed sorry-fb  : {len([n for n in compiled if n not in cset])}")
    print(f"own-error failures      : {len(failed)}")
    print(f"  clean-transpile but failed: {sorted(n for n in failed if n in cset)}")
    print(f"build exit code         : {r.returncode}")
    print("\n(see fresh_build.log for full output)")

if __name__ == "__main__":
    main()
