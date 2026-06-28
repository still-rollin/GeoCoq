#!/usr/bin/env python3
"""Run geolean_transpile over all of Elements/OriginalProofs and report
parse coverage (how many proofs transpile with zero `sorry` fallbacks)."""
from __future__ import annotations
import collections
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geolean_transpile as T

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "..", "theories", "Elements", "OriginalProofs")
SKIP = {"book1", "euclidean_defs", "euclidean_tactics", "general_tactics"}

full, partial, errored = [], [], []
warn_kinds = collections.Counter()

files = sorted(glob.glob(os.path.join(ROOT, "*.v")))
for f in files:
    name = os.path.basename(f)[:-2]
    if name in SKIP:
        continue
    if not re.search(rf"^(Lemma|Theorem|Proposition|Corollary)\s+{re.escape(name)}\b",
                     open(f).read(), re.MULTILINE):
        continue
    try:
        _, warnings = T.transpile(f, name)
    except SystemExit as e:
        errored.append((name, f"not found: {e}"))
        continue
    except Exception as e:                      # noqa: BLE001 — never crash the run
        errored.append((name, f"{type(e).__name__}: {e}"))
        continue
    for w in warnings:
        warn_kinds[w.split(":")[0]] += 1
    (full if not warnings else partial).append((name, len(warnings)))

tot = len(full) + len(partial) + len(errored)
print(f"=== GeoCoq Elements/OriginalProofs transpile coverage ===")
print(f"total lemmas:        {tot}")
print(f"0-fallback (clean):  {len(full)}  ({100*len(full)//tot}%)")
print(f"partial (>0 sorry):  {len(partial)}")
print(f"transpiler errored:  {len(errored)}")
print()
print("fallback-count histogram (partial proofs):")
hist = collections.Counter(n for _, n in partial)
for k in sorted(hist):
    print(f"  {k:3d} fallback(s): {hist[k]} proofs")
print()
print("top fallback reasons:")
for kind, c in warn_kinds.most_common(8):
    print(f"  {c:4d}  {kind}")
print()
print("sample of clean (0-fallback) lemmas:")
for n, _ in full[:25]:
    print(f"  {n}")
