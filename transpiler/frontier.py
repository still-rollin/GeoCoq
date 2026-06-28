#!/usr/bin/env python3
"""
frontier — the honest bottom-up coverage engine.

A lemma is only ATTEMPTED once every one of its Elements dependencies has a
`.olean` on disk. So a failure here is always a *genuine own-error*, never a
cascade artifact (the flaw that inflated the old "229").

Loop:
  compiled := {lemmas whose .olean exists}
  repeat:
    frontier := {L not compiled, all Elements-deps(L) ⊆ compiled}
    build the whole frontier in ONE `lake build` (no inter-deps among them)
    newly-compiled → add to compiled; the rest are this layer's ROOT FAILURES
  until a pass adds nothing new.

Output: COMPILED count + the exact current root-failure frontier (with the head
of each lemma's own error), which is the actionable fix list. Re-run after each
fix to peel the next layer.

Usage:  python3 frontier.py            # analyse + drive one full sweep
        python3 frontier.py --once     # single frontier pass (faster)
"""
from __future__ import annotations
import glob, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, ".."))
COQ_ROOT = os.path.join(REPO, "theories", "Elements", "OriginalProofs")
PKG = os.path.join(REPO, "lean", "geocoq_translate")
ELEM = os.path.join(PKG, "GeocoqTranslate", "Elements", "OriginalProofs")
OLEAN = os.path.join(PKG, ".lake", "build", "lib", "lean",
                     "GeocoqTranslate", "Elements", "OriginalProofs")
SKIP = {"book1", "euclidean_defs", "euclidean_tactics", "general_tactics",
        "euclidean_axioms"}

def lemma_names() -> list[str]:
    out = []
    for f in sorted(glob.glob(os.path.join(COQ_ROOT, "*.v"))):
        n = os.path.basename(f)[:-2]
        if n in SKIP:
            continue
        if re.search(rf"^(Lemma|Theorem|Proposition|Corollary)\s+{re.escape(n)}\b",
                     open(f).read(), re.MULTILINE):
            out.append(n)
    return out

def lean_path(n: str) -> str:
    return os.path.join(ELEM, "Lemmas" if n.startswith("lemma_") else "", f"{n}.lean")

def module(n: str) -> str:
    base = "GeocoqTranslate.Elements.OriginalProofs"
    return f"{base}.Lemmas.{n}" if n.startswith("lemma_") else f"{base}.{n}"

def olean(n: str) -> str:
    return os.path.join(OLEAN, "Lemmas" if n.startswith("lemma_") else "", f"{n}.olean")

_IMP = re.compile(r"import GeocoqTranslate\.Elements\.OriginalProofs"
                  r"(?:\.Lemmas)?\.([A-Za-z0-9_]+)")

def deps(n: str, allnames: set[str]) -> set[str]:
    p = lean_path(n)
    if not os.path.exists(p):
        return set()
    found = set(_IMP.findall(open(p).read()))
    return {d for d in found if d in allnames and d != n}

def main():
    once = "--once" in sys.argv
    names = lemma_names()
    nameset = set(names)
    dep = {n: deps(n, nameset) for n in names}
    compiled = {n for n in names if os.path.exists(olean(n))}

    root_fail: dict[str, str] = {}
    while True:
        frontier = sorted(n for n in names
                          if n not in compiled and dep[n] <= compiled)
        # drop ones we already know fail (avoid rebuilding known roots forever)
        todo = [n for n in frontier if n not in root_fail]
        if not todo:
            break
        print(f"[frontier] attempting {len(todo)} lemmas "
              f"(compiled={len(compiled)}/{len(names)})", flush=True)
        r = subprocess.run(["lake", "build", *[module(n) for n in todo]],
                           cwd=PKG, capture_output=True, text=True)
        log = r.stdout + r.stderr
        own = set(re.findall(r"error: .*?(?:Lemmas/|OriginalProofs/)([A-Za-z0-9_]+)\.lean", log))
        progressed = False
        for n in todo:
            if os.path.exists(olean(n)):
                compiled.add(n); progressed = True
            else:
                # capture the head of this lemma's own error
                msgs = re.findall(rf"error: [^\n]*{re.escape(n)}\.lean:[^\n]*", log)
                root_fail[n] = msgs[0] if msgs else "(no own error line — investigate)"
        if once or not progressed:
            break

    print(f"\n========== FRONTIER COVERAGE ==========")
    print(f"total            : {len(names)}")
    print(f"COMPILED (olean) : {len(compiled)}  ({100*len(compiled)//len(names)}%)")
    blocked = [n for n in names if n not in compiled]
    print(f"NOT compiled     : {len(blocked)}")
    print(f"ROOT FAILURES (deps satisfied, lemma itself fails): {len(root_fail)}")
    print()
    for n in sorted(root_fail):
        print(f"  • {n}")
        print(f"      {root_fail[n].split('error: ',1)[-1][:160]}")
    still_blocked = [n for n in blocked if n not in root_fail]
    print(f"\nstill cascade-blocked (waiting on a root fix): {len(still_blocked)}")

if __name__ == "__main__":
    main()
