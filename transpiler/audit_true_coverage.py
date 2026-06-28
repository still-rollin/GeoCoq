#!/usr/bin/env python3
"""
audit_true_coverage — the HONEST coverage audit.

Unlike fresh_euclidean (which classified by grepping a build log and was fooled by
stale `.olean`s + cascade failures counted as "compiled"), this measures ground
truth after a *clean* rebuild:

  compiled  := the lemma's `.olean` exists on disk  (it truly built, kernel-checked)
  failed    := no `.olean`  (own error OR a dependency failed)

Then splits `failed` into:
  own-error := the build log has an `error:` line citing THIS file
  cascade   := failed but no own error line  (a dependency broke first)

Run AFTER: deleting Elements oleans + `lake build GeocoqTranslate.FreshElements`.
"""
from __future__ import annotations
import glob, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, ".."))
COQ_ROOT = os.path.join(REPO, "theories", "Elements", "OriginalProofs")
LEAN_PKG = os.path.join(REPO, "lean", "geocoq_translate")
OLEAN_ROOT = os.path.join(LEAN_PKG, ".lake", "build", "lib", "lean",
                          "GeocoqTranslate", "Elements", "OriginalProofs")
LOG = sys.argv[1] if len(sys.argv) > 1 else "/tmp/true_rebuild.log"
SKIP = {"book1", "euclidean_defs", "euclidean_tactics", "general_tactics",
        "euclidean_axioms"}

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

def olean_path(name: str) -> str:
    sub = "Lemmas" if name.startswith("lemma_") else ""
    return os.path.join(OLEAN_ROOT, sub, f"{name}.olean")

def main():
    names = lemma_names()
    log = open(LOG).read() if os.path.exists(LOG) else ""
    own_err = set()
    for m in re.finditer(r"error: .*?(?:Lemmas/|OriginalProofs/)([A-Za-z0-9_]+)\.lean", log):
        own_err.add(m.group(1))

    compiled, own_fail, cascade = [], [], []
    for n in names:
        if os.path.exists(olean_path(n)):
            compiled.append(n)
        elif n in own_err:
            own_fail.append(n)
        else:
            cascade.append(n)

    tot = len(names)
    print(f"========== TRUE EUCLIDEAN COVERAGE (clean rebuild) ==========")
    print(f"total lemmas       : {tot}")
    print(f"COMPILED (olean)   : {len(compiled)}  ({100*len(compiled)//tot}%)")
    print(f"own-error failures : {len(own_fail)}")
    print(f"cascade failures   : {len(cascade)}  (blocked by a broken dependency)")
    print()
    print("=== OWN-ERROR (fix these; each unblocks its cascade) ===")
    for n in sorted(own_fail):
        print(f"  {n}")
    print()
    print(f"=== CASCADE ({len(cascade)}) — will likely clear once own-errors fixed ===")
    print("  " + ", ".join(sorted(cascade)))

if __name__ == "__main__":
    main()
