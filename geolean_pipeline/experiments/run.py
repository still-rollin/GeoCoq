"""
CLI for the autonomous GeoCoq→Lean transliteration pipeline.

  python geolean_pipeline/run.py Ch03_bet
  python geolean_pipeline/run.py Ch04_cong_bet OrchCh04
  python geolean_pipeline/run.py theories/.../Foo.v lean/.../Foo.lean OutModule

For a chapter shorthand `ChNN_name`, the Coq file is
`theories/Main/Tarski_dev/<name>.v` and the Lean stub (source of statements)
is `lean/geocoq_translate/GeocoqTranslate/Tarski_dev/<name>.lean`.

Prints the ledger (accepted/unsupported/blocked) and runs the verify gate
(`lake env lean` + `#print axioms`). Original files are never modified.
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import orchestrator as O

LEAN_DIR = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"


def resolve(args):
    if args and args[0].endswith(".v"):
        coq = args[0]
        lean = args[1]
        out = args[2] if len(args) > 2 else "OrchOut"
    else:
        name = args[0]
        coq = f"theories/Main/Tarski_dev/{name}.v"
        lean = f"{LEAN_DIR}/{name}.lean"
        out = args[1] if len(args) > 1 else f"Orch_{name}"
    return coq, lean, out


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    coq, lean, out = resolve(sys.argv[1:])
    print(f"=== PIPELINE: {coq}  (statements from {lean}) ===")
    ledger, emitted, out_path = O.run(coq, lean, out)
    tot = sum(len(v) for v in ledger.values())
    print(f"accepted (transliterated) : {len(ledger['accepted'])}/{tot}  {ledger['accepted']}")
    print(f"unsupported               : {len(ledger['unsupported'])}")
    for n, r in ledger['unsupported'][:8]:
        print(f"     - {n}: {r}")
    print(f"blocked (non-cone dep)    : {len(ledger['blocked'])}")
    for n, r in ledger['blocked'][:8]:
        print(f"     - {n}: {r}")
    print(f"no lean stub              : {len(ledger['no_stub'])}")
    print(f"\noutput: {out_path}")
    print("=== VERIFY GATE (lake env lean + #print axioms) ===")
    clean, errors, _ = O.verify(out_path)
    ok = [n for n, ax in clean if 'sorryAx' not in ax]
    print(f"axiom-clean confirmed: {len(ok)}/{len(ledger['accepted'])}  {ok}")
    if errors:
        print(f"compile errors: {len(errors)}")
        for e in errors[:6]:
            print("   ", e[:120])


if __name__ == "__main__":
    main()
