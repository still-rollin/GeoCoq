"""
Live end-to-end demo of the pipeline on ONE lemma, stage by stage, then the
autonomous batch + verify gate. Run:  python geolean_pipeline/demo.py [lemma]
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import re
import translit as T
import orchestrator as O
from src.oracle import (run_proof, extract_lemma_source, default_q_paths,
                        collect_geocoq_lemma_names)
from src.port_map import get_lean_signature

COQ = "theories/Main/Tarski_dev/Ch03_bet.v"
LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch03_bet.lean"
BAR = "═" * 70


def hdr(t): print(f"\n{BAR}\n  {t}\n{BAR}")


def walkthrough(name):
    stubs = O.parse_stubs(LEAN)
    tail, binders = stubs[name]
    KNOWN = collect_geocoq_lemma_names(os.path.join(os.getcwd(), "theories"))

    hdr(f"LIVE PIPELINE  ·  {name}   (GeoCoq → Lean, zero LLM)")

    print("\n▶ INPUT — the GeoCoq (Coq) lemma:\n")
    print(extract_lemma_source(COQ, name))

    pt = run_proof(COQ, name, default_q_paths())
    print("\n▶ STAGE 1 · ORACLE — Coq's proof term (`Show Proof`):\n")
    print(pt)

    used = sorted({t for t in re.findall(r"[A-Za-z_][A-Za-z0-9_']*", pt) if t in KNOWN})
    print("\n▶ STAGE 2 · PORT_MAP — Lean signature of each lemma it uses:\n")
    for u in used:
        ms = get_lean_signature(u)["matches"]
        cone = [m for m in ms if any(cf in m["file"] for cf in T.CONE_FILES)]
        sig = cone[0]["signature"] if cone else (f"{u}  (Tarski axiom / in scope)"
              if u in T.ALLOW_AXIOMS else "NOT ported")
        print(f"   {u:28s} {sig}")

    ast = T.parse_term(T.P(T.tok(pt)), stop={None})
    while ast[0] == "paren":
        ast = ast[1]
    body = T.emit_body(ast[2], dict(zip(ast[1], binders)), [])
    print("\n▶ STAGE 3 · TRANSLITERATE — emitted Lean proof (deterministic):\n")
    kw = ":= by" if body.startswith("by\n") else ":="
    print(f"theorem {name} {tail} {kw}")
    print(body[3:] if body.startswith("by\n") else f"  {body}")


def batch_and_verify():
    hdr("STAGE 4 · AUTONOMOUS BATCH + VERIFY GATE  (whole Ch03_bet.v)")
    ledger, emitted, out_path = O.run(COQ, LEAN, "Demo_Ch03")
    clean, errors, _ = O.verify(out_path)
    ok = [n for n, ax in clean if 'sorryAx' not in ax]
    print(f"\n  processed         : {sum(len(v) for v in ledger.values())} lemmas")
    print(f"  transliterated    : {len(ledger['accepted'])}")
    print(f"  ✅ VERIFIED axiom-clean (lake + #print axioms): {len(ok)}")
    print(f"     {ok}")
    print(f"  ⛔ gate-rejected   : {len(ledger['accepted']) - len(ok)}  (bad transliteration caught)")
    print(f"  queued (unsupported/blocked): {len(ledger['unsupported']) + len(ledger['blocked'])}")


if __name__ == "__main__":
    walkthrough(sys.argv[1] if len(sys.argv) > 1 else "l3_17")
    batch_and_verify()
