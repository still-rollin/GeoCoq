"""
Measure the REAL combined yield on one chapter: deterministic transliterator +
LLM path on the residue, each kernel-verified. Prints one line per residue
lemma as it finishes.  Usage: python geolean_pipeline/measure_a3.py [Chapter]
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import llm_path as L
import orchestrator as O
from src.oracle import find_all_lemma_names

ch = sys.argv[1] if len(sys.argv) > 1 else "Ch03_bet"
coq = f"theories/Main/Tarski_dev/{ch}.v"
lean = f"lean/geocoq_translate/GeocoqTranslate/Tarski_dev/{ch}.lean"

stubs = O.parse_stubs(lean)
total = len([n for n in find_all_lemma_names(coq) if n in stubs])
ledger, _, _ = O.run(coq, lean, "Discard")
det = list(ledger["accepted"])
residue = [n for n, _ in ledger["unsupported"]] + [n for n, _ in ledger["blocked"]]
residue = [n for n in residue if n in stubs]

print(f"CHAPTER {ch}: {total} lemmas (with stubs)", flush=True)
print(f"  deterministic (no LLM): {len(det)}", flush=True)
print(f"  residue to try with LLM: {len(residue)}\n", flush=True)

recovered = []
for i, n in enumerate(residue, 1):
    tail, binders = stubs[n]
    try:
        proof, tries = L.llm_translate(coq, n, tail, binders, retries=2)
    except Exception as e:
        proof, tries = None, f"err:{str(e)[:30]}"
    if proof:
        recovered.append(n)
        print(f"[{i}/{len(residue)}] ✅ {n}  (clean in {tries} attempt(s))", flush=True)
    else:
        print(f"[{i}/{len(residue)}] ❌ {n}  (no clean proof, {tries})", flush=True)

tot = len(det) + len(recovered)
print(f"\n{'='*56}", flush=True)
print(f"COMBINED {ch}:  deterministic {len(det)} + LLM {len(recovered)} = {tot}/{total}"
      f"  = {100*tot//max(total,1)}%", flush=True)
print(f"  (LLM recovered {len(recovered)}/{len(residue)} of the residue)", flush=True)
