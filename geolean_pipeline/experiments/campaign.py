"""
Campaign runner — sweep many chapters, measuring how many lemmas the pipeline
produces axiom-clean WITHOUT LLM (deterministic) and (optionally) WITH LLM on the
residue. Every accepted lemma is kernel-verified; nothing is ever `sorry`-filled.

  python geolean_pipeline/campaign.py det          # deterministic sweep only (fast)
  python geolean_pipeline/campaign.py full         # + LLM on residue (slow, hours)
  python geolean_pipeline/campaign.py full Ch02_cong Ch03_bet   # scope to chapters
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import orchestrator as O
from src.oracle import find_all_lemma_names

STUB_CHAPTERS = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
                 "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality",
                 "Ch09_plane", "Ch10_line_reflexivity"]
LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"


def det_pass(ch):
    coq = f"theories/Main/Tarski_dev/{ch}.v"
    lean = f"{LEAN}/{ch}.lean"
    stubs = O.parse_stubs(lean)
    total = len([n for n in find_all_lemma_names(coq) if n in stubs])
    ledger, _, out = O.run(coq, lean, f"Camp_{ch}")
    clean, _errs, _ = O.verify(out)
    det = [n for n, ax in clean if 'sorryAx' not in ax]
    residue = [n for n, _ in ledger["unsupported"]] + [n for n, _ in ledger["blocked"]]
    residue = [n for n in residue if n in stubs and n not in det]
    return total, det, residue


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "det"
    chapters = sys.argv[2:] or STUB_CHAPTERS

    print(f"{'CAMPAIGN — deterministic sweep' if mode=='det' else 'CAMPAIGN — deterministic + LLM'}", flush=True)
    print(f"{'chapter':22s} {'det':>5s} {'/tot':>5s} {'residue':>8s}", flush=True)
    print("-" * 45, flush=True)

    results = {}
    G_tot = G_det = 0
    for ch in chapters:
        total, det, residue = det_pass(ch)
        results[ch] = (total, det, residue)
        G_tot += total
        G_det += len(det)
        print(f"{ch:22s} {len(det):>5d} {'/'+str(total):>5s} {len(residue):>8d}", flush=True)
    print("-" * 45, flush=True)
    print(f"{'TOTAL (no LLM)':22s} {G_det:>5d} {'/'+str(G_tot):>5s}"
          f"   = {100*G_det//max(G_tot,1)}% deterministic, axiom-clean", flush=True)

    if mode != "full":
        return

    # Phase 2 — LLM on the residue, continuous running tally.
    import llm_path as L
    print("\n=== PHASE 2: LLM on residue (kernel-gated) ===", flush=True)
    G_llm = 0
    for ch in chapters:
        total, det, residue = results[ch]
        stubs = O.parse_stubs(f"{LEAN}/{ch}.lean")
        coq = f"theories/Main/Tarski_dev/{ch}.v"
        for n in residue:
            tail, binders = stubs[n]
            try:
                proof, _ = L.llm_translate(coq, n, tail, binders, retries=1)
            except Exception:
                proof = None
            if proof:
                G_llm += 1
            comb = G_det + G_llm
            print(f"[{ch}:{n}] {'✅' if proof else '❌'}  running: det {G_det} + LLM {G_llm} = {comb}/{G_tot} ({100*comb//max(G_tot,1)}%)", flush=True)
    print(f"\n=== FINAL: det {G_det} + LLM {G_llm} = {G_det+G_llm}/{G_tot} = {100*(G_det+G_llm)//max(G_tot,1)}% ===", flush=True)


if __name__ == "__main__":
    main()
