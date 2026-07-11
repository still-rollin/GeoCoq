"""
Measurement harness for the thesis plot (prof suggestion, 2026-07-08).

Joins two data sources per lemma and reports the quantitative story behind the
"minimal, kernel-gated LLM" claim:

  1. DETERMINISTIC layer  — solve-rate vs proof-term size (the 93%->2% curve),
     read from the live Climb_All.lean (clean / tainted / hole) + oracle metrics.
  2. LLM layer            — added coverage vs cost, read from .llm_ledger.jsonl
     (per-lemma attempts, in/out tokens, wallclock, mirror-vs-freeform mode).

Output: a size-bucket table with det solve-rate AND, overlaid, how many of the
remaining holes the LLM closed and at what token cost.

  python geolean_pipeline/measure.py
"""
import os, sys, re, json, collections
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import translit as T
import orchestrator as O
from src.oracle import run_proof, find_all_lemma_names, default_q_paths, _ensure_known_names

LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"
CHAPTER_MODS = ["Ch02", "Ch03", "Ch04", "Ch05", "Ch06", "Ch07", "Ch08", "Ch09", "Ch10"]
CHAPTER_PATHS = [f"{LEAN}/{c}.lean" for c in CHAPTER_MODS]
LEDGER = os.path.join(REPO, "geolean_pipeline", ".llm_ledger.jsonl")
STUB_CHAPTERS = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
                 "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality",
                 "Ch09_plane", "Ch10_line_reflexivity"]
BUCKETS = [(0, 40), (40, 100), (100, 250), (250, 600), (600, 10**9)]


AXIOMS_DUMP = os.environ.get("AXIOMS_DUMP", "")   # optional path to a `lake build` log


def climb_status():
    """name -> 'clean' | 'tainted' | 'hole'.

    Holes are read multi-line-aware across the chapter split Ch02..Ch10 (a hole =
    a theorem whose body is exactly `sorry`). Clean-vs-tainted needs the kernel
    verdict: parse a `#print axioms` dump (AXIOMS_DUMP env, else run `lake build`
    on the final chapter, which transitively pulls in the whole chain)."""
    holes = set()
    allthm = set()
    for p_path in CHAPTER_PATHS:
        src = open(p_path).read()
        allthm |= set(re.findall(r"theorem (\w+)_c\b", src))
        for p in re.split(r"(?=^theorem \w+_c\b)", src, flags=re.M):
            m = re.match(r"theorem (\w+)_c\b", p)
            if m and ":=" in p:
                body = p.split(":=", 1)[1].split("theorem")[0].split("#print")[0].strip()
                if body[:6].strip() == "sorry":
                    holes.add(m.group(1))

    # kernel verdict per lemma from a #print axioms dump
    dump = ""
    if AXIOMS_DUMP and os.path.exists(AXIOMS_DUMP):
        dump = open(AXIOMS_DUMP).read()
    else:
        import subprocess
        r = subprocess.run(["lake", "build", f"GeocoqTranslate.Tarski_dev.{CHAPTER_MODS[-1]}"],
                           cwd="lean/geocoq_translate", capture_output=True, text=True, timeout=1800)
        dump = r.stdout + r.stderr
    tainted = set()
    for blk in re.split(r"(?=(?:info: )?'GeocoqTranslate)", dump):
        mm = re.match(r"(?:info: )?'GeocoqTranslate\.Tarski\.Base\.(\w+)_c'", blk)
        if mm and "sorryAx" in blk:
            tainted.add(mm.group(1))

    out = {}
    for n in allthm:
        out[n] = "hole" if n in holes else ("tainted" if n in tainted else "clean")
    return out


def ptoks_of(coq, n):
    try:
        return len(T.tok(run_proof(coq, n, default_q_paths())))
    except Exception:
        return None


def main():
    _ensure_known_names()
    status = climb_status()
    rows = []                                    # (name, ptoks, det_status)
    for ch in STUB_CHAPTERS:
        coq = f"theories/Main/Tarski_dev/{ch}.v"
        stubs = O.parse_stubs(f"{LEAN}/{ch}.lean")
        for n in [x for x in find_all_lemma_names(coq) if x in stubs]:
            rows.append((n, ptoks_of(coq, n), status.get(n, "hole")))
        print(f"  scanned {ch}", flush=True)

    # LLM ledger (may be absent / partial)
    led = {}
    if os.path.exists(LEDGER):
        for line in open(LEDGER):
            try:
                r = json.loads(line); led[r["name"]] = r      # last record wins
            except Exception:
                pass

    print("\n" + "=" * 72)
    print("DETERMINISTIC solve-rate by proof-term size, + LLM overlay on the residue")
    print(f"{'size (tok)':>12s} {'lemmas':>7s} {'det-solved':>11s} {'rate':>6s} "
          f"{'llm-closed':>11s} {'out-tok/lemma':>13s}")
    tot_det = tot_llm = tot_out = 0
    for lo, hi in BUCKETS:
        insize = [(n, p) for (n, p, s) in rows if p is not None and lo <= p < hi]
        det = [(n, p) for (n, p, s) in rows if p is not None and lo <= p < hi and s == "clean"]
        llm = [led[n] for (n, p) in insize if led.get(n, {}).get("outcome") == "clean"]
        outt = sum(r["out_tok"] for r in llm)
        tot_det += len(det); tot_llm += len(llm); tot_out += outt
        lbl = f"{lo}-{hi if hi < 10**8 else 'inf'}"
        rate = f"{100*len(det)//max(len(insize),1)}%"
        avg = f"{outt//max(len(llm),1)}" if llm else "-"
        print(f"{lbl:>12s} {len(insize):>7d} {len(det):>11d} {rate:>6s} "
              f"{len(llm):>11d} {avg:>13s}")
    print("-" * 72)
    print(f"{'TOTAL':>12s} {len(rows):>7d} {tot_det:>11d} "
          f"{100*tot_det//max(len(rows),1)}%  {tot_llm:>11d} "
          f"{'tot '+str(tot_out)+'tok':>13s}")

    if led:
        clean = [r for r in led.values() if r["outcome"] == "clean"]
        mir = sum(1 for r in clean if r["mode"] == "mirror-faithful")
        ff = sum(1 for r in clean if r["mode"] == "freeform")
        print("\nLLM ledger summary:")
        print(f"  attempted={len(led)}  clean={len(clean)}  "
              f"(mirror-faithful={mir}, freeform={ff})  fail={len(led)-len(clean)}")
        if clean:
            print(f"  avg attempts={sum(r['attempts'] for r in clean)/len(clean):.1f}  "
                  f"avg out-tok={sum(r['out_tok'] for r in clean)//len(clean)}  "
                  f"total out-tok={sum(r['out_tok'] for r in led.values())}")
    else:
        print("\n(no LLM ledger yet — run llm_path on the residue to populate "
              ".llm_ledger.jsonl; det column is the current baseline)")


if __name__ == "__main__":
    main()
