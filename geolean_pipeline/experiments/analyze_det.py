"""
Failure analysis of the DETERMINISTIC path. For every stub-chapter lemma, run the
oracle -> parse -> emit pipeline exactly as `climb.try_det` does (same-chapter pool
populated), and record WHERE and HOW it fails. Categories:

  EMIT_OK     : deterministic produced a body (compile is a separate gate)
  ORACLE_FAIL : oracle couldn't produce a proof term
  STRUCTURAL  : proof term uses `match`/`fix` (parser fundamentally lacks these)
  PARSE_FAIL  : parser threw on some other construct
  NOT_FUN     : top-level term isn't `fun …` (e.g. a bare constructor/eq_refl)
  UNRESOLVED  : parsed, but a head couldn't be resolved -> subclassified:
                  builtin   (eq_refl/proj1/False_ind/… -> mappable, cheap win)
                  crosschap (a known GeoCoq lemma from another chapter -> needs pool)
                  defn/other(not a known lemma -> a definition/notation)
  NON_LEMMA   : application head is not a variable (raw match/constructor)

Usage: python geolean_pipeline/analyze_det.py [Ch03_bet ...]   (default: all 10)
"""
import os, sys, time
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import re, collections
import translit as T
import orchestrator as O
from src.oracle import (run_proof, find_all_lemma_names, default_q_paths,
                        collect_geocoq_lemma_names, _ensure_known_names)

LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"
STUB_CHAPTERS = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
                 "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality",
                 "Ch09_plane", "Ch10_line_reflexivity"]

KNOWN = collect_geocoq_lemma_names(os.path.join(os.getcwd(), "theories"))
STRUCT_KW = {"match", "fix", "cofix", "end", "with", "return", "as", "if", "then",
             "else", "Prop", "Type", "Set", "forall", "SooOo"}
# Coq stdlib primitives that HAVE a clean Lean image (cheap deterministic wins):
BUILTIN = {"eq_refl", "eq_sym", "eq_trans", "eq_ind", "eq_rect", "f_equal", "f_equal2",
           "proj1", "proj2", "False_ind", "False_rect", "False_rec", "absurd", "not",
           "iff", "iff_refl", "iff_sym", "iff_trans", "id", "eq_sind", "conj",
           "or_introl", "or_intror", "ex_intro", "and_ind", "or_ind", "ex_ind",
           "eq_ind_r", "eq_rec_r", "and_rec", "or_rec", "sumbool_rec", "sig",
           "proj1_sig", "proj2_sig", "iff_and", "and_comm", "or_comm"}

UNRES = re.compile(r"UNRESOLVED head: (\S+)")


def analyze_chapter(ch, agg, dep_ctr, badtok_ctr, examples, emit_exc_ctr):
    coq = f"theories/Main/Tarski_dev/{ch}.v"
    lean = f"{LEAN}/{ch}.lean"
    stubs = O.parse_stubs(lean)
    order = [n for n in find_all_lemma_names(coq) if n in stubs]
    chap_names = set(find_all_lemma_names(coq))
    # replicate climb: same-chapter pool available so same-chapter deps resolve to _c
    T.LOCAL_SIGS = {n: T.lean_binder_kinds(f"theorem {n} {stubs[n][0]}") for n in order}

    local = collections.Counter()
    for n in order:
        tail, binders = stubs[n]
        try:
            pt = run_proof(coq, n, default_q_paths())
        except Exception as e:
            local["ORACLE_FAIL"] += 1; agg["ORACLE_FAIL"] += 1; continue
        if not pt or not pt.strip():
            local["ORACLE_FAIL"] += 1; agg["ORACLE_FAIL"] += 1; continue

        toks = set(T.tok(pt))
        structural = bool(toks & {"match", "fix", "cofix"})
        try:
            ast = T.parse_term(T.P(T.tok(pt)), stop={None})
            while ast[0] == "paren": ast = ast[1]
        except Exception as e:
            cat = "STRUCTURAL" if structural else "PARSE_FAIL"
            local[cat] += 1; agg[cat] += 1
            if cat == "PARSE_FAIL" and len(examples["PARSE_FAIL"]) < 8:
                examples["PARSE_FAIL"].append((ch, n, str(e)[:60]))
            continue
        if structural:
            local["STRUCTURAL"] += 1; agg["STRUCTURAL"] += 1
            if len(examples["STRUCTURAL"]) < 8:
                examples["STRUCTURAL"].append((ch, n, "match" if "match" in toks else "fix"))
            continue
        if ast[0] != "fun":
            local["NOT_FUN"] += 1; agg["NOT_FUN"] += 1
            if len(examples["NOT_FUN"]) < 8:
                examples["NOT_FUN"].append((ch, n, ast[0]))
            continue

        notes = []
        try:
            T.emit_body(ast[2], dict(zip(ast[1], binders)), notes)
        except Exception as e:
            local["EMIT_EXC"] += 1; agg["EMIT_EXC"] += 1
            msg = f"{type(e).__name__}: {str(e)[:70]}"
            emit_exc_ctr[msg.split(':')[0] + ('|ValueError-node' if 'ValueError' in msg else '')] += 1
            if len(examples["EMIT_EXC"]) < 12:
                examples["EMIT_EXC"].append((ch, n, msg))
            continue
        unres = UNRES.findall("\n".join(notes))
        nonlemma = any("NON-LEMMA" in x for x in notes)
        if unres:
            local["UNRESOLVED"] += 1; agg["UNRESOLVED"] += 1
            for h in unres:
                base = h.split(".")[0]
                if base in STRUCT_KW: dep_ctr["structural-kw"][h] += 1
                elif base in BUILTIN: dep_ctr["builtin"][h] += 1
                elif base in chap_names: dep_ctr["same-chapter"][h] += 1
                elif base in KNOWN: dep_ctr["cross-chapter"][h] += 1
                else: dep_ctr["defn/other"][h] += 1
        elif nonlemma:
            local["NON_LEMMA"] += 1; agg["NON_LEMMA"] += 1
        else:
            local["EMIT_OK"] += 1; agg["EMIT_OK"] += 1
    return len(order), local


def main():
    _ensure_known_names()
    chapters = sys.argv[1:] or STUB_CHAPTERS
    agg = collections.Counter()
    dep_ctr = {k: collections.Counter() for k in
               ["builtin", "same-chapter", "cross-chapter", "structural-kw", "defn/other"]}
    badtok_ctr = collections.Counter()
    emit_exc_ctr = collections.Counter()
    examples = {"PARSE_FAIL": [], "STRUCTURAL": [], "NOT_FUN": [], "EMIT_EXC": []}
    print(f"{'chapter':22s} {'tot':>4s}  breakdown", flush=True)
    print("-" * 70, flush=True)
    GT = 0
    for ch in chapters:
        t0 = time.time()
        tot, local = analyze_chapter(ch, agg, dep_ctr, badtok_ctr, examples, emit_exc_ctr)
        GT += tot
        brk = "  ".join(f"{k}={v}" for k, v in sorted(local.items(), key=lambda x: -x[1]))
        print(f"{ch:22s} {tot:>4d}  {brk}   ({time.time()-t0:.0f}s)", flush=True)

    print("\n" + "=" * 70, flush=True)
    print(f"AGGREGATE over {GT} lemmas:", flush=True)
    for k, v in agg.most_common():
        print(f"  {k:14s} {v:4d}  ({100*v//max(GT,1)}%)", flush=True)

    print("\n--- UNRESOLVED dep breakdown (what specific heads block us) ---", flush=True)
    for cls, ctr in dep_ctr.items():
        tot = sum(ctr.values())
        if not tot: continue
        top = "  ".join(f"{name}×{c}" for name, c in ctr.most_common(12))
        print(f"\n[{cls}]  total occurrences={tot}, distinct={len(ctr)}", flush=True)
        print(f"    {top}", flush=True)

    if emit_exc_ctr:
        print("\n--- EMIT_EXC exception types ---", flush=True)
        for k, v in emit_exc_ctr.most_common():
            print(f"  {k:24s} {v}", flush=True)

    print("\n--- examples ---", flush=True)
    for cat, exs in examples.items():
        if exs:
            print(f"  {cat}:", flush=True)
            for ch, n, info in exs:
                print(f"     {ch}:{n}  -> {info}", flush=True)


if __name__ == "__main__":
    main()
