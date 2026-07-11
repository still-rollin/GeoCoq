"""Count the SPECIFIC blocking reason for every current hole, so we know which
deterministic lever is worth adding next. Prints the top UNRESOLVED heads etc."""
import os, sys, re, collections
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import translit as T
import orchestrator as O
from src.oracle import run_proof, find_all_lemma_names, default_q_paths, _ensure_known_names

LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"
STUB = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
        "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality", "Ch09_plane", "Ch10_line_reflexivity"]


def main():
    _ensure_known_names()
    T.LOCAL_SIGS = {}
    chapters = []
    for ch in STUB:
        coq = f"theories/Main/Tarski_dev/{ch}.v"
        stubs = O.parse_stubs(f"{LEAN}/{ch}.lean")
        order = [n for n in find_all_lemma_names(coq) if n in stubs]
        chapters.append((ch, coq, order, stubs))
        for n in order:
            T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n} {stubs[n][0]}")

    kind = collections.Counter()
    heads = collections.Counter()
    for ch, coq, order, stubs in chapters:
        for n in order:
            tail, binders = stubs[n]
            try:
                pt = run_proof(coq, n, default_q_paths())
            except Exception:
                kind["oracle_fail"] += 1; continue
            try:
                ast = T.parse_term(T.P(T.tok(pt)), stop={None})
                while ast[0] == "paren": ast = ast[1]
            except Exception:
                kind["parse_throw"] += 1; continue
            notes = []
            try:
                if ast[0] == "fun":
                    T.emit_body(ast[2], dict(zip(ast[1], binders)), notes)
                else:
                    T.emit_body(ast, {}, notes)
            except Exception:
                kind["emit_throw"] += 1; continue
            rej = [x for x in notes if "UNRESOLVED" in x or "LEAK" in x or "NON-LEMMA" in x]
            if not rej:
                kind["BODY(solved)"] += 1; continue
            r = rej[0]
            if "unsupported" in r: kind["fix_unsupported"] += 1
            elif "LEAK" in r: kind["leak"] += 1
            elif "match in term" in r: kind["match_term"] += 1
            elif "NON-LEMMA" in r: kind["non_lemma"] += 1
            elif "UNRESOLVED head" in r:
                kind["unresolved_head"] += 1
                m = re.search(r"UNRESOLVED head: (\S+)", r)
                if m: heads[m.group(1)] += 1
            else:
                kind["unresolved_other"] += 1
        print(f"  {ch} done", flush=True)

    print("\nKIND breakdown:")
    for k, v in kind.most_common():
        print(f"  {k:20s} {v}")
    print("\nTop UNRESOLVED heads (candidate levers):")
    for h, v in heads.most_common(20):
        print(f"  {h:28s} {v}")


if __name__ == "__main__":
    main()
