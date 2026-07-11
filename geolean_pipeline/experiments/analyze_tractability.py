"""
Why does the deterministic pipeline solve the 25% it solves? For every stub-chapter
lemma, measure (a) the deterministic OUTCOME + reason, and (b) structural metrics of
the Coq proof term. Then compare the distributions: what do the SOLVED proofs have in
common, and what specifically blocks the rest.

  python geolean_pipeline/analyze_tractability.py
"""
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
STUB_CHAPTERS = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
                 "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality",
                 "Ch09_plane", "Ch10_line_reflexivity"]


def metrics(pt):
    toks = T.tok(pt)
    deps = {t for t in toks if t in T.KNOWN_LEMMAS}
    return dict(
        tokens=len(toks),
        ndeps=len(deps),
        match=toks.count("match"),
        fix=toks.count("fix") + toks.count("cofix"),
        eqind=sum(1 for t in toks if t == "eq_ind"),          # eq_ind (NOT eq_ind_r)
        casesplit=toks.count("or_ind") + toks.count("match"),
        nfun=toks.count("fun"),
    )


def outcome(ch, coq, n, binders):
    """Return (bucket, reason, metrics)."""
    try:
        pt = run_proof(coq, n, default_q_paths())
    except Exception:
        return "HOLE", "oracle_fail", None
    if not pt or not pt.strip():
        return "HOLE", "oracle_fail", None
    m = metrics(pt)
    try:
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren": ast = ast[1]
    except Exception:
        return "HOLE", "parse_throw", m
    notes = []
    try:
        if ast[0] == "fun":
            T.emit_body(ast[2], dict(zip(ast[1], binders)), notes)
        else:
            T.emit_body(ast, {}, notes)
    except Exception:
        return "HOLE", "emit_throw", m
    j = "\n".join(notes)
    if "unsupported" in j:            return "HOLE", "fix_unsupported", m
    if "LEAK" in j:                   return "HOLE", "leak(match/prop/token)", m
    if "UNRESOLVED head" in j:        return "HOLE", "unresolved_dep", m
    if "UNRESOLVED" in j:             return "HOLE", "unresolved_other", m
    if "NON-LEMMA" in j:              return "HOLE", "non_lemma", m
    return "BODY", "ok", m            # produced a real body (clean or elab-fail downstream)


def main():
    _ensure_known_names()
    # which theorems ended as holes / real bodies in the final Climb_All.lean
    climb = open(f"{LEAN}/Climb_All.lean").read()
    file_holes = set(re.findall(r"theorem (\w+)_c .*:= sorry", climb))

    T.LOCAL_SIGS = {}
    chapters = []
    for ch in STUB_CHAPTERS:
        coq = f"theories/Main/Tarski_dev/{ch}.v"
        stubs = O.parse_stubs(f"{LEAN}/{ch}.lean")
        order = [n for n in find_all_lemma_names(coq) if n in stubs]
        chapters.append((ch, coq, order, stubs))
        for n in order:
            T.LOCAL_SIGS[n] = T.lean_binder_kinds(f"theorem {n} {stubs[n][0]}")

    rows = []   # (name, final_bucket, reason, metrics)
    reason_ctr = collections.Counter()
    for ch, coq, order, stubs in chapters:
        for n in order:
            tail, binders = stubs[n]
            bucket, reason, m = outcome(ch, coq, n, binders)
            if bucket == "BODY":
                # real body was emitted; did it survive the kernel or get demoted?
                final = "elab_fail" if n in file_holes else "solved_body"
            else:
                final = "hole"
            rows.append((n, bucket, reason, final, m))
            key = reason if bucket == "HOLE" else ("elab_fail" if final == "elab_fail" else "solved_body")
            reason_ctr[key] += 1
        print(f"  done {ch}", flush=True)

    # ---- report ----
    print("\n" + "=" * 64)
    print("OUTCOME / HOLE-REASON breakdown (all 511):")
    for k, v in reason_ctr.most_common():
        print(f"  {k:26s} {v:4d}  ({100*v//len(rows)}%)")

    def stats(pred):
        ms = [m for (_, _, _, _, m) in rows if m and pred(_, _)]
        return ms
    solved = [m for (n, b, r, f, m) in rows if f == "solved_body" and m]
    holes = [m for (n, b, r, f, m) in rows if f in ("hole", "elab_fail") and m]

    def avg(ms, k): return sum(x[k] for x in ms) / max(len(ms), 1)
    def med(ms, k):
        v = sorted(x[k] for x in ms); return v[len(v)//2] if v else 0
    def pct(ms, k): return 100 * sum(1 for x in ms if x[k] > 0) // max(len(ms), 1)

    print("\n" + "=" * 64)
    print(f"STRUCTURAL METRICS  (solved n={len(solved)}  vs  hole n={len(holes)})")
    print(f"{'metric':22s} {'SOLVED':>10s} {'HOLE':>10s}")
    for k in ["tokens", "ndeps", "casesplit", "nfun"]:
        print(f"  median {k:15s} {med(solved,k):>10d} {med(holes,k):>10d}")
    print(f"  % using match          {pct(solved,'match'):>9d}% {pct(holes,'match'):>9d}%")
    print(f"  % using fix            {pct(solved,'fix'):>9d}% {pct(holes,'fix'):>9d}%")
    print(f"  % using eq_ind         {pct(solved,'eqind'):>9d}% {pct(holes,'eqind'):>9d}%")

    # proof-size buckets: solve-rate by size
    print("\n" + "=" * 64)
    print("SOLVE-RATE by proof-term size (tokens):")
    buckets = [(0, 40), (40, 100), (100, 250), (250, 600), (600, 10**9)]
    for lo, hi in buckets:
        insize = [(f) for (n, b, r, f, m) in rows if m and lo <= m["tokens"] < hi]
        tot = len(insize); sol = sum(1 for f in insize if f == "solved_body")
        print(f"  {lo:>4d}-{hi if hi<10**8 else '∞':<4} tokens : {sol:3d}/{tot:3d} solved ({100*sol//max(tot,1)}%)")


if __name__ == "__main__":
    main()
