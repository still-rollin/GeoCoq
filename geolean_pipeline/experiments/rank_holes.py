"""
Rank the current `:= sorry` holes in Climb_All.lean by how cheap they are to
hand-port, so the deterministic cascade targets the easiest wins first.

For each hole it reports the Coq proof's line-count and whether the proof uses
reflective/inductive machinery (CongR/ColR/fix/induction) — those are LLM
territory, not cheap hand-ports. Optionally pass an axioms dump (a `lake build`
log) as argv[1] to also flag which holes' Coq dependencies are already CLEAN vs
TAINTED — a tainted dep means the fold would only be tainted, so skip it.

  python geolean_pipeline/rank_holes.py [path/to/lake-build.log]
"""
import os, re, sys, glob
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CLIMB = f"{REPO}/lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Climb_All.lean"


def holes():
    src = open(CLIMB).read()
    out = []
    for p in re.split(r"(?=^theorem \w+_c\b)", src, flags=re.M):
        m = re.match(r"theorem (\w+)_c\b", p)
        if m and ":=" in p:
            body = p.split(":=", 1)[1].split("theorem")[0].split("#print")[0].strip()
            if body[:6].strip() == "sorry":
                out.append(m.group(1))
    return out


def coq_proofs():
    d = {}
    for vf in glob.glob(f"{REPO}/theories/Main/Tarski_dev/Ch*.v"):
        c = re.sub(r"\(\*.*?\*\)", "", open(vf).read(), flags=re.DOTALL)
        for m in re.finditer(r"(?:Lemma|Theorem|Corollary|Proposition|Remark|Fact)\s+(\w+)\b"
                             r".*?Proof\.(.*?)(?:Qed|Defined|Admitted)\s*\.", c, re.DOTALL):
            if m.group(1) not in d:
                b = m.group(2)
                d[m.group(1)] = (os.path.basename(vf), b.strip().count("\n") + 1,
                                 bool(re.search(r"CongR|ColR|induction|\bfix\b", b)))
    return d


def main():
    hs = holes()
    proofs = coq_proofs()
    print(f"HOLES = {len(hs)}")
    rows = []
    for h in hs:
        f, nl, refl = proofs.get(h, ("?", 999, False))
        rows.append((nl, h, f, refl))
    rows.sort()
    cheap = [r for r in rows if not r[3] and r[2] != "?" and r[0] <= 8]
    print(f"cheap non-reflective (<=8 Coq lines): {len(cheap)}\n")
    for nl, h, f, refl in cheap:
        print(f"  {nl:2d}L  {h:34s} {f}")
    hard = [r for r in rows if r[3]]
    if hard:
        print(f"\nreflective/inductive (LLM territory): {len(hard)}")
        for nl, h, f, refl in hard[:15]:
            print(f"  {nl:2d}L  {h:34s} {f}")


if __name__ == "__main__":
    main()
