"""
Kernel-gated LLM cascade — ONE round:

  rank holes by Coq proof size
    -> filter: non-reflective, deps currently CLEAN (a tainted/hole dep can only
       yield a tainted fold, so don't waste LLM calls)
    -> llm_translate (mirror-first, free-form fallback; olean-fast kernel verify)
    -> fold each VERIFIED-clean proof into its chapter file (replace `:= sorry`)
    -> one `lake build` at the end (incremental, per-chapter) -> new clean count

Every accepted proof passed `#print axioms` with no sorryAx. The LLM is only a
proposer; the kernel is the judge. Per-lemma cost lands in .llm_ledger.jsonl.

Single round from the CLI:
  python geolean_pipeline/cascade_llm.py [max_lemmas] [max_coq_lines]
Fixpoint loop over rounds: see pipeline.py.
"""
import os, sys, re, glob, subprocess
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import llm_path as L                     # scaffold + claude + olean-fast verify + ledger

# Climb_All.lean is a FROZEN historical snapshot (kept untouched, do not edit).
# Live work now happens on the chapter split: Ch02.lean -> Ch03.lean -> ... ->
# Ch10.lean, each importing the previous. `lake build` is incremental, so editing
# Ch09 only recompiles Ch09+Ch10 — Ch02..08 (already stable) are skipped.
LEAN_PKG = "lean/geocoq_translate"
CHAPTERS = ["Ch02", "Ch03", "Ch04", "Ch05", "Ch06", "Ch07", "Ch08", "Ch09", "Ch10"]
CHAPTER_INDEX = {c: i for i, c in enumerate(CHAPTERS)}
CHAPTER_PATH = {c: f"lean/geocoq_translate/GeocoqTranslate/Tarski_dev/{c}.lean" for c in CHAPTERS}
FINAL_CHAPTER = "Ch10"                                # imports the whole chain
ID = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


# ---------------------------------------------------------------- corpus scan
def hole_blocks():
    """name -> (full_text_span, tail) for every `:= sorry` hole, across ALL
    chapter files.

    Split per theorem block first (a lazy cross-block regex would swallow the
    NEXT theorem's `:= sorry` for non-hole theorems — real bug, caught live)."""
    out = {}
    for c in CHAPTERS:
        src = open(CHAPTER_PATH[c]).read()
        for blk in re.split(r"(?=^theorem \w+_c\b)", src, flags=re.M):
            m = re.match(r"theorem (\w+)_c\b", blk)
            if not m or ":=" not in blk:
                continue
            sig, body = blk.split(":=", 1)
            if body.split("theorem")[0].split("#print")[0].strip() != "sorry":
                continue                              # real proof — not a hole
            span = sig + ":= sorry"
            if span not in src:
                continue
            tail = " ".join(sig.split()[2:])          # drop `theorem <name>_c`
            out[m.group(1)] = (span, tail)
    return out


def _name_file_map():
    """name -> chapter file path, for every DECLARED theorem (hole or proven)."""
    m = {}
    for c in CHAPTERS:
        src = open(CHAPTER_PATH[c]).read()
        for mm in re.finditer(r"^theorem (\w+)_c\b", src, re.M):
            m[mm.group(1)] = CHAPTER_PATH[c]
    return m


def _chapter_of_path(path):
    for c in CHAPTERS:
        if CHAPTER_PATH[c] == path:
            return c
    return None


def coq_index():
    """lemma -> (chapter .v path, proof body text)."""
    d = {}
    for vf in sorted(glob.glob("theories/Main/Tarski_dev/Ch*.v")):
        c = re.sub(r"\(\*.*?\*\)", "", open(vf).read(), flags=re.DOTALL)
        for m in re.finditer(r"(?:Lemma|Theorem|Corollary|Proposition|Remark|Fact)\s+(\w+)\b"
                             r".*?Proof\.(.*?)(?:Qed|Defined|Admitted)\s*\.", c, re.DOTALL):
            d.setdefault(m.group(1), (vf, m.group(2)))
    return d


def clean_set_from(dump_text):
    """Names whose `_c` is currently kernel-CLEAN, from lake-build output text."""
    ok = set()
    for m in re.finditer(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)_c'((?:.(?!'GeocoqTranslate))*)",
                         dump_text, re.S):
        if "sorryAx" not in m.group(2)[:120]:
            ok.add(m.group(1))
    return ok


def rebuild(target=None):
    """lake build the given chapter (default: the final chapter, which imports
    the whole Ch02..Ch10 chain). Lake is incremental — chapters whose source
    didn't change since the last build are skipped, not recompiled.
    Returns (errors, clean, total, dump_text)."""
    mod = f"GeocoqTranslate.Tarski_dev.{target or FINAL_CHAPTER}"
    r = subprocess.run(["lake", "build", mod],
                       cwd=LEAN_PKG, capture_output=True, text=True, timeout=1800)
    out = r.stdout + r.stderr
    errs = out.count("error:")
    seen = {}
    for m in re.finditer(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)'((?:.(?!'GeocoqTranslate))*)",
                         out, re.S):
        seen[m.group(1)] = "sorryAx" not in m.group(2)[:120]
    return errs, sum(seen.values()), len(seen), out


# ------------------------------------------------------------------- folding
def fold(name, span, tail, proof):
    fmap = _name_file_map()
    path = fmap.get(name)
    if path is None:
        print(f"    fold REJECTED: `{name}_c` not declared in any chapter file", flush=True)
        return False
    src = open(path).read()
    if span not in src:
        return False
    # position guard: verify ran against the FULL olean, but the fold lands at the
    # hole's position — every `_c` lemma the proof references must be defined
    # EARLIER in the file (same-file) or in an earlier-imported chapter, else the
    # fold introduces a forward-reference error.
    pos = src.index(span)
    my_ch = _chapter_of_path(path)
    for dep in set(re.findall(r"(\w+)_c(?![\w'])", proof)):
        dep_path = fmap.get(dep)
        if dep_path is None:
            print(f"    fold REJECTED: `{dep}_c` not defined in any chapter file", flush=True)
            return False
        if dep_path == path:
            m = re.search(rf"^theorem {dep}_c\b", src, re.M)
            if m is None or m.start() >= pos:
                print(f"    fold REJECTED: `{dep}_c` not defined before {name}_c (same file)", flush=True)
                return False
        elif CHAPTER_INDEX[_chapter_of_path(dep_path)] > CHAPTER_INDEX[my_ch]:
            print(f"    fold REJECTED: `{dep}_c` is in a LATER chapter than {name}_c", flush=True)
            return False
    kw = ":= by" if proof.lstrip().startswith("by") else ":="
    pbody = proof.lstrip()[2:].lstrip("\n") if proof.lstrip().startswith("by") else "  " + proof
    new = span.replace(":= sorry", f"{kw}\n{pbody}" if kw == ":= by" else f":=\n{pbody}")
    open(path, "w").write(src.replace(span, new, 1))
    return True


# --------------------------------------------------------------------- round
def run_round(dump_text, max_n=40, max_lines=10, colr=False, workers=8, skip=()):
    """One cascade round against the CURRENT olean/dump. Returns a result dict:
    {folded, failed, attempted, errors, clean, total, dump} — `dump` is the fresh
    post-rebuild lake output (or the input dump if nothing folded)."""
    holes = hole_blocks()
    coq = coq_index()
    clean = clean_set_from(dump_text)
    allthm = set(_name_file_map().keys())
    print(f"holes={len(holes)}  clean(now)={len(clean)}", flush=True)

    cands = []
    for h, (span, tail) in holes.items():
        if h in skip or h not in coq:
            continue
        vf, body = coq[h]
        nl = body.strip().count("\n") + 1
        # NB: Ltac `induction H` on a disjunction/conjunction is mere case analysis
        # (rcases), NOT structural recursion. Only true reflection (CongR/ColR)
        # and `fix` are out of the headless LLM's reach; colr=True flips to a
        # ColR-only round with the col-helper hint injected.
        if nl > max_lines or re.search(r"CongR|\bfix\b", body):
            continue
        has_colr = bool(re.search(r"(?<![\w])ColR(?![\w])", body))
        if colr != has_colr:
            continue
        toks = set(ID.findall(body)) & allthm              # referenced ported lemmas
        if any(t != h and t not in clean for t in toks):
            continue
        cands.append((nl, h, vf, span, tail))
    cands.sort()
    cands = cands[:max_n]
    print(f"candidates this run: {[c[1] for c in cands]}", flush=True)
    if not cands:
        return dict(folded=[], failed=[], attempted=[], errors=0,
                    clean=len(clean), total=None, dump=dump_text)

    extra0 = None
    if colr:                     # hand the LLM the helpers Coq's ColR abbreviates
        cs = L._climb_sigs()
        helpers = ["col_transitivity_1", "col_transitivity_2", "col3", "colx",
                   "l6_16_1", "col_permutation_1", "col_permutation_2",
                   "col_permutation_4", "col_permutation_5", "not_col_permutation_1"]
        extra0 = ("Coq's `ColR` tactic = a short collinearity chain. Build it from: "
                  + "; ".join(cs[hn] for hn in helpers if hn in cs))

    def attempt(cand):
        nl, h, vf, span, tail = cand
        binders = re.findall(r"\((\w+)[^)]*?:", tail)       # best-effort binder names
        print(f"--- {h} ({nl}L, {os.path.basename(vf)}) started", flush=True)
        try:
            proof, tries, mode = L.llm_translate(vf, h, tail, binders, retries=2,
                                                 extra0=extra0)
        except Exception as e:
            print(f"    {h}: EXC {str(e)[:120]}", flush=True)
            return (h, None, None, 0)
        print((f"    {h}: CLEAN [{mode}] in {tries} attempt(s)" if proof
               else f"    {h}: no clean proof in {tries} attempts"), flush=True)
        return (h, proof, mode, tries)

    from concurrent.futures import ThreadPoolExecutor
    with ThreadPoolExecutor(max_workers=workers) as ex:
        results = list(ex.map(attempt, cands))

    folded, failed = [], []
    span_by = {h: (span, tail) for _, h, _, span, tail in cands}
    for h, proof, mode, tries in results:
        if proof and fold(h, *span_by[h], proof):
            folded.append(h)
        elif not proof:
            failed.append(h)

    print(f"folded {len(folded)}: {folded}", flush=True)
    if folded:
        print(f"rebuilding ({FINAL_CHAPTER}, incremental) ...", flush=True)
        errs, cl, tot, dump_text = rebuild()
        print(f"rebuild: errors={errs}  clean={cl}/{tot}", flush=True)
        return dict(folded=folded, failed=failed, attempted=[c[1] for c in cands],
                    errors=errs, clean=cl, total=tot, dump=dump_text)
    return dict(folded=[], failed=failed, attempted=[c[1] for c in cands],
                errors=0, clean=len(clean), total=None, dump=dump_text)


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    max_lines = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    dump_path = os.environ.get("AXIOMS_DUMP")
    if dump_path and os.path.exists(dump_path):
        dump_text = open(dump_path).read()
    else:
        print("no AXIOMS_DUMP — building baseline ...", flush=True)
        errs, cl, tot, dump_text = rebuild()
        print(f"baseline: errors={errs}  clean={cl}/{tot}", flush=True)
    run_round(dump_text, max_n=max_n, max_lines=max_lines,
              colr=bool(os.environ.get("COLR")),
              workers=int(os.environ.get("CASCADE_WORKERS", "8")))


if __name__ == "__main__":
    main()
