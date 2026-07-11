"""
Climb engine — the scalable version. Processes a chapter in dependency order,
emitting EVERY lemma as `<name>_c`, either a real (deterministic / LLM) proof or a
TRACKED `sorry` hole. Same-chapter lemmas chain (grow-the-pool via LOCAL_SIGS).
`#print axioms` then classifies each:

  clean   : real proof, no sorryAx           (truly done)
  tainted : real proof but depends on a hole (structurally done, waiting on holes)
  hole    : couldn't be produced -> `sorry`  (the debt to grind down)

Nothing is silently `sorry`-filled: holes are explicit, counted, and reported, and
the metric never claims a tainted/hole lemma as clean.

  python geolean_pipeline/climb.py Ch03_bet          # deterministic
  python geolean_pipeline/climb.py Ch03_bet llm      # + LLM on what deterministic misses
"""
import os, sys
REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO, "geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)

import re, subprocess
import translit as T
import orchestrator as O
from src.oracle import run_proof, find_all_lemma_names, default_q_paths, _ensure_known_names

LEAN = "lean/geocoq_translate/GeocoqTranslate/Tarski_dev"
CWD = "lean/geocoq_translate"


def try_det(coq, name, binders):
    """Deterministic transliteration (chains via LOCAL_SIGS). Body or None."""
    try:
        pt = run_proof(coq, name, default_q_paths())
        ast = T.parse_term(T.P(T.tok(pt)), stop={None})
        while ast[0] == "paren":
            ast = ast[1]
        notes = []
        if ast[0] == "fun":
            body = T.emit_body(ast[2], dict(zip(ast[1], binders)), notes)
        else:                                          # S4: top-level term with no lambda
            body = T.emit_body(ast, {}, notes)         # (e.g. bare `ex_intro …` / `let …`)
        if any("UNRESOLVED" in n or "NON-LEMMA" in n or "LEAK" in n for n in notes):
            return None
        return body
    except Exception:
        return None


def write_full(ch, order, stubs, bodies):
    path = f"{LEAN}/Climb_{ch}.lean"
    out = ["import GeocoqTranslate.Tarski_dev.Ch05Bet",
           "import GeocoqTranslate.Tarski_dev.Ch04Cong", "",
           "namespace GeocoqTranslate.Tarski.Base",
           "open Tarski_neutral_dimensionless",
           "open Tarski_neutral_dimensionless_with_decidable_point_equality", "",
           "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]", ""]
    for n in order:
        tail = stubs[n][0]
        b = bodies[n]
        if b is None:
            out.append(f"theorem {n}_c {tail} := sorry")          # TRACKED hole
        elif b.startswith("by\n"):
            out += [f"theorem {n}_c {tail} := by", b[3:]]
        else:
            out += [f"theorem {n}_c {tail} :=", f"  {b}"]
        out.append("")
    for n in order:
        out.append(f"#print axioms GeocoqTranslate.Tarski.Base.{n}_c")
    out.append("end GeocoqTranslate.Tarski.Base")
    open(path, "w").write("\n".join(out))
    return path


def compile_axioms(path):
    rel = path.split("lean/geocoq_translate/")[-1]
    r = subprocess.run(["lake", "env", "lean", rel], cwd=CWD, capture_output=True, text=True, timeout=1800)
    out = r.stdout + r.stderr
    ax = {}
    for m in re.finditer(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)_c' "
                         r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out):
        ax[m.group(1)] = m.group(2) or ""
    return ax


def climb(ch, use_llm=False):
    _ensure_known_names()
    coq = f"theories/Main/Tarski_dev/{ch}.v"
    lean = f"{LEAN}/{ch}.lean"
    stubs = O.parse_stubs(lean)
    order = [n for n in find_all_lemma_names(coq) if n in stubs]

    # grow-the-pool: every chapter lemma's binder kinds, so deps can chain
    T.LOCAL_SIGS = {n: T.lean_binder_kinds(f"theorem {n} {stubs[n][0]}") for n in order}

    bodies = {}
    for n in order:
        tail, binders = stubs[n]
        b = try_det(coq, n, binders)
        if b is None and use_llm:
            import llm_path as L
            try:
                b, _ = L.llm_translate(coq, n, tail, binders, retries=1)
            except Exception:
                b = None
        bodies[n] = b

    # emit + compile; repair: any real body that doesn't compile -> convert to a hole
    for _ in range(4):
        path = write_full(ch, order, stubs, bodies)
        ax = compile_axioms(path)
        errored = [n for n in order if bodies[n] is not None and n not in ax]
        if not errored:
            break
        for n in errored:
            bodies[n] = None                                   # demote wrong proof to a hole

    holes = [n for n in order if bodies[n] is None]
    clean = [n for n in order if bodies[n] is not None and "sorryAx" not in ax.get(n, "sorryAx")]
    tainted = [n for n in order if bodies[n] is not None and "sorryAx" in ax.get(n, "")]
    return dict(total=len(order), clean=clean, tainted=tainted, hole=holes, path=path)


STUB_CHAPTERS = ["Ch02_cong", "Ch03_bet", "Ch04_col", "Ch04_cong_bet", "Ch05_bet_le",
                 "Ch06_out_lines", "Ch07_midpoint", "Ch08_orthogonality",
                 "Ch09_plane", "Ch10_line_reflexivity"]


# ==========================================================================
# S6 — CROSS-CHAPTER chaining. One cumulative file: every lemma of every stub
# chapter, in dependency order, as `<name>_c`. A proof may reference ANY earlier
# lemma (cone OR any prior chapter) natively — they're all defined above in the
# same file, so no cross-file imports / oleans are needed. `sorry` holes are
# tracked; a body that fails to compile is demoted to a hole (error-line mapped).
# ==========================================================================
def write_all(flat, bodies):
    """flat: [(ch, name, tail)] in global dep order. Emit ONE self-contained file.
    Returns (path, {name: 1-indexed start line})."""
    out = ["import GeocoqTranslate.Tarski_dev.Ch05Bet",
           "import GeocoqTranslate.Tarski_dev.Ch04Cong", "",
           "namespace GeocoqTranslate.Tarski.Base",
           "open Tarski_neutral_dimensionless",
           "open Tarski_neutral_dimensionless_with_decidable_point_equality", "",
           "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]", ""]
    start = {}
    for ch, n, tail in flat:
        start[n] = len(out) + 1                                  # 1-indexed line of the header
        b = bodies[n]
        if b is None:
            out.append(f"theorem {n}_c {tail} := sorry")
        elif b.startswith("by\n"):
            out.append(f"theorem {n}_c {tail} := by")
            out += b[3:].split("\n")                             # one list elem PER line (keeps len(out)==#lines)
        else:
            out += [f"theorem {n}_c {tail} :=", f"  {b}"]
        out.append("")
    for ch, n, tail in flat:
        out.append(f"#print axioms GeocoqTranslate.Tarski.Base.{n}_c")
    out.append("end GeocoqTranslate.Tarski.Base")
    path = f"{LEAN}/Climb_All.lean"
    open(path, "w").write("\n".join(out))
    return path, start


def compile_all(path):
    rel = path.split("lean/geocoq_translate/")[-1]
    r = subprocess.run(["lake", "env", "lean", rel], cwd=CWD, capture_output=True, text=True, timeout=5400)
    out = r.stdout + r.stderr
    ax = {}
    for m in re.finditer(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)_c' "
                         r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out):
        ax[m.group(1)] = m.group(2) or ""
    err_lines = [int(m.group(1)) for m in re.finditer(r"Climb_All\.lean:(\d+):\d+: error", out)]
    return ax, err_lines


def theorem_positions(path):
    """Read the WRITTEN file and return sorted [(name_without_c, 1-indexed header line)].
    Robust: uses actual file lines, so it never drifts from the compiler's line refs."""
    pos = []
    for i, l in enumerate(open(path).read().split("\n")):
        m = re.match(r"theorem (\w+)_c\b", l)
        if m:
            pos.append((m.group(1), i + 1))
    pos.sort(key=lambda x: x[1])
    return pos


def owning_theorem(err_line, starts_sorted):
    """The theorem whose header is the greatest start-line <= err_line."""
    import bisect
    lns = [l for _, l in starts_sorted]
    i = bisect.bisect_right(lns, err_line) - 1
    return starts_sorted[i][0] if i >= 0 else None


BODIES_CACHE = os.path.join(REPO, ".climb_bodies.pkl")

def climb_all(use_llm=False, reuse=False):
    import pickle
    _ensure_known_names()
    chapters, all_sigs, flat = [], {}, []
    for ch in STUB_CHAPTERS:
        coq = f"theories/Main/Tarski_dev/{ch}.v"
        stubs = O.parse_stubs(f"{LEAN}/{ch}.lean")
        order = [n for n in find_all_lemma_names(coq) if n in stubs]
        chapters.append((ch, coq, order, stubs))
        for n in order:
            all_sigs[n] = T.lean_binder_kinds(f"theorem {n} {stubs[n][0]}")
            flat.append((ch, n, stubs[n][0]))                    # (ch, name, tail) — deterministic
    T.LOCAL_SIGS = all_sigs                                       # global pool: chain on anything

    if reuse and os.path.exists(BODIES_CACHE):                   # skip the ~8-min oracle re-transliteration
        bodies = pickle.load(open(BODIES_CACHE, "rb"))
        print(f"  [reused {sum(v is not None for v in bodies.values())} cached bodies]", flush=True)
    else:
        bodies = {}
        for ch, coq, order, stubs in chapters:
            for n in order:
                tail, binders = stubs[n]
                b = try_det(coq, n, binders)
                if b is None and use_llm:
                    import llm_path as L
                    try: b, _ = L.llm_translate(coq, n, tail, binders, retries=1)
                    except Exception: b = None
                bodies[n] = b
            det = sum(1 for _, n, _ in flat if bodies.get(n) is not None)
            print(f"  transliterated through {ch}: {det}/{len(flat)} bodies so far", flush=True)
        pickle.dump(bodies, open(BODIES_CACHE, "wb"))

    ax = {}
    for it in range(8):
        path, _ = write_all(flat, bodies)
        ax, err_lines = compile_all(path)
        starts_sorted = theorem_positions(path)                  # map from the ACTUAL file (drift-proof)
        errored = set()
        for e in err_lines:
            nm = owning_theorem(e, starts_sorted)
            if nm is not None and bodies.get(nm) is not None:
                errored.add(nm)
        print(f"  compile pass {it}: {len(err_lines)} error-lines -> demote {len(errored)} bodies", flush=True)
        if not errored:
            break
        for nm in errored:
            bodies[nm] = None

    rows = {}
    for ch, coq, order, stubs in chapters:
        c = t = h = 0
        for n in order:
            if bodies[n] is None: h += 1
            elif "sorryAx" in ax.get(n, "sorryAx"): t += 1
            else: c += 1
        rows[ch] = (c, t, h, len(order))
    return rows, ax, bodies


if __name__ == "__main__":
    arg = sys.argv[1] if len(sys.argv) > 1 else "Ch03_bet"
    use_llm = "llm" in sys.argv
    if arg == "chain":                                   # S6: cross-chapter cumulative sweep
        reuse = "reuse" in sys.argv                       # reuse cached bodies -> just re-run repair/compile
        print(f"CLIMB CHAIN — cross-chapter (deterministic{'+LLM' if use_llm else ''}{', reuse' if reuse else ''})", flush=True)
        rows, ax, bodies = climb_all(use_llm=use_llm, reuse=reuse)
        print(f"\n{'chapter':22s} {'clean':>6s} {'taint':>6s} {'hole':>6s} {'/tot':>6s}", flush=True)
        print("-" * 50, flush=True)
        GC = GTn = GH = GT = 0
        for ch in STUB_CHAPTERS:
            c, t, h, tot = rows[ch]
            GC += c; GTn += t; GH += h; GT += tot
            print(f"{ch:22s} {c:>6d} {t:>6d} {h:>6d} {'/'+str(tot):>6s}", flush=True)
        print("-" * 50, flush=True)
        print(f"{'TOTAL':22s} {GC:>6d} {GTn:>6d} {GH:>6d} {'/'+str(GT):>6s}"
              f"   truly-clean = {100*GC//max(GT,1)}%   holes = {GH}", flush=True)
    elif arg == "all":
        print(f"CLIMB SWEEP (deterministic{'+LLM' if use_llm else ''})", flush=True)
        print(f"{'chapter':22s} {'clean':>6s} {'taint':>6s} {'hole':>6s} {'/tot':>6s}", flush=True)
        print("-" * 50, flush=True)
        GC = GTn = GH = GT = 0
        for ch in STUB_CHAPTERS:
            r = climb(ch, use_llm=use_llm)
            GC += len(r["clean"]); GTn += len(r["tainted"]); GH += len(r["hole"]); GT += r["total"]
            print(f"{ch:22s} {len(r['clean']):>6d} {len(r['tainted']):>6d} {len(r['hole']):>6d} {'/'+str(r['total']):>6s}", flush=True)
        print("-" * 50, flush=True)
        print(f"{'TOTAL':22s} {GC:>6d} {GTn:>6d} {GH:>6d} {'/'+str(GT):>6s}"
              f"   truly-clean = {100*GC//max(GT,1)}%   holes = {GH}", flush=True)
    else:
        r = climb(arg, use_llm=use_llm)
        print(f"\n===== CLIMB {arg}  (deterministic{'+LLM' if use_llm else ''}) =====")
        print(f"  total lemmas   : {r['total']}")
        print(f"  ✅ truly clean  : {len(r['clean'])}")
        print(f"  🟡 tainted      : {len(r['tainted'])}")
        print(f"  ⛳ holes (sorry): {len(r['hole'])}   {r['hole']}")
        print(f"  output: {r['path']}")
