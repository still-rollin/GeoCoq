"""
One-shot fixpoint pipeline over the kernel-gated LLM cascade.

  python geolean_pipeline/pipeline.py            # run to fixpoint
  python geolean_pipeline/pipeline.py --colr     # include a ColR pass per ladder sweep

Replaces the manual between-rounds glue (fresh dump paths, max_lines choices,
relaunches) with a single driver:

  1. baseline `lake build` -> dump + clean count (no env plumbing)
  2. LADDER over max_lines (10 -> 20 -> 40 -> 60): at each level run rounds
     until that level folds nothing, then climb; any fold RESTARTS the ladder
     from the bottom (a foundational fold reopens cheaper pools via flips)
  3. HARD-LIST: a lemma that accumulates >= 6 failed attempts is skipped for
     good (.llm_hard.json) — it is escalation-tier work, not more tokens
  4. stop at fixpoint: one full ladder sweep with zero folds
  5. final report: count trajectory, folds, hard-list, ledger cost

Every fold is still kernel-gated + position-guarded; the final state always
compiles with zero errors (invariant unchanged).
"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cascade_llm as C

HARD = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".llm_hard.json")
LADDER = [10, 20, 40, 60]
MAX_ATTEMPTS = 6                      # 2 full rounds of 3 -> escalation tier


def load_hard():
    try:
        return json.load(open(HARD))
    except Exception:
        return {}


def save_hard(d):
    json.dump(d, open(HARD, "w"), indent=1)


def main():
    colr_pass = "--colr" in sys.argv
    hard = load_hard()

    print("=== baseline build ===", flush=True)
    errs, cl, tot, dump = C.rebuild()
    print(f"baseline: errors={errs}  clean={cl}/{tot}", flush=True)
    if errs:
        print("ABORT: baseline has errors — fix before running the pipeline", flush=True)
        return
    trajectory, all_folded, rounds = [cl], [], 0

    while True:
        sweep_folds = 0
        for lvl in LADDER:
            while True:
                rounds += 1
                skip = {h for h, n in hard.items() if n >= MAX_ATTEMPTS}
                print(f"\n=== round {rounds} (max_lines={lvl}, skip={len(skip)}) ===", flush=True)
                res = C.run_round(dump, max_n=40, max_lines=lvl, colr=False,
                                  workers=int(os.environ.get("CASCADE_WORKERS", "8")),
                                  skip=skip)
                for h in res["failed"]:
                    hard[h] = hard.get(h, 0) + 3
                save_hard(hard)
                dump = res["dump"]
                if res["errors"]:
                    print("ABORT: rebuild errors — inspect before continuing", flush=True)
                    return
                if res["folded"]:
                    sweep_folds += len(res["folded"])
                    all_folded += res["folded"]
                    trajectory.append(res["clean"])
                    break                      # fold -> restart ladder from bottom
                if not res["attempted"]:
                    break                      # empty pool at this level -> climb
                break                          # attempts but no folds -> climb
            if sweep_folds:
                break                          # restart ladder from the bottom
        else:
            # full ladder, no folds anywhere -> optional ColR pass, else fixpoint
            if colr_pass:
                rounds += 1
                skip = {h for h, n in hard.items() if n >= MAX_ATTEMPTS}
                print(f"\n=== round {rounds} (ColR pass, skip={len(skip)}) ===", flush=True)
                res = C.run_round(dump, max_n=40, max_lines=60, colr=True,
                                  skip=skip)
                for h in res["failed"]:
                    hard[h] = hard.get(h, 0) + 3
                save_hard(hard)
                dump = res["dump"]
                if res["folded"]:
                    all_folded += res["folded"]
                    trajectory.append(res["clean"])
                    continue                   # flips may have reopened pools
            break                              # FIXPOINT
        if not sweep_folds:
            break

    print("\n" + "=" * 60, flush=True)
    print(f"FIXPOINT after {rounds} rounds", flush=True)
    print(f"clean trajectory: {' -> '.join(map(str, trajectory))}", flush=True)
    print(f"folded ({len(all_folded)}): {all_folded}", flush=True)
    esc = sorted(h for h, n in hard.items() if n >= MAX_ATTEMPTS)
    print(f"escalation list ({len(esc)}): {esc}", flush=True)


if __name__ == "__main__":
    main()
