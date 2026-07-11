# Tarski_dev port status

Honest, current status of the `Tarski_dev` port (Ch02–Ch16b). Unlike
`Elements/OriginalProofs` (see `GEOLEAN.md`), this corpus is written in a
goal-directed, backward-`apply`/`eapply` idiom that a line-for-line tactic
transpiler cannot reproduce. The approach here is different: extract Coq's own
**elaborated proof term** (`Show Proof`, via SerAPI) for each lemma and
deterministically transliterate that term into Lean 4 syntax
(`geolean_pipeline/translit.py` + `climb_upper.py`). See
`docs/tarski_architecture.md` for the full design.

"Clean" below always means kernel-verified: `lake env lean` + `#print axioms`
shows no `sorryAx` — not just "no literal `sorry` token in the file". "Tainted"
means the proof itself is real and compiles, but currently depends (directly or
transitively) on something still `sorry` elsewhere; tainted lemmas convert to
clean automatically, with no further work on the lemma itself, once whatever
they depend on gets proven.

## Ch02–Ch10 — foundations, complete

**538/538 lemmas, 0 `sorry`, 0 `sorryAx`, clean rebuild confirmed 2026-07-11.**
Congruence, betweenness, collinearity, orthogonality, and reflection — the base
every later chapter imports. A read-only copy is in `proven/tarski_ch02_10/`
(see `proven/README.md` for the exact per-file breakdown and reproduction
commands).

## Bridge files (gap-filling between Ch10 and Ch11)

Two small files close gaps the original chapter boundaries left uncovered:

| File | Lemmas | Status |
|---|---:|---|
| `CoplanarPermExtra.lean` | 17 | **All clean.** 11 `coplanar_perm_N` permutation facts + 4 coplanarity lemmas (`reflect__coplanar`, `inangle__coplanar`, ...) that GeoCoq's own chapter split never grouped into one file. |
| `Ch10Line2Extra.lean` | 31 | **All currently `sorry`** (declared with correct signatures, file builds clean). Covers `Ch10_line_reflexivity_2.v`, a continuation of Ch10 that neither the base pipeline nor the upper-chapter stub generator had ever ported. Declaring these (even unproven) was enough to unblock 5 previously name-unresolved dependencies in Ch11 — see below. Proving them for real is future work. |

## Ch11 — angles

**58/278 clean, 220 tainted, 0 hole.**

The name-resolution layer is now **100% saturated**: every one of the 220
non-clean lemmas parses and resolves every reference it makes (zero
"unresolved head" blockers, down from 32 earlier this session). The remaining
gap is exclusively:
1. Genuine build/type-check failures in the transliterated body (a proof that
   parses fine syntactically but Lean's elaborator rejects) — roughly 31
   confirmed instances.
2. A known repair-loop limitation: when many fresh proof attempts are inserted
   into one file simultaneously and one is genuinely broken, Lean's error
   recovery can emit spurious diagnostics on unrelated *later* declarations,
   which the current line-based error attribution sometimes misdemotes back to
   `sorry` alongside the real failure. Isolation-testing individual suspects
   confirms most of them are independently valid; a batched/isolated repair
   strategy that avoids this is the next planned fix, not yet implemented.

## Ch12–Ch13f — partial

Ledger-confirmed clean counts from the deterministic pass (no `sorry`-fallback,
no LLM):

| Chapter | Clean / Total | Chapter | Clean / Total |
|---|---:|---|---:|
| Ch12 | 33/84 | Ch13c | 2/65 |
| Ch12b | 0/30 | Ch13d | 1/60 |
| Ch13a | 7/39 | Ch13e | 0/15 |
| Ch13b | 12/22 | Ch13f | 0/12 |

## Ch14a–Ch16b — attempted, needs re-verification

A full-chapter pass hit a real bug in `Ch14a.lean` (content had been
quadruplicated by an earlier recovery script) that cascaded false "upstream
blocked" reports through Ch14b–Ch16b. The `Ch14a.lean` bug is fixed and
confirmed structurally clean (95 theorems, 95 `#print axioms` lines, 1 `end`),
but a fresh clean/tainted/hole count for Ch14a–Ch16b has **not yet been
re-measured** after that fix — reporting the pre-fix numbers here would be
exactly the kind of stale-measurement mistake `GEOLEAN.md` documents avoiding
for the Elements corpus, so they're deliberately omitted. Current on-disk
`sorry` counts (informational only, not a clean/tainted breakdown):

| Chapter | Sorry / Total | Chapter | Sorry / Total |
|---|---:|---|---:|
| Ch14a | 73/95 | Ch15b | 2/5 |
| Ch14b | 20/37 | Ch16a | 15/27 |
| Ch14c | 4/36 | Ch16b | 61/87 |
| Ch15a | 7/79 | | |

Next step: re-run the deterministic pass Ch14a→Ch16b now that the upstream
block is cleared, and replace this table with real numbers.

## Reproduce

```bash
cd /path/to/repo
python3 geolean_pipeline/climb_upper.py Ch11        # single chapter, deterministic only
python3 geolean_pipeline/climb_upper.py             # all Ch11-Ch16b chapters
tail -20 .climb_upper_ledger.jsonl                  # per-chapter clean/tainted/hole history
```
