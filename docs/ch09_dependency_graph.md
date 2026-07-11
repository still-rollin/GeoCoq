# Ch09.lean remaining-holes dependency graph — updated architecture

Regenerated 2026-07-11 against the current file state: **473/527 clean, 36 holes remain in
Ch09** (down from the 454/527, 49-hole baseline this doc originally described). Raw
machine-readable form: [`ch09_dependency_graph.json`](ch09_dependency_graph.json).

**What closed since the original graph:** `outer_pasch`, `l9_8_2`, `l9_17`, `l9_19`,
`out_out_one_side`, `out_one_side_1`, `col_two_sides_bet` (the wave-0 leaves), then
`l9_9`, `out_one_side`, `ts2__ex_bet2` (wave 1), then `out_two_sides_two_sides`,
`col_one_side_out`, `ts_ts_os` (wave 2). All verified `#print axioms`-clean (no `sorryAx`).

**Method:** unchanged — for each of the 36 remaining `sorry` theorems, pulled its
`Lemma ... Qed.` body from `theories/Main/Tarski_dev/Ch09_plane.v` and grepped it for
identifier-boundary occurrences of every other remaining pool member's base name.

## Current leaves (zero in-pool dependencies)

| name | Coq proof length | transitively unlocks |
|---|---|---|
| **`l9_31`** | 221 lines | **31 of the other 35 nodes (89% of the whole remaining pool)** |
| `cop_per2__col` | 145 lines | 5 (`cop_perp2__col`, `two_sides_dec`, `one_side_dec`, `cop_dec`, `cong3_cop2__col`) |
| `l8_21_bis` | 67 lines | 0 |
| `one_or_two_sides_aux` | 62 lines | 0 |
| `os_ts1324__os` | — | 0 |

**This is the key change from the old graph.** Previously the pool had a broad wave-0 of
8 independent leaves. Now it has collapsed to a single dominant chain:
`l9_31 → os__coplanar → coplanar_trans_1 → col_cop__cop → col_cop2__cop (indeg 8) → ...`
— closing `l9_31` alone is a prerequisite for essentially the entire rest of Ch09's
coplanarity machinery (waves 1–9 below). `cop_per2__col` gates a smaller side-branch
that overlaps with `l9_31`'s reach (`cop_perp2__col`, `two_sides_dec`, `one_side_dec`,
`cop_dec`, `cong3_cop2__col` all need *both*). `l8_21_bis`, `one_or_two_sides_aux`, and
`os_ts1324__os` are dead-end leaves — each is a 9-way/case-bash-style proof with **zero**
downstream pool dependents, so closing them only adds +1 each; not worth the effort
relative to `l9_31`/`cop_per2__col`.

## Top hubs by in-degree (most depended-upon)

`col_cop2__cop`(8) · `coplanar_trans_1`(5) · `col_cop__cop`(5) · `os__coplanar`(3) ·
`col2_cop2__eq`(3) · `l9_41_2`(3)

## Topological attack order (10 waves)

0. `cop_per2__col`, `l8_21_bis`, **`l9_31`**, `one_or_two_sides_aux`, `os_ts1324__os`
1. `os__coplanar`
2. `coplanar_trans_1`, `sac__coplanar`
3. `col_cop__cop`
4. `col2_cop__cop`, `col_cop2__cop`, `cong3_cop2__col`, `cop_perp2__col`
5. `col2_cop2__eq`, `cop2_ts__tsp`, `cop_out__osp`, `coplanar_pseudo_trans`, `l9_39`, `tsp_exists`, `two_sides_dec`
6. `cop2_os__osp`, `cop3_tsp__tsp`, `l9_18_3`, `l9_30`, `l9_41_2`, `one_side_dec`, `osp_bet__osp`, `osp_reflexivity`
7. `bet_cop__tsp`, `cop3_osp__osp`, `cop_dec`, `osp_transitivity`, `tsp__nosp`
8. `cop_osp__ex_cop2`, `osp__ntsp`
9. `l9_19_3`

## Strategy implication

There are no more cheap broad-fan-out wins left in Ch09 — the remaining pool has
condensed into one deep, high-leverage proof (`l9_31`, 221 lines, comparable in size to
`l9_8_2`) plus one deep, low-fan-out proof (`cop_per2__col`, 145 lines, needs
`five_segment`/`l4_17`/`l4_18`/`l5_6`/`l6_13_2`/`le_bet`/`construction_uniqueness`/`l7_20`
— none used elsewhere in the Lean port yet, plus a full `Coplanar` case-split). Both are
required to fully close the pool; `l9_31` should go first since its reach subsumes most of
`cop_per2__col`'s. `l8_21_bis`, `one_or_two_sides_aux`, `os_ts1324__os` are safe to skip
indefinitely — they block nothing.
