# Autonomous session progress log

Running log of the autonomous Tarski-automation work. Each entry: what was built,
build status, honesty check, blockers. No git commits; no sorry/admit/axiom in any
committed file; existing non-authoritative `Ch0x` files untouched; `col3` cone not
attempted (pending Julien).

## Session start state
- ColR ✅ (`Tarski_dev/ColR.lean`, 395 lines) — reflective collinearity, `colr`
- CongR ✅ (`Tarski_dev/CongR.lean`, 318 lines) — reflective congruence, `cong_r`
- assert_diffs ✅ (`Tarski_dev/TarskiDiffs.lean` + `DiffRuleSet.lean`) — forward `≠` rule-set

## Queue
1. `finish` closer combining colr / cong_r / assert_diffs
2. next reflective tactic (CoincR / coplanarity)
3. expand ColR+CongR acceptance suites + stress goal (decide vs native_decide)
4. statement-translation script: Tarski chapter → `theorem … := by sorry` stubs

---

## Item 1 — `finish` closer ✅ (`Tarski_dev/TarskiFinish.lean`)
Combined closer `Tfinish` = `first | assumption | colr | cong_r | assert_diffs`,
dispatching by goal shape. 5 acceptance tests (Col / Cong / ≠ / cong-derived-≠ /
trivial) pass. `lake build` green (8.3s), no sorry.

**Bug found + fixed (general improvement):** `colr`/`cong_r` did full work
before failing on wrong-shaped goals, so `Tfinish`'s `first | …` chain made the
build time out (>2min). Added an **early instance-synthesis check** to both tactics
(`synthInstance (ColTheory/CongTheory …)` up front; `throwError` if absent), so they
now fail instantly on non-matching goals. `colr`/`cong_r` are now safe to
drop into any `first | …` closer. ColR.lean + CongR.lean rebuilt green.

## Item 4 — statement-translation script ✅ (`transpiler/tarski_statements.py`)
Deterministic Layer-2: a Tarski `.v` chapter → Lean `theorem <name> : <stmt> := by
sorry` stubs. Reuses `geolean_transpile.translate_type`; adds Tarski surface fixes.
**Verified on Ch06_out_lines: 53/53 statements translated and all 53 typecheck**
(clean build, 0 errors, 53 `sorry`-warnings as expected). The generated stub file is
the reconstruction target (Layer 3); removed from the tree after verification since
it is regenerable and the session keeps the tree sorry-free.

**Two bugs found + fixed (both in the new script, shared code untouched):**
- point type must be `Type`, not `Type*` — the class `Tarski_neutral_dimensionless`
  is monomorphic `(Tpoint : Type)`; `Type*` caused a parse/universe cascade.
- the leading-`forall` binder regex must accept primes/digits (`A'`, `C'`, `A0`,
  `D0`) — pervasive in Tarski point names — else quantified points lose their
  `: Tpoint` annotation and the predicates' instances get "stuck".

## Item 5 — end-to-end reconstruction pilot ✅ (`Tarski_dev/PilotCh06.lean`)
The whole pipeline run live on **three real Ch06 lemmas** (`l6_16_1`,
`col_transitivity_1`, `col_transitivity_2`): each *statement* is the verbatim
output of `tarski_statements.py` (Layer 2), each *proof* is a single `colr`
(Layer 1) replacing GeoCoq's multi-line betweenness case-splits. Plus two concrete
`Cong` goals closed by `cong_r`. `lake build` green (20s).

**Honest instance wiring (the `col3`-gate, handled without a cone).**
- `CongR.CongTheory Tpoint Cong` — **fully proven** from the raw `Cong` axioms
  (`cong_pseudo_reflexivity`/`cong_inner_transitivity`); `#print axioms congThy`
  → *depends on no axioms*. No assumption on the `Cong` side at all.
- `ColR.ColTheory Tpoint Col` — `trivial`/`perm1`/`perm2` proven from Ch02-level
  facts (`bet_trivial`, `bet_sym`, themselves proven here from
  `segment_construction`/`inner_pasch`/axioms — no geometric cone). The one deep
  field `col3` is **assumed via an explicit typeclass `Col3Assumption`**, so every
  reconstructed theorem carries `[Col3Assumption Tpoint]` in its signature.
- Verified honest: `#print axioms col_transitivity_1` → `[propext,
  Classical.choice, Quot.sound]` only — **no `sorryAx`, no `admit`, no `axiom`**;
  the assumption shows up as a *hypothesis*, not a baked-in axiom.

This closes the col3-gate pragmatically: when the Ch02–Ch05 cone is later ported,
`Col3Assumption` is discharged and the pilot theorems become unconditional — the
`colr` proofs stay byte-for-byte identical.

## Item 6 — tactic rename + Phase-1 (value + coverage) ✅
Prof (Julien) flagged the pilot: (1) `col_refl` reads as "reflexivity"; (2) a
transitivity fact closing in one word looks unsound. Both addressed:
- **Rename** `col_refl → colr`, `cong_refl → cong_r` (= GeoCoq's `ColR`/`CongR`)
  across all 4 `.lean` + 3 docs; primed helper `cong_refl'` (genuine reflexivity
  lemma) left intact. Full rebuild green.
- **Soundness proven empirically** (not asserted): 5 `fail_if_success` guards in
  `PilotCh06.lean` — `colr` FAILS with no hyps / missing distinctness / one hyp
  missing / a fresh unconstrained point, and SUCCEEDS only with the genuine hyps.
  `colr` scans the *local context* (it is the "context-scanning Col solver", not a
  goal-syntax tactic); `#print axioms` shows no `sorryAx`.
- **Phase-1(a) — `colr` beyond a single `col3`**: a multi-merge `example` in
  `PilotCh06.lean` (`Col P R S` from two independent lines) that needs **three
  saturation steps** — genuine closure work independent of the `col3` axiom's
  strength. Green.
- **Phase-1(b) — Ch06 coverage of `Tfinish`** (throwaway harness `intros; Tfinish`
  over all 53 stubs with the assumed instances; harness removed after measuring —
  49 expected failures, can't live in the tree): **4/53 close, of which 3 are
  genuine** (`l6_16_1`, `col_transitivity_1`, `col_transitivity_2` — the
  collinearity-closure family) and **1 is circular** (`col3` itself = the
  assumption; excluded from the honest count). The other 49 conclude
  `Out`(16)/`Bet`(8)/`∃`(4)/`Le`(4)/`=`(3)/`≠`(7)/`↔`(1)/`Cong`(1) — reasoning the
  closure tactics do not cover. **Honest reading:** raw `Tfinish` alone covers only
  pure-closure goals; this is precisely why the oracle-guided reconstruction
  (Phase 3) is needed — it decomposes complex goals into closure-sized pieces.

## Item 7 — Phase-3 prototype: oracle-guided reconstruction ✅
Julien's Coghetto method, prototyped in three pieces:
- **Oracle-extraction script** `transpiler/oracle_skeleton.py` — parses one lemma's
  Ltac proof into a structured skeleton: NEW-POINT steps (existential/construction
  asserts, per Julien's "keep the new-point statements" heuristic), other `assert`
  `have`s (translated to Lean via the shared type translator), and the justifying
  lemma names. Verified: on `l6_3_1` it flags both `point_construction_different`
  new-point steps (`∃ C, Bet A P C ∧ P <> C`); on `col_out2_col` it lists the full
  10-lemma base; on `out_col` it (correctly) finds no intermediate steps.
- **End-to-end reconstruction** `Tarski_dev/OracleReconstruct.lean` (green) — Ch06
  `out_col`: a `fail_if_success` guard shows raw `Tfinish` cannot close it (hyp is
  `Out`, not a closure fact); the oracle-structure-guided proof (`unfold Out`; case;
  close via the reusable base brick `bet_sym`) does. `bet_trivial`/`bet_sym`
  un-privated in `PilotCh06.lean` as reusable base lemmas.
- **Dependency map** (oracle `--all` over Ch06, justification-base frequencies) — the
  porting critical path: `between_symmetry` 10× (= `bet_sym`, DONE),
  `l6_6` 8×, `bet_out` 5×, `col_transitivity_1` 5× (= colr, DONE),
  `col_permutation_1/2` 4×/3× (= colr, DONE), then the Ch05 between-lemmas
  `l5_1/l5_2/l5_3`, `between_exchange4`, `between_equality`,
  `point_construction_different`, … This turns "port Ch06" into a finite, ordered
  worklist and shows the closure tactics + `bet_sym` already discharge the
  top-frequency base.

**Honest finding:** the bottleneck from 3/53 to full coverage is NOT more tactics —
it is porting the betweenness/`Out` base the oracle pinpoints (Ch05/early-Ch06), i.e.
the same cone that `col3` needs (Phase 2). The oracle gives the order.

## Item 8 — critical-path Tier 1 ported ✅ (`Tarski_dev/BetweenOutBase.lean`)
The top of the oracle dependency map, proven OUTRIGHT from the axioms (no assumption,
no cone). 17 GeoCoq base lemmas, names verbatim so reconstruction calls them directly:
- betweenness (Ch03, from `inner_pasch`/`between_identity`): `between_trivial`,
  `between_symmetry` (map #1, 10×), `between_trivial2`, `between_equality` (4×),
  `between_equality_2`, `between_exchange3`, `between_inner_transitivity` (4×),
  `bet_neq12/21/23/32__neq`.
- `Out` base (Ch06): `out_col`, `l6_6` (8×), `bet_out` (5×), `bet_out_1`,
  `out_trivial`, `out_diff1`, `out_diff2`.
`lake build` green first try (472 ms). `#print axioms between_symmetry` / `bet_out`
→ **"does not depend on any axioms"** — fully constructive from the Tarski class
fields, cleaner even than the pilot's `col_transitivity_1`. No `sorry`/`admit`/`axiom`.

## Item 9 — Tier 2 begun: full Ch02 + Ch03 base ported ✅ (`CongBase.lean`, `SegmentCone.lean`)
Started the cone and climbed Ch02–Ch03 completely — all genuinely proven from the
axioms, no assumption, GeoCoq names verbatim.
- `CongBase.lean` (11): the `Cong` equivalence/commutativity base (`cong_reflexivity`,
  `cong_symmetry`, `cong_transitivity`, `cong_left/right_commutativity`,
  `cong_commutativity`, `cong_trivial_identity`, `cong_reverse_identity`, `cong_diff`),
  `five_segment_with_def`, and **`l2_11`** (segment addition — first lemma above the
  Ch02 base that the cone needs).
- `SegmentCone.lean` (5): **`construction_uniqueness`** (from `l2_11` + `five_segment`)
  and the Ch03 outer-connectivity betweenness lemmas `outer_transitivity_between2`,
  `between_exchange2`, `outer_transitivity_between` (map 3×), `between_exchange4`
  (map 3×).
All three files build first try (~0.4 s each). `#print axioms l2_11` /
`construction_uniqueness` / `between_exchange4` → `[propext, Classical.choice,
Quot.sound]` only (standard, from `by_cases`) — no `sorryAx`, no `Col3Assumption`.
**Running total: 33 base lemmas, axiom-free.**

## Item 10 — Ch04 segment machinery ported ✅ (`Ch04Cong.lean`)
The hard middle of the cone, all proven outright from the axioms + Ch02/Ch03 base:
`l4_2` (inner five segment — the hardest early Tarski lemma), `l4_3`, `l4_3_1`,
`l4_5` (copy a betweenness point onto a congruent segment), `l4_6` (betweenness under
triangle congruence), `l4_16` (five-segment with `Col`, 3-case), `l4_17` (the key
collinear-equidistance lemma). A `CongR.CongTheory Tpoint Cong` instance (from the
proven Ch02 base) lets `cong_r` discharge every `Cong`-normalisation step — this is
what made `l4_2`'s and `l4_16`'s many `Cong` subgoals tractable. Builds green
(l4_2 ~21 s; batches ~13-20 s). `#print axioms l4_2`/`l4_16`/`l4_17` → `[propext,
Classical.choice, Quot.sound]` — no `sorryAx`, no assumption. Also added
`point_construction_different` / `two_distinct_points` / `lower_dim_ex` to
`SegmentCone.lean` (from `lower_dim`).

**Running total: ~40 base/segment lemmas, all axiom-free.** Ch02 + Ch03 + Ch04 done.

**What's left of the cone:** just the capstone `l5_1` (Ch05 connectivity, ~100 lines,
~30 intermediate constructions — but every prerequisite it calls is now ported), then
the short `l5_2`/`l5_3`, then `l6_16_1` → `col_transitivity` = **`col3`**. Reaching
`col3` discharges `Col3Assumption` and makes the pilot theorems unconditional.

## Session tally
Track A: ColR ✅ · CongR ✅ · assert_diffs ✅ · Tfinish ✅ (CoincR pending Julien A1)
Track B: statement-translation script ✅ (Ch06: 53/53 typecheck)
Track C: **end-to-end reconstruction pilot ✅** (3 real Ch06 lemmas + 2 Cong goals +
multi-merge stress, green, honest — `col3` as explicit `Col3Assumption`, no
sorry/axiom). Renamed `colr`/`cong_r`; soundness guards added.
Track D: **Ch06 coverage measured** — raw `Tfinish` = 3/53 genuine (closure family);
motivates oracle-guided reconstruction (Phase 3).
Track E: **Phase-3 prototype ✅** — `oracle_skeleton.py` (skeleton + new-point
heuristic) · `OracleReconstruct.lean` (out_col reconstructed, direct Tfinish fails) ·
Ch06 dependency map → porting critical path (base-lemmas, ordered).
Track F: **cone base: Ch02 + Ch03 + Ch04 ported ✅** — `BetweenOutBase` (17) +
`CongBase` (11) + `SegmentCone` (5+3) + `Ch04Cong` (7: `l4_2`..`l4_17`) = **~40
lemmas, axiom-free, no assumption**, first-try green. `cong_r` instance discharges
the `Cong`-normalisation. Remaining cone: just `l5_1` → `l5_2/l5_3` → `col3`.
All committed files sorry-free; nothing git-committed.

## Item 11 — 2026-07-10: Ch09/Ch10 hole-filling pass + real `translit.py` bug fix

Separate track from Items 1-10 (the ColR/cone work above): this targets the newer
`geolean_pipeline/` climb architecture, specifically `Tarski_dev/Ch02.lean..Ch10.lean`
(511 lemmas at session start, `_c`-suffixed names, live convention — distinct from
the older non-authoritative `Ch0x_*.lean` files and from the cone files above).
Entry state: 432/512 real proof bodies, 80 literal `sorry` (Ch06=2, Ch07=3, Ch08=5,
Ch09=52, Ch10=18). Goal: push toward 500+/512 via the deterministic transliterator
first, LLM cascade (`cascade_llm.py`) only after.

**Step 1 — verified the incoming handoff note.** Two `translit.py` fixes (nested
`and_ind`/`or_ind`/`ex_ind` elim-leak in `emit()`, `parse_let` type-ascription skip)
were already on disk, confirmed present and matching the described diff. Baseline
`lake build` on the `Ch10` module (imports the whole `Ch02..Ch10` chain): **0 errors,
411/511 kernel-clean** (`#print axioms`, no `sorryAx`) — matches the note exactly.

**Step 2 — first deterministic re-pass on the 80 Ch09+Ch10 holes: 0/80 unlocked.**
The two on-disk fixes are real but orthogonal to this hole set — every one of the 80
failed with `UNRESOLVED head: <name> (not ported / unknown)`, not a parser crash.

**Step 3 — found and fixed a seeding bug in the harness (not `translit.py`).** The
throwaway driver script seeded `translit.LOCAL_SIGS` via `orchestrator.parse_stubs()`,
which keys by the *literal* Lean theorem name — already `_c`-suffixed in these
post-climb files (e.g. `bet_col_c`). `translit.py`'s resolver looks up the *base*
Coq name (`bet_col`) when it sees that call in a proof term, so every lookup missed
even though the lemma (`bet_col_c`, `col_permutation_5_c`, `perp_sym_c`,
`not_col_distincts_c`, …) was already proven and sitting in `Ch03.lean`/`Ch04.lean`/
`Ch08.lean`. Re-seeding with the correct base-name-keyed pattern (mirrors
`climb_upper.py`'s `seed_base_pool()`) alone took 0/70 candidates → 27/70 producing a
syntactically clean body — a pure harness fix, zero `translit.py` changes.

**Step 4 — found and fixed a second harness bug: binder extraction.** The driver's
binder-name regex (`re.findall(r"\((\w+)[^)]*?:", tail)`, copied from
`cascade_llm.py`'s `attempt()`, where it's only an LLM-prompt hint and thus harmless)
only captures the *first* name per `(...)` group — so `(A B C X Y P : Tpoint)` yielded
`['A']` instead of all six, positionally misaligning the Coq→Lean binder substitution
and leaking raw Coq hypothesis names (`H`, `H0`, `B`, `P`, …) into emitted Lean as
`Unknown identifier` errors. Fixed by switching to `orchestrator.parse_stubs()`'s
regex (`[\(\{\[]\s*([^:(){}\[\]]+?)\s*:`, split on whitespace per group) — the same
extractor `climb.py`'s production `climb()` already uses correctly.

**Step 5 — real `translit.py` bug found and fixed: `ex_intro` match-arity.** Porting
4 core coplanarity lemmas (`col__coplanar`, `ncop__ncol`, `ts__coplanar`,
`perp__coplanar`, from `theories/Main/Annexes/coplanar.v` — outside the usual
`Tarski_dev/Ch*.v` oracle glob, reached directly via `run_proof` with an explicit
path) + 12 `coplanar_perm_*` variants surfaced a real bug: Coq's raw proof term for
an `ex_intro` pattern-match (`match H with | ex_intro _ x x0 => ...`) carries an
extra leading pattern slot for the existential's implicit motive/predicate parameter
that Lean's `Exists`/`⟨⟩` has no slot for. `emit()` (term mode) already special-cased
`f=="ex_intro"` correctly (drops `args[0]`, uses `args[1]`/`args[2]`), but
`emit_match` (match mode) blindly emitted every parsed pattern var, producing
`obtain ⟨_, x, x0⟩ := H` against a 2-field `Exists` — Lean silently misaligned the
destructure, binding `x` to a `Prop` component instead of the `Tpoint` witness,
surfacing downstream as `Application type mismatch: argument x has type Col A B w✝
... but is expected to have type Tpoint`. Fixed in `geolean_pipeline/translit.py`
`emit_match`: `if _ctor=="ex_intro" and len(vars)>2: vars=vars[-2:]`, mirroring the
term-mode special case. Coplanarity port result: **1/16 → 15/16 kernel-verified
clean** after the fix (the remaining `ts__coplanar`/`perp__coplanar` failures that
looked like a *different* bug — `rcases ... is not an inductive datatype` — turned
out to be downstream fallout of the same arity bug, and also cleared).

**Step 6 — 16 new base lemmas spliced into `Ch09.lean`, rebuilt, confirmed clean.**
`col__coplanar_c`, `ncop__ncol_c`, `ts__coplanar_c`, `perp__coplanar_c`,
`coplanar_perm_{1,2,4,6,8,9,12,16,17,18,19,21}_c` — all inserted after the `variable`
line (available to every Ch09/Ch10 hole), `#print axioms` lines added, full
`lake build` on `Ch10`: **0 errors, 428/527 clean** (412+16 ✓, confirms every spliced
lemma is genuinely axiom-clean in context, not just in isolation).

**Step 7 — final deterministic re-pass on the original 70 holes: 69 remain.**
With both harness fixes, the `translit.py` fix, and the 16 new base lemmas in place,
re-ran the full pass: translit candidates rose 0→50/70, but kernel-verify still only
closed **1 additional hole total across the whole session** (`ex_sym_c` — closed in
an earlier intermediate pass). The other 49 candidates fail kernel-verify on a long
tail of *distinct* real errors (unknown identifiers, stuck typeclass search, invalid
anonymous-constructor inference, nested `cases` failures) — no longer one repeating
bug. 19 holes still can't even produce a candidate: partly missing further base
(`collect_diffs`, not yet ported), partly a recurring `"<name>-><name>: dropped N
implicit arg(s)"` note on already-ported lemmas (`bet_neq12__neq`, `out_col`,
`cong_symmetry`) that looks like a **third, undiagnosed** transpiler bug in
`choose_variant`'s implicit-arg-count inference — not yet investigated.

**Honest final count — Ch09+Ch10: 69/70 holes remain** (was 70/70 at session start;
1 closed: `ex_sym_c`). Base chain: 511→527 lemmas, 411→428 kernel-clean (+16, all the
new coplanarity lemmas, zero from the original 70 holes beyond `ex_sym_c`).

**Process note:** ran the same 69/70-hole deterministic pass 5 times this session
(after seeding fix, after binder fix, after `ex_intro` fix, after a stale-`.olean`
false-negative from editing `Ch09.lean` without an intervening `lake build`, and the
final clean run) — real progress each time (candidate count climbed), but repeated
full-batch re-verification is expensive under load (this machine: 8 cores, was
sharing with a concurrent `climb_upper.py Ch11` run + 3 idle IDE Lean-server workers,
load average briefly hit 12+). Future passes on this same hole set should re-verify
only the subset actually affected by a given fix, not the full batch.

**Deliverable, not yet committed:** `translit.py`'s `ex_intro` match-arity fix (1
line + comment) is a real, general transpiler correctness fix — worth keeping
regardless of Ch09/Ch10's remaining count, since it's already demonstrated 15x
leverage on the coplanarity family alone and likely affects other chapters' `ex_ind`
patterns too (untested beyond Ch09/Ch10 + `coplanar.v` in this session).

**Addendum — the actual root cause, confirmed.** Per Julien's original guidance
(`tarski_architecture.md` §0): port the reflective tactics first, reconstruct
proofs using that automation. `ColR`/`CongR` (`colr`/`cong_r`) *were* ported —
mature, verified, 400+300 lines. But grepping all of `Ch02.lean..Ch10.lean` for
`colr`/`cong_r`/`Tfinish`: **zero occurrences.** The whole `translit.py` climb
pipeline transliterates Coq's raw kernel proof term literally instead of
invoking the ported automation — so when Coq's tactic script calls `ColR`
(41× in `Ch09_plane.v`), what gets transliterated is the specific expanded
chain of primitive lemmas ColR's internals happened to construct for that one
goal (`col_permutation_5 D X C (col_permutation_1 C D X H2)`, etc.), not a
single `colr` call. This is almost certainly why the deterministic transpiler
needs an ever-growing tail of individual permutation/transitivity lemmas.

Confirmed empirically (`ScratchColRTest.lean`, `lake env lean`, kernel-clean,
no `sorryAx`): wired a real `ColTheory Tpoint Col` instance into a scratch
file (missing from the climb chain entirely — `PilotCh06.lean` built one but
it's never imported by `Ch02.lean..Ch10.lean`, and it depended on an unproven
`Col3Assumption` placeholder). That placeholder is no longer needed — derived
`col3` unconditionally from `col_transitivity_1_c`/`l6_16_1_c` (`Ch06.lean`) +
permutation lemmas (`Ch04.lean`), already proven in the chain. With the
instance wired, `colr` closes pure-permutation goals AND transitivity-shaped
goals in one tactic call, zero individual lemmas referenced.

Design + staged plan to act on this: [`docs/ch09_ch10_closure_architecture.md`](ch09_ch10_closure_architecture.md).
Not yet executed: promoting the scratch instance to a permanent file + wiring
it into the real chain, and adding a `colr`/`cong_r` prefilter to the hole-fill
driver before falling back to literal transliteration.


