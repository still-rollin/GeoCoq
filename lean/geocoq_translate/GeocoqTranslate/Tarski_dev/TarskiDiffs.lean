/-
Lean port of GeoCoq's `assert_diffs` — automatic derivation of distinctness
(`A ≠ B`) facts from the hypotheses in context.

Source: the `Ltac assert_diffs` used throughout `Tarski_dev` (e.g.
`theories/Main/Tarski_dev/Ch12_parallel.v:236`). GeoCoq implements it as a
`repeat match goal` that, for each hypothesis of a recognised geometric shape
(`~Col`, `Bet`, `Cong`, `Midpoint`, `Out`, `Per`, …), applies a *distinctness
lemma* and adds the resulting `≠` facts (with `not_exist_hyp` dedup guards).

The idiomatic Lean equivalent is an **aesop forward rule-set**: each distinctness
lemma is a `safe forward` rule, so the derived `≠` facts are produced by
forward-chaining exactly when needed (aesop tracks them, so there is no
re-derivation loop — the dedup is automatic). `assert_diffs` is an aesop pass over
that set.

As with `ColR`/`CongR`, the mechanism is parametric over abstract interfaces (one
small `*Diff` class per predicate, so instance resolution is unambiguous) — this
file is self-contained and `sorry`-free; the real Tarski instances attach the
lemmas as they are proven.
-/
import Mathlib.Tactic
import GeocoqTranslate.Tarski_dev.DiffRuleSet

namespace GeocoqTranslate.Tarski.Diffs

/-! ## The interfaces

One tiny class per predicate — each distinctness lemma mentions a single geometric
predicate, so its instance is determined by that predicate alone (bundling all
predicates into one class would leave the others as unresolved metavariables when a
rule fires). More predicates (`Per`, `Perp`, `Le`, `Lt`, `TS`, …) follow the same
pattern. -/

class ColDiff (P : Type*) (Col : P → P → P → Prop) : Prop where
  /-- `not_col_distincts`: a non-collinear triple has three distinct points. -/
  not_col_distincts : ∀ A B C, ¬ Col A B C → A ≠ B ∧ A ≠ C ∧ B ≠ C

class BetDiff (P : Type*) (Bet : P → P → P → Prop) : Prop where
  /-- `bet_neq12__neq`: `Bet A B C` with `A ≠ B` gives `A ≠ C`. -/
  bet_neq12 : ∀ A B C, Bet A B C → A ≠ B → A ≠ C
  /-- `bet_neq23__neq`: `Bet A B C` with `B ≠ C` gives `A ≠ C`. -/
  bet_neq23 : ∀ A B C, Bet A B C → B ≠ C → A ≠ C

class CongDiff (P : Type*) (Cong : P → P → P → P → Prop) : Prop where
  /-- `cong_diff`: a segment congruent to a non-degenerate one is non-degenerate. -/
  cong_diff : ∀ A B C D, A ≠ B → Cong A B C D → C ≠ D

class MidpDiff (P : Type*) (Midp : P → P → P → Prop) : Prop where
  /-- `midpoint_distinct_1`: endpoints distinct ⇒ midpoint distinct from each. -/
  midpoint_distinct_1 : ∀ I A B, A ≠ B → Midp I A B → I ≠ A ∧ I ≠ B

class OutDiff (P : Type*) (Out : P → P → P → Prop) : Prop where
  /-- `out_distinct`: `Out A B C` forces `A ≠ B` and `A ≠ C`. -/
  out_distinct : ∀ A B C, Out A B C → A ≠ B ∧ A ≠ C

/-! ## Distinctness lemmas as aesop forward rules

Each interface field is exposed as a top-level lemma and registered `safe forward`
in the `TarskiDiffs` set. Aesop splits the conjunctions automatically, so every
individual `≠` fact becomes available by forward chaining. -/

section Rules
variable {P : Type*}

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem not_col_distincts {Col : P → P → P → Prop} [ColDiff P Col] {A B C : P}
    (h : ¬ Col A B C) : A ≠ B ∧ A ≠ C ∧ B ≠ C :=
  ColDiff.not_col_distincts A B C h

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem bet_neq12 {Bet : P → P → P → Prop} [BetDiff P Bet] {A B C : P}
    (h : Bet A B C) (hab : A ≠ B) : A ≠ C :=
  BetDiff.bet_neq12 A B C h hab

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem bet_neq23 {Bet : P → P → P → Prop} [BetDiff P Bet] {A B C : P}
    (h : Bet A B C) (hbc : B ≠ C) : A ≠ C :=
  BetDiff.bet_neq23 A B C h hbc

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem cong_diff {Cong : P → P → P → P → Prop} [CongDiff P Cong] {A B C D : P}
    (hab : A ≠ B) (h : Cong A B C D) : C ≠ D :=
  CongDiff.cong_diff A B C D hab h

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem midpoint_distinct_1 {Midp : P → P → P → Prop} [MidpDiff P Midp] {I A B : P}
    (hab : A ≠ B) (h : Midp I A B) : I ≠ A ∧ I ≠ B :=
  MidpDiff.midpoint_distinct_1 I A B hab h

@[aesop safe forward (rule_sets := [TarskiDiffs])]
theorem out_distinct {Out : P → P → P → Prop} [OutDiff P Out] {A B C : P}
    (h : Out A B C) : A ≠ B ∧ A ≠ C :=
  OutDiff.out_distinct A B C h

end Rules

/-! ## The tactic

`assert_diffs` runs the `TarskiDiffs` forward rules (over the default set), deriving
the `≠` facts and discharging distinctness goals. It is also the distinctness
component of the `finish`-style closers: adding `TarskiDiffs` to any `aesop
(rule_sets := …)` call makes the derived facts available to the rest of the search. -/

macro "assert_diffs" : tactic =>
  `(tactic| aesop (rule_sets := [TarskiDiffs]))

/-! ## Acceptance tests -/

section Tests
variable {P : Type*} {Col : P → P → P → Prop} {Bet : P → P → P → Prop}
  {Cong : P → P → P → P → Prop} {Midp : P → P → P → Prop} {Out : P → P → P → Prop}
  [ColDiff P Col] [BetDiff P Bet] [CongDiff P Cong] [MidpDiff P Midp] [OutDiff P Out]

-- direct distinctness from non-collinearity
example (A B C : P) (h : ¬ Col A B C) : A ≠ B := by assert_diffs
example (A B C : P) (h : ¬ Col A B C) : B ≠ C := by assert_diffs

-- congruence propagates non-degeneracy
example (A B C D : P) (hab : A ≠ B) (h : Cong A B C D) : C ≠ D := by assert_diffs

-- betweenness chains a distinctness through
example (A B C : P) (h : Bet A B C) (hab : A ≠ B) : A ≠ C := by assert_diffs

-- midpoint config
example (I A B : P) (hab : A ≠ B) (h : Midp I A B) : I ≠ A := by assert_diffs

-- multi-step: Out gives A≠B, then Cong propagates to C≠D
example (A B C D : P) (hout : Out A B C) (hcong : Cong A B C D) : C ≠ D := by assert_diffs

end Tests

end GeocoqTranslate.Tarski.Diffs
