/-
Lean port of GeoCoq's Tarski automation tactics (`finish.v` + per-chapter Ltac).

GeoCoq closes routine collinearity / congruence / betweenness side-goals with
one-word tactics backed by hint databases:
  Ltac Col  := auto with col.      Ltac Cong := auto with cong.
  Ltac Between := auto with between.
Here we reproduce them with `aesop` rule-sets populated by the translated
Ch02/Ch03 lemmas, so Tarski_dev proofs stay short and idiomatic:

  have : Col A B C := by Col
  have : Cong A B C D := by Cong

Later chapters extend the rule-sets with
  `attribute [aesop … (rule_sets := [Tcol])] my_new_col_lemma`.
-/
import GeocoqTranslate.Tarski_dev.AesopRuleSets
import GeocoqTranslate.Tarski_dev.Ch03_bet
import Mathlib.Tactic

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

/-! ## Hint rule-sets (the Lean analogue of GeoCoq's `col`/`cong`/`between` DBs).
    The sets `Tcol`/`Tcong`/`Tbet` are declared in `AesopRuleSets.lean`. -/

-- betweenness (col goals unfold to Bet disjunctions, so Tbet powers Col too)
attribute [aesop unsafe 50% forward (rule_sets := [Tbet, Tcol])] between_symmetry
attribute [aesop safe (rule_sets := [Tbet])] between_trivial between_trivial2

-- congruence
attribute [aesop safe (rule_sets := [Tcong])]
  cong_reflexivity cong_trivial_identity
attribute [aesop unsafe 50% (rule_sets := [Tcong])]
  cong_symmetry cong_left_commutativity cong_right_commutativity
  cong_commutativity cong_transitivity

/-! ## The closers -/

/-- GeoCoq `Between := auto with between`. -/
macro "Between" : tactic =>
  `(tactic| first | assumption | aesop (rule_sets := [Tbet]))

/-- GeoCoq `Cong := auto with cong`. -/
macro "Cong" : tactic =>
  `(tactic| first | assumption | aesop (rule_sets := [Tcong]))

/-- GeoCoq `Col := auto with col`. `Col` is `@[simp]`-unfoldable to a `Bet`
    disjunction, so unfolding + betweenness symmetry decides most goals. -/
macro "Col" : tactic =>
  `(tactic|
    first
      | assumption
      | (simp [Col, between_trivial, between_trivial2]; done)   -- degenerate Cols
      | (simp only [Col] at *; first | tauto | aesop (rule_sets := [Tbet]))
      | aesop (rule_sets := [Tcol]))

/-- GeoCoq `treat_equalities`: substitute degenerate equalities (`Cong A B C C`
    ⟹ `A = B`, etc.) and clean up. -/
macro "treat_equalities" : tactic =>
  `(tactic|
    ((try simp_all only [cong_reverse_identity, cong_trivial_identity]);
     (try subst_vars)))

end GeocoqTranslate.Tarski
