/-
Foundational permutation lemmas for the bounded `conclude` engine.

These give, from ONE oriented fact, the CONJUNCTION of all its argument
permutations (`Col A B C → Col A B C ∧ Col A C B ∧ …`). They are proved from the
DEFINITIONS (`Col`/`nCol`) and the CLASS AXIOMS (`axiom_betweennesssymmetry`,
the `cn_*` congruence axioms) ONLY — no dependency on `conclude` or any derived
`lemma_*`. That lets this file sit BELOW `conclude_bounded.lean`, so the meta
premise-matcher there can reason modulo argument-permutation (apply the matching
`*_perm` to a candidate hypothesis, then pick the conjunct the premise needs)
without a circular import.
-/
import Mathlib.Tactic
import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral
variable {Point : Type} [euclidean_neutral Point]

set_option maxHeartbeats 800000

/-- Betweenness symmetry as an iff, for `simp`-driven permutation closing. -/
theorem betS_symm_iff (A B C : Point) : BetS A B C ↔ BetS C B A :=
  ⟨axiom_betweennesssymmetry A B C, axiom_betweennesssymmetry C B A⟩

/-- All 6 argument permutations of a collinearity, from one. -/
theorem Col_perm (A B C : Point) (h : Col A B C) :
    Col A B C ∧ Col A C B ∧ Col B A C ∧ Col B C A ∧ Col C A B ∧ Col C B A := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold euclidean_neutral_basis.Col at *
      rcases h with h|h|h|h|h|h <;> simp_all [eq_comm, betS_symm_iff]

/-- All 6 argument permutations of a non-collinearity, from one. -/
theorem nCol_perm (A B C : Point) (h : nCol A B C) :
    nCol A B C ∧ nCol A C B ∧ nCol B A C ∧ nCol B C A ∧ nCol C A B ∧ nCol C B A := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold euclidean_neutral_basis.nCol at *
      simp_all [eq_comm, betS_symm_iff]

/-- Both orientations of a strict betweenness, from one. -/
theorem BetS_perm (A B C : Point) (h : BetS A B C) : BetS A B C ∧ BetS C B A :=
  ⟨h, axiom_betweennesssymmetry A B C h⟩

/-- All 8 argument permutations of a congruence, from one. -/
theorem Cong_perm (A B C D : Point) (h : Cong A B C D) :
    Cong A B C D ∧ Cong A B D C ∧ Cong B A C D ∧ Cong B A D C ∧
    Cong C D A B ∧ Cong C D B A ∧ Cong D C A B ∧ Cong D C B A := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    solve_by_elim (config := { maxDepth := 6 })
      [cn_congruencetransitive, cn_congruencereflexive, cn_equalityreverse, h]

end GeocoqTranslate.Elements
