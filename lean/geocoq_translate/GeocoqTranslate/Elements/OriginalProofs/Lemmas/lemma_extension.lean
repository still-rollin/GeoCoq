/-
Translated from theories/Elements/OriginalProofs/lemma_extension.v.

  A ≠ B → P ≠ Q → ∃ X, BetS A B X ∧ Cong B X P Q

Stronger extension lemma than `lemma_localextension`. Doesn't assume
`B ≠ Q`; instead case-splits on whether `B = P` and uses `proposition_02`
(transport-a-segment) to produce the right-radius circle for the line/
circle continuity step.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.proposition_02
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruenceflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_extension (A B P Q : Point) (hAB : A ≠ B) (hPQ : P ≠ Q) :
    ∃ X, BetS A B X ∧ Cong B X P Q := by
  -- Phase 1: get some D with `Cong B D P Q`, dispatching on whether B = P.
  have hExistsD : ∃ D, Cong B D P Q := by
    rcases Classical.em (B = P) with hBP | hBP
    · -- B = P case: build the segment with QP-radius then flip the cong.
      have hQP : Q ≠ P := fun h => hPQ h.symm
      have hBQ : B ≠ Q := by rw [hBP]; exact fun h => hQP h.symm
      obtain ⟨D, hCong_BD_QP⟩ := proposition_02 B Q P hBQ hQP
      exact ⟨D, (lemma_congruenceflip B D Q P hCong_BD_QP).2.2⟩
    · -- B ≠ P case: direct application of proposition_02 with PQ-radius.
      exact proposition_02 B P Q hBP hPQ
  obtain ⟨D, hCong_BD_PQ⟩ := hExistsD

  -- Phase 2: build the BD-radius circle around B and intersect line AB.
  have hCong_PQ_BD : Cong P Q B D := lemma_congruencesymmetric P B D Q hCong_BD_PQ
  have hBD : B ≠ D := axiom_nocollapse P Q B D hPQ hCong_PQ_BD
  obtain ⟨J, hCI_J⟩ := postulate_Euclid3 B D hBD
  have hInCirc_B_J : InCirc B J := by
    show ∃ X Y U V W : Point,
      CI J U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
    exact ⟨B, B, B, B, D, hCI_J, Or.inl rfl⟩
  obtain ⟨_C, E, _hCol_ABC, hBetS_ABE, _hOnCirc_C_J, hOnCirc_E_J, _hBetS_CBE⟩ :=
    postulate_line_circle A B B J B D hCI_J hInCirc_B_J hAB

  -- Phase 3: chain Cong B E B D and Cong B D P Q for the goal.
  have hCong_BE_BD : Cong B E B D := axiom_circle_center_radius B B D J E hCI_J hOnCirc_E_J
  have hCong_BE_PQ : Cong B E P Q :=
    lemma_congruencetransitive B E B D P Q hCong_BE_BD hCong_BD_PQ
  exact ⟨E, hBetS_ABE, hCong_BE_PQ⟩

end GeocoqTranslate.Elements
