/-
Translated from theories/Elements/OriginalProofs/proposition_03.v.

Euclid, Elements Book I, Proposition 3:
  "Given two unequal straight lines, to cut off from the greater a
  straight line equal to the less."

Given `Lt C D A B` (segment CD is strictly shorter than AB) and
`Cong E F A B` (some segment EF is congruent to AB), there exists a
point X on segment EF with `BetS E X F ∧ Cong E X C D`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_lessthancongruence

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem proposition_03 (A B C D E F : Point)
    (hLt : Lt C D A B) (hCong_EF_AB : Cong E F A B) :
    ∃ X, BetS E X F ∧ Cong E X C D := by
  -- Flip Cong E F A B to Cong A B E F, then chain into Lt C D E F.
  have hCong_AB_EF : Cong A B E F :=
    lemma_congruencesymmetric A E F B hCong_EF_AB
  have hLt_CD_EF : Lt C D E F := lemma_lessthancongruence C D A B E F hLt hCong_AB_EF
  -- Lt C D E F unfolds directly to the existential we need.
  exact hLt_CD_EF

end GeocoqTranslate.Elements
