/-
Translated from theories/Elements/OriginalProofs/lemma_trichotomy2.v.

  Lt A B C D → ¬ Lt C D A B

Antisymmetry of the strict-length order. Proof by contradiction: if both
`Lt A B C D` and `Lt C D A B`, then chasing `lemma_lessthancongruence`
produces a point `F` with `BetS C F D` and `Cong C F C D`, contradicting
`lemma_partnotequalwhole`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_lessthancongruence
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_partnotequalwhole

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_trichotomy2 (A B C D : Point) (hLt_AB_CD : Lt A B C D) :
    ¬ Lt C D A B := by
  obtain ⟨E, hBetS_CED, hCong_CE_AB⟩ := hLt_AB_CD
  have hCong_AB_CE : Cong A B C E := lemma_congruencesymmetric A C E B hCong_CE_AB
  intro hLt_CD_AB
  have hLt_CD_CE : Lt C D C E :=
    lemma_lessthancongruence C D A B C E hLt_CD_AB hCong_AB_CE
  obtain ⟨F, hBetS_CFE, hCong_CF_CD⟩ := hLt_CD_CE
  have hBetS_CFD : BetS C F D := lemma_3_6b C F E D hBetS_CFE hBetS_CED
  have hNotCong : ¬ Cong C F C D := lemma_partnotequalwhole C F D hBetS_CFD
  exact hNotCong hCong_CF_CD

end GeocoqTranslate.Elements
