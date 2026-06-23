/-
Translated from theories/Elements/OriginalProofs/lemma_layoff.v.

  A ≠ B → C ≠ D → ∃ X, Out A B X ∧ Cong A X C D

Lay off a segment congruent to CD on the ray from A through B. Two
applications of `lemma_extension`: one to extend BA past A by CD (giving
the construction point E), the second to extend EA past A by CD (giving
the result point P, which witnesses `Out A B P`).
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extension

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_layoff (A B C D : Point) (hAB : A ≠ B) (hCD : C ≠ D) :
    ∃ X, Out A B X ∧ Cong A X C D := by
  have hBA : B ≠ A := lemma_inequalitysymmetric A B hAB
  -- First extension: B → A → E with Cong A E C D.
  obtain ⟨E, hBetS_BAE, _hCong_AE_CD⟩ := lemma_extension B A C D hBA hCD
  have hBetS_EAB : BetS E A B := axiom_betweennesssymmetry B A E hBetS_BAE
  have hEA : E ≠ A := (lemma_betweennotequal E A B hBetS_EAB).2.1
  -- Second extension: E → A → P with Cong A P C D.
  obtain ⟨P, hBetS_EAP, hCong_AP_CD⟩ := lemma_extension E A C D hEA hCD
  -- Out A B P uses E as the common witness.
  have hOut_ABP : Out A B P := ⟨E, hBetS_EAP, hBetS_EAB⟩
  exact ⟨P, hOut_ABP, hCong_AP_CD⟩

end GeocoqTranslate.Elements
