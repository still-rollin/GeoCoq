/-
Translated from theories/Elements/OriginalProofs/lemma_lessthancongruence.v.

  Lt A B C D → Cong C D E F → Lt A B E F

Carry the witness on the CD side through a chain of extensions to the
EF side: extend EF past E to get a `P` with `BetS P E F`, extend EP past
E by `AB` to get a witness `H'` on `EF`. Then a five-segment chase plus
`lemma_betweennesspreserved` produces `BetS E H' F`, which witnesses
`Lt A B E F` together with the construction's `Cong E H' A B`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_doublereverse
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennesspreserved

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_lessthancongruence (A B C D E F : Point)
    (hLt : Lt A B C D) (hCong_CD_EF : Cong C D E F) : Lt A B E F := by
  -- Unfold Lt A B C D → ⟨G, BetS C G D, Cong C G A B⟩
  obtain ⟨G, hBetS_CGD, hCong_CG_AB⟩ := hLt
  -- Distinctness facts.
  have hBNE_CGD := lemma_betweennotequal C G D hBetS_CGD
  have hCD : C ≠ D := hBNE_CGD.2.2
  have hCG : C ≠ G := hBNE_CGD.2.1
  have hEF : E ≠ F := axiom_nocollapse C D E F hCD hCong_CD_EF
  have hFE : F ≠ E := lemma_inequalitysymmetric E F hEF
  have hAB : A ≠ B := axiom_nocollapse C G A B hCG hCong_CG_AB
  -- First extension: build P with BetS F E P ∧ Cong E P F E.
  obtain ⟨P, hBetS_FEP, _hCong_EP_FE⟩ := lemma_extension F E F E hFE hFE
  have hBetS_PEF : BetS P E F := axiom_betweennesssymmetry F E P hBetS_FEP
  have hPE : P ≠ E := (lemma_betweennotequal P E F hBetS_PEF).2.1
  -- Second extension: build H' with BetS P E H' ∧ Cong E H' A B.
  obtain ⟨H', hBetS_PEH', hCong_EH'_AB⟩ := lemma_extension P E A B hPE hAB
  -- Distinctness for the inner extension.
  have hDC : D ≠ C := by
    intro hDCeq
    rw [hDCeq] at hBetS_CGD
    exact axiom_betweennessidentity C G hBetS_CGD
  have hEP : E ≠ P := lemma_inequalitysymmetric P E hPE
  -- Third extension: build Q with BetS D C Q ∧ Cong C Q E P.
  obtain ⟨Q, hBetS_DCQ, hCong_CQ_EP⟩ := lemma_extension D C E P hDC hEP
  have hBetS_QCD : BetS Q C D := axiom_betweennesssymmetry D C Q hBetS_DCQ
  -- Cong chain to derive Cong Q C P E.
  have hCong_QC_CQ : Cong Q C C Q := cn_equalityreverse Q C
  have hCong_QC_EP : Cong Q C E P :=
    lemma_congruencetransitive Q C C Q E P hCong_QC_CQ hCong_CQ_EP
  have hCong_EP_PE : Cong E P P E := cn_equalityreverse E P
  have hCong_QC_PE : Cong Q C P E :=
    lemma_congruencetransitive Q C E P P E hCong_QC_EP hCong_EP_PE
  -- Sum of parts: Cong Q D P F.
  have hCong_QD_PF : Cong Q D P F :=
    cn_sumofparts Q C D P E F hCong_QC_PE hCong_CD_EF hBetS_QCD hBetS_PEF
  -- Cong A B E H' and Cong C G E H'.
  have hCong_AB_EH' : Cong A B E H' :=
    lemma_congruencesymmetric A E H' B hCong_EH'_AB
  have hCong_CG_EH' : Cong C G E H' :=
    lemma_congruencetransitive C G A B E H' hCong_CG_AB hCong_AB_EH'
  -- BetS Q C G via inner transitivity from BetS Q C D and BetS C G D.
  have hBetS_QCG : BetS Q C G := axiom_innertransitivity Q C G D hBetS_QCD hBetS_CGD
  -- Apply axiom_5_line: Cong D G F H'.
  have hCong_DG_FH' : Cong D G F H' :=
    axiom_5_line Q C G D P E H' F hCong_CG_EH' hCong_QD_PF hCong_CD_EF
      hBetS_QCG hBetS_PEH' hCong_QC_PE
  -- Flip to Cong G D H' F via doublereverse.
  have hCong_GD_H'F : Cong G D H' F := (lemma_doublereverse D G F H' hCong_DG_FH').2
  -- Apply lemma_betweennesspreserved on the C-G-D / E-H'-F triangle.
  have hBetS_EH'F : BetS E H' F :=
    lemma_betweennesspreserved C G D E H' F hCong_CG_EH' hCong_CD_EF hCong_GD_H'F hBetS_CGD
  -- Conclude Lt A B E F with witness H'.
  exact ⟨H', hBetS_EH'F, hCong_EH'_AB⟩

end GeocoqTranslate.Elements
