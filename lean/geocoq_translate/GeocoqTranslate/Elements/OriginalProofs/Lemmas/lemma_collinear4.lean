/-
Translated from theories/Elements/OriginalProofs/lemma_collinear4.v.
  Col A B C → Col A B D → A ≠ B → Col B C D.

LLM-translated with the oracle (`geolean_oracle`) supplying the resolved
lemma-application recipe — every `lemma_3_X` / `axiom_connectivity` argument
order below is exactly what Coq's proof term uses. Col-from-`BetS` is built by
`unfold Col; tauto`; permutations use explicit `lemma_collinearorder` projections.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_5b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6a
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7a
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_outerconnectivity

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_collinear4 (A B C D : Point)
    (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D := by
  by_cases hBC : B = C
  · exact Or.inl hBC
  by_cases hBD : B = D
  · exact Or.inr (Or.inl hBD)
  by_cases hCD : C = D
  · exact Or.inr (Or.inr (Or.inl hCD))
  by_cases hAC : A = C
  · exact (lemma_collinearorder C B D (hAC ▸ hABD)).1
  by_cases hAD : A = D
  · exact (lemma_collinearorder D B C (hAD ▸ hABC)).2.1
  -- all distinct.  Reduce Col A B C / Col A B D to their `BetS` disjuncts.
  rcases hABC with h | h | h | hBAC | hABC' | hACB
  · exact absurd h hAB
  · exact absurd h hAC
  · exact absurd h hBC
  · -- hBAC : BetS B A C
    rcases hABD with h | h | h | hBAD | hABD' | hADB
    · exact absurd h hAB
    · exact absurd h hAD
    · exact absurd h hBD
    · -- BetS B A C, BetS B A D
      apply not_nCol_Col; intro H
      have hnBCD : ¬ BetS B C D := fun hbcd =>
        Col_nCol_False B C D H (by unfold euclidean_neutral_basis.Col; tauto)
      have hnACD : ¬ BetS A C D := fun hacd => hnBCD (lemma_3_5b B A C D hBAD hacd)
      have hnBDC : ¬ nCol B D C := by
        intro H2
        have hnADC : ¬ BetS A D C := fun hadc =>
          Col_nCol_False B D C H2
            (by have : BetS B D C := lemma_3_5b B A D C hBAC hadc
                unfold euclidean_neutral_basis.Col; tauto)
        exact hCD (lemma_outerconnectivity B A C D hBAC hBAD hnACD hnADC)
      have hBDC : Col B D C := not_nCol_Col B D C hnBDC
      exact Col_nCol_False B C D H (lemma_collinearorder B D C hBDC).2.2.2.1
    · -- BetS B A C, BetS A B D
      have hDBA : BetS D B A := axiom_betweennesssymmetry A B D hABD'
      have hDBC : BetS D B C := lemma_3_7b D B A C hDBA hBAC
      exact (lemma_collinearorder D B C (by unfold euclidean_neutral_basis.Col; tauto)).2.1
    · -- BetS B A C, BetS A D B
      have hBDA : BetS B D A := axiom_betweennesssymmetry A D B hADB
      have hBDC : BetS B D C := lemma_3_6b B D A C hBDA hBAC
      exact (lemma_collinearorder B D C (by unfold euclidean_neutral_basis.Col; tauto)).2.2.2.1
  · -- hABC' : BetS A B C
    rcases hABD with h | h | h | hBAD | hABD' | hADB
    · exact absurd h hAB
    · exact absurd h hAD
    · exact absurd h hBD
    · -- BetS A B C, BetS B A D
      have hDAB : BetS D A B := axiom_betweennesssymmetry B A D hBAD
      have hDBC : BetS D B C := lemma_3_7a D A B C hDAB hABC'
      exact (lemma_collinearorder D B C (by unfold euclidean_neutral_basis.Col; tauto)).2.1
    · -- BetS A B C, BetS A B D
      apply not_nCol_Col; intro H
      have hnBCD : ¬ BetS B C D := fun hbcd =>
        Col_nCol_False B C D H (by unfold euclidean_neutral_basis.Col; tauto)
      have hnBDC : ¬ BetS B D C := fun hbdc =>
        Col_nCol_False B C D H
          (lemma_collinearorder B D C (by unfold euclidean_neutral_basis.Col; tauto)).2.2.2.1
      exact hCD (lemma_outerconnectivity A B C D hABC' hABD' hnBCD hnBDC)
    · -- BetS A B C, BetS A D B
      have hDBC : BetS D B C := lemma_3_6a A D B C hADB hABC'
      exact (lemma_collinearorder D B C (by unfold euclidean_neutral_basis.Col; tauto)).2.1
  · -- hACB : BetS A C B
    rcases hABD with h | h | h | hBAD | hABD' | hADB
    · exact absurd h hAB
    · exact absurd h hAD
    · exact absurd h hBD
    · -- BetS A C B, BetS B A D
      have hDAB : BetS D A B := axiom_betweennesssymmetry B A D hBAD
      have hDCB : BetS D C B := lemma_3_5b D A C B hDAB hACB
      have hBCD : BetS B C D := axiom_betweennesssymmetry D C B hDCB
      unfold euclidean_neutral_basis.Col; tauto
    · -- BetS A C B, BetS A B D
      have hCBD : BetS C B D := lemma_3_6a A C B D hACB hABD'
      unfold euclidean_neutral_basis.Col; tauto
    · -- BetS A C B, BetS A D B
      apply not_nCol_Col; intro H
      have hBDC : BetS B D C := by
        by_contra h1
        have hBCD : BetS B C D := by
          by_contra h2
          have hBCA : BetS B C A := axiom_betweennesssymmetry A C B hACB
          have hBDA : BetS B D A := axiom_betweennesssymmetry A D B hADB
          exact hCD (axiom_connectivity B C D A hBCA hBDA h2 h1)
        exact Col_nCol_False B C D H (by unfold euclidean_neutral_basis.Col; tauto)
      exact Col_nCol_False B C D H
        (lemma_collinearorder B D C (by unfold euclidean_neutral_basis.Col; tauto)).2.2.2.1

end GeocoqTranslate.Elements
