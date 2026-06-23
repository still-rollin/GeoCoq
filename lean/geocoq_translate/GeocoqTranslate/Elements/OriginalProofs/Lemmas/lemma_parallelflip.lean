/-
Translated from theories/Elements/OriginalProofs/lemma_parallelflip.v.
  Par A B C D → Par B A C D ∧ Par A B D C ∧ Par B A D C.

Hand-finished like `lemma_parallelsymmetric`: the Coq proof is pure
`conclude_def Par`/`conclude_def Meet` packing, where the bounded `conclude_def`
cannot cheaply reconstruct the large `Par` existential (witness reorder + an
ambiguous witness search; see docs/bounded_tactics_report.md §6). Instead we
destruct `Par` once and rebuild each flipped variant explicitly, reusing the
same witnesses `U V u v X`; the `Col` reorders go through the (now bounded)
`forward_using lemma_collinearorder`, and each `¬ Meet` variant is reduced by
hand to the original `¬ Meet A B C D`.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral Point]

theorem lemma_parallelflip :
    ∀ (A B C D : Point), Par A B C D → Par B A C D ∧ Par A B D C ∧ Par B A D C := by
  intro A B C D h1
  obtain ⟨U, V, u, v, X, hAB, hCD, hABU, hABV, hUV, hCDu, hCDv, huv, hnMeet, hbet1, hbet2⟩ := h1
  -- Col reorders (bounded forward_using)
  have hBAU : Col B A U := by forward_using lemma_collinearorder
  have hBAV : Col B A V := by forward_using lemma_collinearorder
  have hDCu : Col D C u := by forward_using lemma_collinearorder
  have hDCv : Col D C v := by forward_using lemma_collinearorder
  have hBA : B ≠ A := hAB.symm
  have hDC : D ≠ C := hCD.symm
  -- ¬ Meet variants, each reduced to ¬ Meet A B C D
  have hnMeetBACD : ¬ Meet B A C D := by
    intro hM
    obtain ⟨P, _, _, hBAP, hCDP⟩ := hM
    have hABP : Col A B P := by forward_using lemma_collinearorder
    exact hnMeet ⟨P, hAB, hCD, hABP, hCDP⟩
  have hnMeetABDC : ¬ Meet A B D C := by
    intro hM
    obtain ⟨P, _, _, hABP, hDCP⟩ := hM
    have hCDP : Col C D P := by forward_using lemma_collinearorder
    exact hnMeet ⟨P, hAB, hCD, hABP, hCDP⟩
  have hnMeetBADC : ¬ Meet B A D C := by
    intro hM
    obtain ⟨P, _, _, hBAP, hDCP⟩ := hM
    have hABP : Col A B P := by forward_using lemma_collinearorder
    have hCDP : Col C D P := by forward_using lemma_collinearorder
    exact hnMeet ⟨P, hAB, hCD, hABP, hCDP⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨U, V, u, v, X, hBA, hCD, hBAU, hBAV, hUV, hCDu, hCDv, huv, hnMeetBACD, hbet1, hbet2⟩
  · exact ⟨U, V, u, v, X, hAB, hDC, hABU, hABV, hUV, hDCu, hDCv, huv, hnMeetABDC, hbet1, hbet2⟩
  · exact ⟨U, V, u, v, X, hBA, hDC, hBAU, hBAV, hUV, hDCu, hDCv, huv, hnMeetBADC, hbet1, hbet2⟩

end GeocoqTranslate.Elements
