/-
Translated from theories/Elements/OriginalProofs/lemma_parallelsymmetric.v.
  Par A B C D → Par C D A B.

The Coq proof is pure `conclude_def Par`/`conclude_def Meet` packing — the
oracle (`geolean_oracle`) reports zero resolved lemma calls, so there are no
argument orders to recover; aesop instead times out reconstructing the large
`Par`/`Meet` existentials. Hand-finished like `lemma_collinearparallel`:
destruct `Par` directly and rebuild it with the roles of AB and CD swapped.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_parallelsymmetric (A B C D : Point) (h : Par A B C D) : Par C D A B := by
  obtain ⟨U, V, u, v, X, hAB, hCD, hABU, hABV, hUV, hCDu, hCDv, huv, hnMeet, hbet1, hbet2⟩ := h
  have hnMeet' : ¬ Meet C D A B := by
    intro hM
    obtain ⟨P, _, _, hCDP, hABP⟩ := hM
    exact hnMeet ⟨P, hAB, hCD, hABP, hCDP⟩
  exact ⟨u, v, U, V, X, hCD, hAB, hCDu, hCDv, huv, hABU, hABV, hUV, hnMeet', hbet2, hbet1⟩

end GeocoqTranslate.Elements
