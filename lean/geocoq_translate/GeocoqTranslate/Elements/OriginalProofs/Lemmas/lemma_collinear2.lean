/-
Translated from theories/Elements/OriginalProofs/lemma_collinear2.v.
  Col A B C → Col B C A.   (LLM-translated; goal-directed tail.)
`Col B C A = B=C ∨ B=A ∨ C=A ∨ BetS C B A ∨ BetS B C A ∨ BetS B A C`.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_collinear2 (A B C : Point) (h : Col A B C) : Col B C A := by
  unfold euclidean_neutral_basis.Col at *
  rcases h with h | h | h | h | h | h
  · exact Or.inr (Or.inl h.symm)                              -- A=B → B=A
  · exact Or.inr (Or.inr (Or.inl h.symm))                     -- A=C → C=A
  · exact Or.inl h                                            -- B=C
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))        -- BetS B A C
  · exact Or.inr (Or.inr (Or.inr (Or.inl                      -- BetS A B C → BetS C B A
      (axiom_betweennesssymmetry A B C h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl             -- BetS A C B → BetS B C A
      (axiom_betweennesssymmetry A C B h)))))

end GeocoqTranslate.Elements
