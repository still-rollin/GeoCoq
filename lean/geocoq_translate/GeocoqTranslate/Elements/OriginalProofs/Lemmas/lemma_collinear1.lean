/-
Translated from theories/Elements/OriginalProofs/lemma_collinear1.v.
  Col A B C → Col B A C.
LLM-translated (goal-directed; the transpiler leaves a bare-`assert` fallback).
Col is the 6-way disjunction `A=B ∨ A=C ∨ B=C ∨ BetS B A C ∨ BetS A B C ∨ BetS A C B`;
each case maps to a disjunct of `Col B A C`, the last via betweenness symmetry.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_collinear1 (A B C : Point) (h : Col A B C) : Col B A C := by
  unfold euclidean_neutral_basis.Col at *
  rcases h with h | h | h | h | h | h
  · exact Or.inl h.symm                                        -- A=B → B=A
  · exact Or.inr (Or.inr (Or.inl h))                           -- A=C
  · exact Or.inr (Or.inl h)                                    -- B=C
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))         -- BetS B A C
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))                  -- BetS A B C
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr              -- BetS A C B → BetS B C A
      (axiom_betweennesssymmetry A C B h)))))

end GeocoqTranslate.Elements
