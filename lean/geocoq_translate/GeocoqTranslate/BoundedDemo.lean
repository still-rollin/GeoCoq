/-
DEMO: bounded `col_close` vs the unbounded `forward_using`/aesop macros.

`col_close` tries at most 6 concrete things — the identity (`assumption`) plus
the 5 reorderings `lemma_collinearorder` produces. No `aesop`, no `forward`
rule, no fact generation. So it cannot explode, regardless of how many Col
facts sit in context. Type-directed elaboration pins the points from the goal,
so `(by assumption)` always grabs the *right* source fact.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinear4

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

/-- Bounded collinearity closer: ≤ 6 fixed tries, no search. -/
macro "col_close" : tactic =>
  `(tactic|
    first
      | assumption
      | exact (lemma_collinearorder _ _ _ (by assumption)).1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.2.2)

-- A RICH context, like the middle of `lemma_twolines` (~10 Col facts floating
-- around). These are exactly the conditions where the old aesop macro timed out.
section
variable (A B C D E F : Point)
  (cAEB : Col A E B) (cCED : Col C E D) (cAFB : Col A F B) (cCFD : Col C F D)
  (cBEF : Col B E F) (cCDF : Col C D F) (cCDE : Col C D E) (cDEF : Col D E F)
  (cDCE : Col D C E) (cDCF : Col D C F)

-- Each of these is a REORDER step that the unbounded `forward_using
-- lemma_collinearorder` blew up on. `col_close` closes each instantly.
example : Col A B E := by col_close   -- from cAEB
example : Col E F B := by col_close   -- from cBEF
example : Col A B F := by col_close   -- from cAFB
example : Col D C F := by col_close   -- from cCDF
example : Col E F D := by col_close   -- from cDEF
end

-- The PIVOT step (`conclude lemma_collinear4`): the free pivot A is not in the
-- goal, but `apply <;> assumption` recovers it by matching a premise.
example (A B E F : Point) (hABE : Col A B E) (hABF : Col A B F) (hAB : A ≠ B) :
    Col B E F := by
  apply lemma_collinear4 <;> assumption

-- AMBIGUOUS PIVOT: two candidate pivots for `Col B E F`.
--   G is a DEAD END: `Col G B E` exists, but `Col G B F` does NOT.
--   A is CORRECT:    `Col A B E`, `Col A B F`, `A ≠ B` all present.
-- The dead-end hypothesis comes FIRST, so a no-backtracking tactic picks G.
section
variable (A B E F G : Point)
  (cABE : Col A B E) (cABF : Col A B F) (hAB : A ≠ B)   -- correct pivot A (older)
  (cGBE : Col G B E) (cGBF : Col G B F)                 -- trap G: passes FIRST TWO
                                                        -- premises, but NO `G ≠ B`

-- assumption tries newest-first → grabs G, clears `Col G B E` and `Col G B F`,
-- then dies on `G ≠ B`. A greedy/bounded tactic with no backtracking fails here.
example : Col B E F := by
  sorry
end

end GeocoqTranslate.Elements
