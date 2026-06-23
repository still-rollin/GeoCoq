/-
TEST: can a COMPLETE complex proof compile with only FAITHFUL BOUNDED tactics
(no aesop)?  `lemma_NCorder` failed under the old aesop macros. Here every step
uses only bounded analogs of Coq's tactics:
  forward_using lemma_collinearorder  →  col_close   (forward-once + project)
  contradict                          →  contra      (bounded)
  close                               →  nclose      (bounded And-build)
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral
variable {Point : Type} [euclidean_neutral Point]

/-- faithful `forward_using lemma_collinearorder`: forward-apply to a hyp, project. -/
macro "col_close" : tactic =>
  `(tactic|
    first
      | assumption
      | exact (lemma_collinearorder _ _ _ (by assumption)).1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.2.1
      | exact (lemma_collinearorder _ _ _ (by assumption)).2.2.2.2)

/-- faithful `contradict`: bounded. Uses the `nCol`/`Col` clash lemma directly
    (Lean's `contradiction` won't unfold `nCol = ¬Col` on its own). -/
macro "contra" : tactic =>
  `(tactic|
    first
      | contradiction
      | solve_by_elim [Col_nCol_False]   -- bounded backtracking finds the matching nCol/Col pair
      | (exfalso; solve_by_elim)
      | assumption)

/-- faithful `close` for an nCol-conjunction: split the conjunction with the
    anonymous constructor (does NOT descend into `nCol = ¬Col`), then assumption. -/
macro "nclose" : tactic =>
  `(tactic|
    first
      | assumption
      | exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩
      | exact ⟨by assumption, by assumption, by assumption, by assumption⟩
      | exact ⟨by assumption, by assumption, by assumption⟩
      | exact ⟨by assumption, by assumption⟩)

-- The full lemma, faithfully, bounded-only:
theorem lemma_NCorder_faithful :
    ∀ (A B C : Point), nCol A B C →
      nCol B A C ∧ nCol B C A ∧ nCol C A B ∧ nCol A C B ∧ nCol C B A := by
  intro A B C h1
  have hBAC : nCol B A C := by
    apply nCol_notCol
    intro h
    have : Col A B C := by col_close
    contra
  have hBCA : nCol B C A := by
    apply nCol_notCol
    intro h
    have : Col A B C := by col_close
    contra
  have hCAB : nCol C A B := by
    apply nCol_notCol
    intro h
    have : Col A B C := by col_close
    contra
  have hACB : nCol A C B := by
    apply nCol_notCol
    intro h
    have : Col A B C := by col_close
    contra
  have hCBA : nCol C B A := by
    apply nCol_notCol
    intro h
    have : Col A B C := by col_close
    contra
  nclose

-- ============================================================================
-- ORACLE VERSION: same lemma, but each reorder step uses the EXACT resolved
-- call the oracle reported (lemma_collinearorder B A C / B C A / ...), with the
-- explicit projection — no search at all. Everything ELSE (nCol_notCol, contra,
-- nclose) is identical to the bounded version.
-- ============================================================================
theorem lemma_NCorder_oracle :
    ∀ (A B C : Point), nCol A B C →
      nCol B A C ∧ nCol B C A ∧ nCol C A B ∧ nCol A C B ∧ nCol C B A := by
  intro A B C h1
  have hBAC : nCol B A C := by
    apply nCol_notCol; intro h
    have : Col A B C := (lemma_collinearorder B A C h).1
    contra
  have hBCA : nCol B C A := by
    apply nCol_notCol; intro h
    have : Col A B C := (lemma_collinearorder B C A h).2.2.1
    contra
  have hCAB : nCol C A B := by
    apply nCol_notCol; intro h
    have : Col A B C := (lemma_collinearorder C A B h).2.1
    contra
  have hACB : nCol A C B := by
    apply nCol_notCol; intro h
    have : Col A B C := (lemma_collinearorder A C B h).2.2.2.1
    contra
  have hCBA : nCol C B A := by
    apply nCol_notCol; intro h
    have : Col A B C := (lemma_collinearorder C B A h).2.2.2.2
    contra
  nclose

end GeocoqTranslate.Elements
