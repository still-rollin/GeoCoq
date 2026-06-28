/-
EXPERIMENT: translate `lemma_oppositesideflip` TWO ways and diff them.
  TS P A B Q → TS P B A Q.
Richer than NCorder: an existential (TS extract+build), a lemma-application
(forward_using lemma_NCorder), and a reorder (forward_using lemma_collinearorder).

Reuses col_close / contra / nclose / lemma_NCorder_faithful from FaithfulDemo.
-/
import GeocoqTranslate.FaithfulDemo

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral
variable {Point : Type} [euclidean_neutral Point]

/-- bounded `forward_using lemma_NCorder`: forward-apply to a hyp, project. -/
macro "nc_close" : tactic =>
  `(tactic|
    first
      | assumption
      | exact (lemma_NCorder_faithful _ _ _ (by assumption)).1
      | exact (lemma_NCorder_faithful _ _ _ (by assumption)).2.1
      | exact (lemma_NCorder_faithful _ _ _ (by assumption)).2.2.1
      | exact (lemma_NCorder_faithful _ _ _ (by assumption)).2.2.2.1
      | exact (lemma_NCorder_faithful _ _ _ (by assumption)).2.2.2.2)

-- ===== BOUNDED-ONLY version =====
theorem oppositesideflip_bounded (A B P Q : Point) (h : TS P A B Q) : TS P B A Q := by
  obtain ⟨r, hPrQ, hABr, hABP⟩ := h            -- conclude_def TS  (extract)
  have hBAP : nCol B A P := by nc_close          -- forward_using lemma_NCorder
  have hBAr : Col B A r := by col_close          -- forward_using lemma_collinearorder
  exact ⟨r, hPrQ, hBAr, hBAP⟩                     -- conclude_def TS  (build, reuse r)

-- ===== ORACLE-ASSISTED version =====
theorem oppositesideflip_oracle (A B P Q : Point) (h : TS P A B Q) : TS P B A Q := by
  obtain ⟨r, hPrQ, hABr, hABP⟩ := h            -- conclude_def TS  (extract)  [SAME]
  have hBAP : nCol B A P := (lemma_NCorder_faithful A B P hABP).1     -- oracle: NCorder A B P
  have hBAr : Col B A r := (lemma_collinearorder A B r hABr).1        -- oracle: collinearorder A B r
  exact ⟨r, hPrQ, hBAr, hBAP⟩                     -- conclude_def TS  (build, reuse r)  [SAME]

end GeocoqTranslate.Elements
