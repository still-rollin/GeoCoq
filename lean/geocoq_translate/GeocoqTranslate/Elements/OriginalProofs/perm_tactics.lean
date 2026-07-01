/-
Permutation-aware tactics for the Elements port — a faithful Lean rendering of
GeoCoq's `perm_apply` (theories/Main/Highschool/gravityCenter.v).

The FOUNDATIONAL machinery now lives in `euclidean_tactics.lean` (the `*_cases`
lemmas for Col / nCol / BetS / Cong, `perm_branch`, `permutation_intro_in_goal`,
and `perm_close`), proved from the definitions + class axioms only, so that the
engine itself (`contradict`) can reason modulo permutation without a circular
dependency on the derived `lemma_*` files.

This file adds the ONE predicate whose symmetry is a genuine derived lemma —
`Par` — and the goal-side `perm_apply` used at proof sites. -/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_parallelflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_parallelsymmetric

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

set_option maxHeartbeats 800000

/-- `Par_cases` — the one `*_cases` lemma that needs a derived lemma
    (`Par`'s symmetry is nontrivial), so it is defined here rather than in the
    engine. Same disjunct order as GeoCoq's `Par_cases`. -/
theorem Par_cases {A B C D : Point}
    (h : Par A B C D ∨ Par B A C D ∨ Par A B D C ∨ Par B A D C ∨
         Par C D A B ∨ Par C D B A ∨ Par D C A B ∨ Par D C B A) :
    Par A B C D := by
  rcases h with h|h|h|h|h|h|h|h <;>
    solve_by_elim (config := { maxDepth := 8 })
      [lemma_parallelflip, lemma_parallelsymmetric, And.left, And.right]

/-- GeoCoq's `perm_apply t`: apply lemma `t` modulo permutation of the goal's
    arguments, discharging `t`'s premises from context. Tries the `Par` head
    first, then the engine's foundational `permutation_intro_in_goal`
    (Col / nCol / BetS / Cong). -/
macro "perm_apply " t:term : tactic => `(tactic|
  ((first | apply Par_cases | permutation_intro_in_goal)
   perm_branch (apply $t <;> (first | assumption | perm_close | close))))

/-- `Par`-aware permutation closer for proof sites: close a `Par` goal that is a
    permutation of a hypothesis; otherwise fall back to the engine `perm_close`. -/
macro "perm_close_par" : tactic => `(tactic|
  first
    | perm_close
    | (apply Par_cases
       perm_branch assumption))

end GeocoqTranslate.Elements
