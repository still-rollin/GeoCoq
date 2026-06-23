/-
Translated from theories/Elements/OriginalProofs/lemma_ray4.v.

  (BetS A E B ∨ E = B ∨ BetS A B E) → A ≠ B → Out A B E

Three-case dispatch. Build a fresh witness `J` past `A` on the line BA
(via `lemma_extension`), reverse it to `BetS J A B`, and in each of the
three cases of the disjunction extend that into `BetS J A E` — by
`axiom_innertransitivity`, by substitution, or by `lemma_3_7b`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7b

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_ray4 (A B E : Point)
    (hCase : BetS A E B ∨ E = B ∨ BetS A B E) (hAB : A ≠ B) :
    Out A B E := by
  have hBA : B ≠ A := lemma_inequalitysymmetric A B hAB
  obtain ⟨J, hBetS_BAJ, _hCong_AJ_AB⟩ := lemma_extension B A A B hBA hAB
  have hBetS_JAB : BetS J A B := axiom_betweennesssymmetry B A J hBetS_BAJ
  -- In each case derive BetS J A E, then use J as the Out witness.
  rcases hCase with hBetS_AEB | hEB | hBetS_ABE
  · -- Case 1: BetS A E B → BetS J A E via inner transitivity.
    have hBetS_JAE : BetS J A E :=
      axiom_innertransitivity J A E B hBetS_JAB hBetS_AEB
    exact ⟨J, hBetS_JAE, hBetS_JAB⟩
  · -- Case 2: E = B → BetS J A E by substitution.
    subst hEB
    exact ⟨J, hBetS_JAB, hBetS_JAB⟩
  · -- Case 3: BetS A B E → BetS J A E via lemma_3_7b.
    have hBetS_JAE : BetS J A E := lemma_3_7b J A B E hBetS_JAB hBetS_ABE
    exact ⟨J, hBetS_JAE, hBetS_JAB⟩

end GeocoqTranslate.Elements
