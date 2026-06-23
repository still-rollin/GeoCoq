/-
Translated from theories/Elements/OriginalProofs/lemma_ray2.v.

  Out A B C → A ≠ B

If C lies on the ray from A through B, then A and B are distinct.
Pull out the witness `BetS E A B` from the `Out` definition and apply
`lemma_betweennotequal`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_ray2 (A B C : Point) (hOut : Out A B C) : A ≠ B := by
  obtain ⟨_E, _hBetS_EAC, hBetS_EAB⟩ := hOut
  exact (lemma_betweennotequal _ A B hBetS_EAB).1

end GeocoqTranslate.Elements
