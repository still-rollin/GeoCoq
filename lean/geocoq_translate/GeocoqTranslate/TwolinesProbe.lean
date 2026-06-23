/-
The genuinely-ambiguous collinear4 step from `lemma_twolines`:
  goal `Col F B C`  via  lemma_collinear4  (oracle pivot = E).
Two candidate pivots for the premise `Col ?A F B`:
  - A : `Col A F B` ✓, but `Col A F C` is ABSENT, `A ≠ F` present  → DEEP TRAP
  - E : `Col E F B` ✓, `Col E F C` ✓, `E ≠ F` ✓                   → CORRECT
This is the real rich context (the accumulated Col facts of twolines).
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinear4

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

section
variable (A B C D E F : Point)
  -- accumulated facts of twolines, with the two pivot candidates present:
  (cAEB : Col A E B) (cABE : Col A B E) (cAFB : Col A F B) (cABF : Col A B F)
  (cBEF : Col B E F) (cEFB : Col E F B) (cDEF : Col D E F) (cEFD : Col E F D)
  (cDCE : Col D C E) (cDCF : Col D C F) (cCEF : Col C E F) (cEFC : Col E F C)
  (hAF : A ≠ F) (hEF : E ≠ F)

example : Col F B C := by
  sorry

end
end GeocoqTranslate.Elements
