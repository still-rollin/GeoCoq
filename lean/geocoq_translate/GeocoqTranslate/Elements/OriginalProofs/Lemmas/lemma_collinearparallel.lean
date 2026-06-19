/-
Translated from theories/Elements/OriginalProofs/lemma_collinearparallel.v.
  Par A B c d → Col c d C → C ≠ d → Par A B C d.

Transpiler emitted this clean, but `conclude_def Par` blows up reconstructing
the large `Par`/`Meet` definitions. Hand-finished: destruct `Par` directly,
build it explicitly, with the oracle (`geolean_oracle`) supplying every
`lemma_collinear4`/`collinearorder` argument order.
-/
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinear4
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_collinearparallel (A B C c d : Point)
    (h1 : Par A B c d) (h2 : Col c d C) (h3 : C ≠ d) : Par A B C d := by
  obtain ⟨a, b, p, q, R, hAB, hcd, hABa, hABb, hab, hcdp, hcdq, hpq, hnMeet, hbet1, hbet2⟩ := h1
  have hCdp : Col C d p := (lemma_collinearorder d C p (lemma_collinear4 c d C p h2 hcdp hcd)).1
  have hCdq : Col C d q := (lemma_collinearorder d C q (lemma_collinear4 c d C q h2 hcdq hcd)).1
  have hnMeet' : ¬ Meet A B C d := by
    intro hMeet
    obtain ⟨E, _, _, hABE, hCdE⟩ := hMeet
    have hCdc : Col C d c := (lemma_collinearorder c d C h2).2.2.2.2
    have hdEc : Col d E c := lemma_collinear4 C d E c hCdE hCdc h3
    have hcdE : Col c d E := (lemma_collinearorder d E c hdEc).2.2.1
    exact hnMeet ⟨E, hAB, hcd, hABE, hcdE⟩
  exact ⟨a, b, p, q, R, hAB, h3, hABa, hABb, hab, hCdp, hCdq, hpq, hnMeet', hbet1, hbet2⟩

end GeocoqTranslate.Elements
