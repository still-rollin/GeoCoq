/-
Translated from theories/Elements/OriginalProofs/lemma_TGsymmetric.v.

  TG A a B b C c → TG B b A a C c

Symmetry of the triangle-inequality witness. Build a new witness `F` by
extending `Bb` past `b` by `Aa`. The five-segment chase gives
`Cong A K B F` (where `K` is the original witness for the `Aa+Bb` side),
which together with `lemma_lessthancongruence` produces the strict
inequality on the new side.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_doublereverse
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruenceflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_lessthancongruence

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_TGsymmetric (A B C a b c : Point) (hTG : TG A a B b C c) :
    TG B b A a C c := by
  -- Destructure TG A a B b C c → ⟨K, BetS A a K, Cong a K B b, Lt C c A K⟩.
  obtain ⟨K, hBetS_AaK, hCong_aK_Bb, hLt_Cc_AK⟩ := hTG
  -- Distinctness facts from BetS A a K.
  have h_BNE := lemma_betweennotequal A a K hBetS_AaK
  have h_aK : a ≠ K := h_BNE.1
  have h_Aa : A ≠ a := h_BNE.2.1
  -- Distinctness for the second extension.
  have h_Bb : B ≠ b := axiom_nocollapse a K B b h_aK hCong_aK_Bb
  -- Extend Bb past b by Aa to get the new witness F.
  obtain ⟨F, hBetS_BbF, hCong_bF_Aa⟩ := lemma_extension B b A a h_Bb h_Aa
  -- Two flips: Cong a A F b, then Cong A a F b.
  have hCong_aA_Fb : Cong a A F b :=
    (lemma_doublereverse b F A a hCong_bF_Aa).1
  have hCong_Aa_Fb : Cong A a F b :=
    (lemma_congruenceflip a A F b hCong_aA_Fb).2.1
  -- Flip Cong a K B b → Cong a K b B.
  have hCong_aK_bB : Cong a K b B :=
    (lemma_congruenceflip a K B b hCong_aK_Bb).2.2
  -- Reverse the BbF betweenness.
  have hBetS_FbB : BetS F b B := axiom_betweennesssymmetry B b F hBetS_BbF
  -- Sum-of-parts: Cong A K F B.
  have hCong_AK_FB : Cong A K F B :=
    cn_sumofparts A a K F b B hCong_Aa_Fb hCong_aK_bB hBetS_AaK hBetS_FbB
  -- Flip to Cong A K B F.
  have hCong_AK_BF : Cong A K B F :=
    (lemma_congruenceflip A K F B hCong_AK_FB).2.2
  -- Chain Lt C c A K with the new congruence.
  have hLt_Cc_BF : Lt C c B F :=
    lemma_lessthancongruence C c A K B F hLt_Cc_AK hCong_AK_BF
  -- Build the new TG witness.
  exact ⟨F, hBetS_BbF, hCong_bF_Aa, hLt_Cc_BF⟩

end GeocoqTranslate.Elements
