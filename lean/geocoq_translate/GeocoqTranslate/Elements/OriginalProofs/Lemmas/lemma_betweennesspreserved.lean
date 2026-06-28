/-
Translated from theories/Elements/OriginalProofs/lemma_betweennesspreserved.v.

  Cong A B a b → Cong A C a c → Cong B C b c → BetS A B C → BetS a b c

Coq strategy: extend `ab`-segment past `b` by `bc` to get a witness `d`
with `BetS a b d` and `Cong b d b c`. Apply `axiom_5_line` to pin
`Cong C C c d`, derive `c = d` from `axiom_nocollapse` + `cn_stability`,
then substitute `d := c` into the constructed `BetS a b d`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_localextension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_betweennesspreserved (A B C a b c : Point)
    (h_AB_ab : Cong A B a b) (h_AC_ac : Cong A C a c) (h_BC_bc : Cong B C b c)
    (h_BetS_ABC : BetS A B C) : BetS a b c := by
  -- Phase 1: get distinctness facts.
  have h_BNE := lemma_betweennotequal A B C h_BetS_ABC
  have hAB : A ≠ B := h_BNE.2.1
  have hBC : B ≠ C := h_BNE.1
  have hab : a ≠ b := axiom_nocollapse A B a b hAB h_AB_ab
  have hbc : b ≠ c := axiom_nocollapse B C b c hBC h_BC_bc

  -- Phase 2: extend ab past b by bc to produce d with BetS a b d ∧ Cong b d b c.
  obtain ⟨d, h_BetS_abd, h_Cong_bd_bc⟩ := lemma_localextension a b c hab hbc

  -- Phase 3: chain Congs to get Cong B C b d.
  have h_Cong_bc_bd : Cong b c b d := lemma_congruencesymmetric b b d c h_Cong_bd_bc
  have h_Cong_bc_BC : Cong b c B C := lemma_congruencesymmetric b B C c h_BC_bc
  have h_Cong_bd_BC : Cong b d B C :=
    cn_congruencetransitive b d B C b c h_Cong_bc_bd h_Cong_bc_BC
  have h_Cong_BC_bd : Cong B C b d := lemma_congruencesymmetric B b d C h_Cong_bd_BC

  -- Phase 4: apply axiom_5_line. With D := C, c := d, d := c:
  --   Cong B C b c, Cong A C a c, Cong B C b c, BetS A B C, BetS a b c, Cong A B a b
  --   ⊢ Cong C C c d
  have h_Cong_CC_cd : Cong C C c d :=
    axiom_5_line A B C C a b d c h_Cong_BC_bd h_AC_ac h_BC_bc
      h_BetS_ABC h_BetS_abd h_AB_ab
  have h_Cong_cd_CC : Cong c d C C := lemma_congruencesymmetric c C C d h_Cong_CC_cd

  -- Phase 5: derive c = d by contradiction (nocollapse gives C ≠ C).
  have hcd : c = d := by
    apply cn_stability
    intro hcd_ne
    exact axiom_nocollapse c d C C hcd_ne h_Cong_cd_CC rfl

  -- Phase 6: substitute and close.
  rw [hcd]
  exact h_BetS_abd

end GeocoqTranslate.Elements
