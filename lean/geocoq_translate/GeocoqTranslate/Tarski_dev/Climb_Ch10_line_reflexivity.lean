import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ex_sym_c (A B X : Tpoint) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y) := sorry

theorem is_image_is_image_spec_c (P P' A B : Tpoint) (hAB : A ≠ B) :
    Reflect P' P A B ↔ ReflectL P' P A B := by
  exact ⟨(fun H0 => or_ind (fun H1 => and_ind (fun _ H2 => H2) H1) (fun H1 => and_ind (fun H2 _ => (let H3 := hAB H2; False_ind (ReflectL P' P A B) H3)) H1) H0), (fun H0 => Or.inl (⟨((fun H1 => (let H2 := hAB H1; False_ind False H2))), H0⟩))⟩

theorem ex_sym1_c (A B X : Tpoint) (hAB : A ≠ B) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y ∧ Reflect X Y A B) := sorry

theorem l10_2_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P1 P A B) (h₂ : Reflect P2 P A B) : P1 = P2 := sorry

theorem l10_2_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P1 P A B) (h₂ : ReflectL P2 P A B) : P1 = P2 := sorry

theorem l10_2_existence_spec_c (A B P : Tpoint) :
    ∃ P', ReflectL P' P A B := sorry

theorem l10_2_existence_c (A B P : Tpoint) :
    ∃ P', Reflect P' P A B := sorry

theorem l10_4_spec_c (A B P P' : Tpoint) (h : ReflectL P P' A B) :
    ReflectL P' P A B := sorry

theorem l10_4_c (A B P P' : Tpoint) (h : Reflect P P' A B) :
    Reflect P' P A B := sorry

theorem l10_5_c (A B P P' P'' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect P'' P' A B) : P = P'' := sorry

theorem l10_6_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P P1 A B) (h₂ : Reflect P P2 A B) : P1 = P2 := sorry

theorem l10_6_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P P1 A B) (h₂ : ReflectL P P2 A B) : P1 = P2 := sorry

theorem l10_6_existence_spec_c (A B P' : Tpoint) (hAB : A ≠ B) :
    ∃ P, ReflectL P' P A B := by
  have H0 := l10_2_existence_spec_c A B P'
  obtain ⟨P, H⟩ := H0
  exact ⟨P, (l10_4_spec_c A B P P' H)⟩

theorem l10_6_existence_c (A B P' : Tpoint) :
    ∃ P, Reflect P' P A B := by
  have H := l10_2_existence_c A B P'
  obtain ⟨P, H0⟩ := H
  exact ⟨P, (l10_4_c A B P P' H0)⟩

theorem l10_7_c (A B P P' Q Q' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect Q' Q A B) (h₃ : P' = Q') : P = Q :=
  eq_ind P' (fun Q'0 => Reflect Q'0 Q A B - > P = Q) (fun H2 => l10_2_uniqueness_c A B P' P Q (l10_4_c A B P' P h₁) (l10_4_c A B P' Q H2)) Q' h₃ h₂

theorem l10_8_c (A B P : Tpoint) (h : Reflect P P A B) : Col P A B := sorry

theorem col__refl_c (A B P : Tpoint) (h : Col P A B) : ReflectL P P A B := sorry

theorem is_image_col_cong_c (A B P P' X : Tpoint) (hAB : A ≠ B)
    (h₁ : Reflect P P' A B) (h₂ : Col A B X) : Cong P X P' X := sorry

theorem is_image_spec_col_cong_c (A B P P' X : Tpoint)
    (h₁ : ReflectL P P' A B) (h₂ : Col A B X) : Cong P X P' X := sorry

theorem image_id_c (A B T T' : Tpoint) (hAB : A ≠ B)
    (hCol : Col A B T) (hRefl : Reflect T T' A B) : T = T' := sorry

theorem osym_not_col_c (A B P P' : Tpoint)
    (h₁ : Reflect P P' A B) (h₂ : ¬ Col A B P) : ¬ Col A B P' := sorry

theorem midpoint_preserves_image_c (A B P P' Q Q' M : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B M) (hRefl : Reflect P P' A B)
    (h₁ : Midpoint M P Q) (h₂ : Midpoint M P' Q') : Reflect Q Q' A B := sorry

theorem image_in_is_image_spec_c (M A B P P' : Tpoint)
    (h : ReflectL_at M P P' A B) : ReflectL P P' A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H0
  exact ⟨(⟨M, (⟨H2, H3⟩)⟩), H1⟩

theorem image_in_gen_is_image_c (M A B P P' : Tpoint)
    (h : Reflect_at M P P' A B) : Reflect P P' A B := by
  rcases h with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    have H3 := image_in_is_image_spec_c M A B P P' H2
    exact Or.inl (⟨((fun H4 => (let H5 := H1 H4; False_ind False H5))), H3⟩)
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨H3, H4⟩ := H2
    subst H1
    subst H3
    exact Or.inr (⟨eq_refl, H4⟩)

theorem image_image_in_c (A B P P' M : Tpoint) (hPP' : P ≠ P')
    (h₁ : ReflectL P P' A B) (h₂ : Col A B M) (h₃ : Col P M P') :
    ReflectL_at M P P' A B := sorry

theorem image_in_col_c (A B P P' Y : Tpoint)
    (h : ReflectL_at Y P P' A B) : Col P P' Y := sorry

theorem is_image_spec_rev_c (P P' A B : Tpoint)
    (h : ReflectL P P' A B) : ReflectL P P' B A := sorry

theorem is_image_rev_c (P P' A B : Tpoint)
    (h : Reflect P P' A B) : Reflect P P' B A := by
  rcases h with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨(Ne.symm H1), (is_image_spec_rev_c P P' A B H2)⟩)
  · exact Or.inr (and_ind (fun H1 H2 => eq_ind_r (fun A0 => Midpoint A0 P' P - > B = A0 /\ Midpoint B P' P) (fun H3 => ⟨eq_refl, H3⟩) H1 H2) H0)

theorem midpoint_preserves_per_c (A B C A1 B1 C1 M : Tpoint)
    (hPer : Per A B C)
    (h₁ : Midpoint M A A1) (h₂ : Midpoint M B B1) (h₃ : Midpoint M C C1) :
    Per A1 B1 C1 := sorry

theorem col__image_spec_c (A B X : Tpoint) (h : Col A B X) :
    ReflectL X X A B := sorry

theorem image_triv_c (A B : Tpoint) : Reflect A A A B := sorry

theorem cong_midpoint__image_c (A B X Y : Tpoint)
    (h₁ : Cong A X A Y) (h₂ : Midpoint B X Y) : Reflect Y X A B := sorry

theorem col_image_spec__eq_c (A B P P' : Tpoint)
    (h₁ : Col A B P) (h₂ : ReflectL P P' A B) : P = P' :=
  l10_6_uniqueness_spec_c A B P P P' (col__image_spec_c A B P h₁) h₂

theorem image_spec_triv_c (A B : Tpoint) : ReflectL A A B B := sorry

theorem image_spec__eq_c (A P P' : Tpoint) (h : ReflectL P P' A A) : P = P' := sorry

theorem image__midpoint_c (A P P' : Tpoint) (h : Reflect P P' A A) :
    Midpoint A P' P := by
  rcases h with H0 | H0
  · obtain ⟨H1, _⟩ := H0
    exact False_ind (Midpoint A P' P) (H1 eq_refl)
  · obtain ⟨_, H1⟩ := H0
    exact H1

theorem is_image_spec_dec_c (A B C D : Tpoint) :
    ReflectL A B C D ∨ ¬ ReflectL A B C D := sorry

theorem l10_14_c (P P' A B : Tpoint) (hPP' : P ≠ P') (hAB : A ≠ B)
    (h : Reflect P P' A B) : TS A B P P' := sorry

theorem l10_15_c (A B C P : Tpoint)
    (hCol : Col A B C) (hNCol : ¬ Col A B P) :
    ∃ Q, Perp A B Q C ∧ OS A B P Q := sorry

theorem ex_per_cong_c (A B C D X Y : Tpoint)
    (hAB : A ≠ B) (hXY : X ≠ Y) (hCol : Col A B C) (hNCol : ¬ Col A B D) :
    ∃ P, Per P C A ∧ Cong P C X Y ∧ OS A B P D := sorry

theorem exists_cong_per_c (A B X Y : Tpoint) :
    ∃ C, Per A B C ∧ Cong B C X Y := sorry

#print axioms GeocoqTranslate.Tarski.Base.ex_sym_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_is_image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.ex_sym1_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_uniqueness_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_existence_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l10_4_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_4_c
#print axioms GeocoqTranslate.Tarski.Base.l10_5_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_uniqueness_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_existence_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l10_7_c
#print axioms GeocoqTranslate.Tarski.Base.l10_8_c
#print axioms GeocoqTranslate.Tarski.Base.col__refl_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_col_cong_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_col_cong_c
#print axioms GeocoqTranslate.Tarski.Base.image_id_c
#print axioms GeocoqTranslate.Tarski.Base.osym_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_image_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_is_image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_gen_is_image_c
#print axioms GeocoqTranslate.Tarski.Base.image_image_in_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_col_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_rev_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_rev_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_per_c
#print axioms GeocoqTranslate.Tarski.Base.col__image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.image_triv_c
#print axioms GeocoqTranslate.Tarski.Base.cong_midpoint__image_c
#print axioms GeocoqTranslate.Tarski.Base.col_image_spec__eq_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec_triv_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec__eq_c
#print axioms GeocoqTranslate.Tarski.Base.image__midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_dec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_14_c
#print axioms GeocoqTranslate.Tarski.Base.l10_15_c
#print axioms GeocoqTranslate.Tarski.Base.ex_per_cong_c
#print axioms GeocoqTranslate.Tarski.Base.exists_cong_per_c
end GeocoqTranslate.Tarski.Base