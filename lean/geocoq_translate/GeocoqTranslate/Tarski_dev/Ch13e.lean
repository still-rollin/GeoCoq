import GeocoqTranslate.Tarski_dev.Ch13d

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_euclidean Tpoint]

theorem l13_10_aux1_c :
    ∀ (O A B P Q : Tpoint) (la lb lp lq : Tpoint → Tpoint → Prop), Col O A B → Col O P Q → Perp O P P A → Perp O Q Q B → Q_Cong la → Q_Cong lb → Q_Cong lp → Q_Cong lq → la O A → lb O B → lp O P → lq O Q → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a ∧ Lcos lp la a ∧ Lcos lq lb a := sorry
theorem l13_10_aux2_c :
    ∀ (O A B : Tpoint) (la lla lb llb : Tpoint → Tpoint → Prop), Col O A B → Q_Cong la → Q_Cong lla → Q_Cong lb → Q_Cong llb → la O A → lla O A → lb O B → llb O B → A ≠ O → B ≠ O → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a ∧ Lcos lla la a ∧ Lcos llb lb a := sorry
theorem l13_6_bis_c :
    ∀ (lp l1 l2 : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l1 a → Lcos lp l2 a → EqL l1 l2 := sorry
theorem lcos3_lcos2_c :
    ∀ (l1 l2 : Tpoint → Tpoint → Prop) (a b c d n : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos3 l1 a b n l2 c d n → Eq_Lcos2 l1 a b l2 c d := sorry
theorem lcos2_lcos_c :
    ∀ (l1 l2 : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos2 l1 a c l2 b c → Eq_Lcos l1 a l2 b := sorry
theorem lcos_per_anga_c :
    ∀ (O A P : Tpoint) (la lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp la a → la O A → lp O P → Per A P O → a A O P := sorry
theorem lcos_lcos_cop__col_c :
    ∀ (la lb lp : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop) (O A B P : Tpoint), Lcos lp la a → Lcos lp lb b → la O A → lb O B → lp O P → a A O P → b B O P → Coplanar O A B P → Col A B P := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  have H7 := lcos_lg_anga_c b0 b2 b3 b9
  have H8 := lcos_lg_anga_c b1 b2 b4 b10
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H7
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨_, H19⟩ := H18
  have H20 := lcos_per_c b5 b8 b6 b2 b0 b3 H19 H17 H13 H15 b11 b13 (anga_sym_c b3 b6 b5 b8 H19 b14)
  have H21 := lcos_per_c b5 b8 b7 b2 b1 b4 H14 H11 H13 H9 b12 b13 (anga_sym_c b4 b7 b5 b8 H14 b15)
  exact cop_per2__col_c b5 b6 b7 b8 b16 ((fun H22 => (by
  subst H22
  have HH := lcos_lg_not_null_c b2 b0 b3 H15
  obtain ⟨H24, _⟩ := HH
  exact H24 (⟨H13, (⟨b5, b13⟩)⟩)))) (l8_2_c b5 b8 b6 H20) (l8_2_c b5 b8 b7 H21)

theorem l13_10_aux3_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Bet A O B → Bet A' O B' := sorry

theorem l13_10_aux4_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Bet O A B → Out O A' B' := sorry

theorem l13_10_aux5_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Out O A B → Out O A' B' := sorry

theorem cop_per2__perp_c :
    ∀ (A B X Y : Tpoint), A ≠ B → X ≠ Y → (B ≠ X ∨ B ≠ Y) → Coplanar A B X Y → Per A B X → Per A B Y → Perp A B X Y := sorry
theorem l13_10_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Perp2 A B' B A' O := sorry

theorem cop_par__perp2_c :
    ∀ (A B C D P : Tpoint), Coplanar A B C P → Par A B C D → Perp2 A B C D P := sorry

theorem l13_11_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Par B C' C B' → Par C A' A C' → Par A B' B A' := sorry

theorem l13_14_c :
    ∀ (O A B C O' A' B' C' : Tpoint), Par_strict O A O' A' → Col O A B → Col O B C → Col O A C → Col O' A' B' → Col O' B' C' → Col O' A' C' → Par A C' A' C → Par B C' B' C → Par A B' A' B := sorry

#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux1_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux2_c
#print axioms GeocoqTranslate.Tarski.Base.l13_6_bis_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_lcos2_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_lcos_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_per_anga_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_lcos_cop__col_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux3_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux4_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux5_c
#print axioms GeocoqTranslate.Tarski.Base.cop_per2__perp_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_c
#print axioms GeocoqTranslate.Tarski.Base.cop_par__perp2_c
#print axioms GeocoqTranslate.Tarski.Base.l13_11_c
#print axioms GeocoqTranslate.Tarski.Base.l13_14_c
end GeocoqTranslate.Tarski.Base