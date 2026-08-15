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

theorem l13_10_aux3_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Bet A O B → Bet A' O B' := sorry

theorem l13_10_aux4_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Bet O A B → Out O A' B' := sorry

theorem l13_10_aux5_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Out O A B → Out O A' B' := sorry

theorem l13_10_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col O A A' → B ≠ O → C ≠ O → Col O A B → Col O B C → B' ≠ O → C' ≠ O → Col O A' B' → Col O B' C' → Perp2 B C' C B' O → Perp2 C A' A C' O → Perp2 A B' B A' O := sorry

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
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux3_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux4_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_aux5_c
#print axioms GeocoqTranslate.Tarski.Base.l13_10_c
#print axioms GeocoqTranslate.Tarski.Base.l13_11_c
#print axioms GeocoqTranslate.Tarski.Base.l13_14_c
end GeocoqTranslate.Tarski.Base