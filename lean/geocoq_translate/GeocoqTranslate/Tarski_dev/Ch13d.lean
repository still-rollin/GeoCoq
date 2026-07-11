import GeocoqTranslate.Tarski_dev.Ch13c

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l13_6_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (lc ld l : Tpoint → Tpoint → Prop), Lcos lc l a → Lcos ld l a → EqL lc ld := sorry
theorem null_lcos_eql_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → Q_CongA_Null_Acute a → EqL l lp := sorry
theorem eql_lcos_null_c :
    ∀ (l lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos l lp a → EqL l lp → Q_CongA_Null_Acute a := sorry
theorem lcos_lg_not_null_c :
    ∀ (l lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos l lp a → ¬ Q_Cong_Null l ∧ ¬ Q_Cong_Null lp := sorry
theorem perp_acute_out_c :
    ∀ (A B C C' : Tpoint), Acute A B C → Perp A B C C' → Col A B C' → Out B A C' :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  l6_6 (acute_col_perp__out_c b2 b1 b0 b3 (acute_sym_c b0 b1 b2 b4) ((by colr)) (perp_comm_c b0 b1 b3 b2 (perp_comm_c b1 b0 b2 b3 (perp_comm_c b0 b1 b3 b2 (perp_right_comm_c b0 b1 b2 b3 b5)))))

theorem perp_out__acute_c :
    ∀ (A B C C' : Tpoint), Perp A B C C' → Col A B C' → (Acute A B C ↔ Out B A C') :=
  fun b0 b1 b2 b3 b4 b5 =>
  ⟨(fun H1 => perp_acute_out_c b0 b1 b2 b3 H1 b4 b5), (fun H1 => perp_out_acute_c b0 b1 b2 b3 H1 b4)⟩

theorem obtuse_not_acute_c :
    ∀ (A B C : Tpoint), Obtuse A B C → ¬ Acute A B C := sorry
theorem acute_not_obtuse_c :
    ∀ (A B C : Tpoint), Acute A B C → ¬ Obtuse A B C :=
  fun b0 b1 b2 b3 =>
  (fun H0 => (let H1 := obtuse_not_acute_c b0 b1 b2 H0; ((H1 b3)).elim))

theorem perp_obtuse_bet_c :
    ∀ (A B C C' : Tpoint), Perp A B C C' → Col A B C' → Obtuse A B C → Bet A B C' := sorry
theorem lcos_const0_c :
    ∀ (l lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → Q_CongA_Null_Acute a → ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), l A B ∧ lp B C ∧ a A B C := by
  intro b0 b1 b2 b3 b4
  have HH := b3
  obtain ⟨_, H2⟩ := HH
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨A, H0⟩ := H6
  obtain ⟨B, H1⟩ := H0
  obtain ⟨C, H7⟩ := H1
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  exact ⟨C, (⟨A, (⟨B, (⟨(lg_sym_c b0 A C H3 H11), (⟨H9, (anga_sym_c b2 B A C H5 H12)⟩)⟩)⟩)⟩)⟩

theorem lcos_const1_c :
    ∀ (l lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (P : Tpoint), Lcos lp l a → ¬ Q_CongA_Null_Acute a → ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), ¬ Col A B P ∧ OS A B C P ∧ l A B ∧ lp B C ∧ a A B C := sorry
theorem lcos_const_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), lp A B ∧ l B C ∧ a A B C := by
  intro b0 b1 b2 b3
  obtain ⟨H0, H1⟩ := b3
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨A, H4⟩ := H3
  obtain ⟨B, H5⟩ := H4
  obtain ⟨C, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  exact ⟨B, (⟨A, (⟨C, (⟨(lg_sym_c b0 A B H0 H8), (⟨H10, H11⟩)⟩)⟩)⟩)⟩

theorem lcos_lg_distincts_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Lcos lp l a → l A B → lp B C → a A B C → A ≠ B ∧ C ≠ B := sorry
theorem lcos_const_a_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (B : Tpoint), Lcos lp l a → ∃ (A : Tpoint), ∃ (C : Tpoint), l A B ∧ lp B C ∧ a A B C := sorry
theorem lcos_const_ab_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (B A : Tpoint), Lcos lp l a → l A B → ∃ (C : Tpoint), lp B C ∧ a A B C := sorry
theorem lcos_const_cb_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (B C : Tpoint), Lcos lp l a → lp B C → ∃ (A : Tpoint), l A B ∧ a A B C := sorry
theorem lcos_lg_anga_c :
    ∀ (l lp : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → Lcos lp l a ∧ Q_Cong l ∧ Q_Cong lp ∧ Q_CongA_Acute a := by
  intro b0 b1 b2 b3
  exact ⟨b3, ((by
  obtain ⟨H0, H1⟩ := b3
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, _⟩ := H3
  exact ⟨H2, (⟨H0, H4⟩)⟩))⟩

theorem lcos_eql_lcos_c :
    ∀ (lp1 l1 lp2 l2 : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), EqL lp1 lp2 → EqL l1 l2 → Lcos lp1 l1 a → Lcos lp2 l2 a := sorry
theorem lcos_not_lg_null_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → ¬ Q_Cong_Null lp := sorry

theorem lcos_const_o_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (A B P : Tpoint), ¬ Col A B P → ¬ Q_CongA_Null_Acute a → Q_Cong l → Q_Cong lp → Q_CongA_Acute a → l A B → Lcos lp l a → ∃ (C : Tpoint), OS A B C P ∧ a A B C ∧ lp B C := sorry

theorem flat_not_acute_c :
    ∀ (A B C : Tpoint), Bet A B C → ¬ Acute A B C := sorry

theorem acute_comp_not_acute_c :
    ∀ (A B C D : Tpoint), Bet A B C → Acute A B D → ¬ Acute C B D := sorry

theorem lcos_per_c :
    ∀ (A B C : Tpoint) (lp l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_Cong l → Q_Cong lp → Lcos lp l a → l A C → lp A B → a B A C → Per A B C := sorry

theorem is_null_anga_dec_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_CongA_Null_Acute a ∨ ¬ Q_CongA_Null_Acute a := sorry

theorem lcos_lg_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (lp l : Tpoint → Tpoint → Prop) (A B C : Tpoint), Lcos lp l a → Perp A B B C → a B A C → l A C → lp A B := sorry

theorem l13_7_c :
    ∀ (a b : Tpoint → Tpoint → Tpoint → Prop) (l la lb lab lba : Tpoint → Tpoint → Prop), Lcos la l a → Lcos lb l b → Lcos lab la b → Lcos lba lb a → EqL lab lba := sorry

theorem out_acute_c :
    ∀ (A B C : Tpoint), Out B A C → Acute A B C := sorry

theorem perp_acute_c :
    ∀ (A B C P : Tpoint), Col A C P → Perp_at P B P A C → Acute A B P := sorry

theorem null_lcos_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Q_Cong l → ¬ Q_Cong_Null l → Q_CongA_Null_Acute a → Lcos l l a := sorry

theorem lcos_exists_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_Cong l → ¬ Q_Cong_Null l → ∃ (lp : Tpoint → Tpoint → Prop), Lcos lp l a := sorry

theorem lcos_uniqueness_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (l1 l2 : Tpoint → Tpoint → Prop), Lcos l1 l a → Lcos l2 l a → EqL l1 l2 := sorry

theorem lcos_eqa_lcos_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos lp l a → EqA a b → Lcos lp l b := sorry

theorem lcos_eq_refl_c :
    ∀ (la : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop), Q_Cong la → ¬ Q_Cong_Null la → Q_CongA_Acute a → Eq_Lcos la a la a := sorry

theorem lcos_eq_sym_c :
    ∀ (la : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (lb : Tpoint → Tpoint → Prop) (b : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos la a lb b → Eq_Lcos lb b la a := sorry

theorem lcos_eq_trans_c :
    ∀ (la : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) (lb : Tpoint → Tpoint → Prop) (b : Tpoint → Tpoint → Tpoint → Prop) (lc : Tpoint → Tpoint → Prop) (c : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos la a lb b → Eq_Lcos lb b lc c → Eq_Lcos la a lc c := sorry

theorem lcos2_comm_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos2 lp l a b → Lcos2 lp l b a := sorry

theorem lcos2_exists_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Q_Cong l → ¬ Q_Cong_Null l → Q_CongA_Acute a → Q_CongA_Acute b → ∃ (lp : Tpoint → Tpoint → Prop), Lcos2 lp l a b := sorry

theorem lcos2_eq_refl_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Q_Cong l → ¬ Q_Cong_Null l → Q_CongA_Acute a → Q_CongA_Acute b → Eq_Lcos2 l a b l a b := sorry

theorem lcos2_eq_sym_c :
    ∀ (l1 : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop) (l2 : Tpoint → Tpoint → Prop) (c d : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos2 l1 a b l2 c d → Eq_Lcos2 l2 c d l1 a b := sorry

theorem lcos2_uniqueness_c :
    ∀ (l l1 l2 : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos2 l1 l a b → Lcos2 l2 l a b → EqL l1 l2 := sorry

theorem lcos2_eql_lcos2_c :
    ∀ (lla llb la lb : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos2 la lla a b → EqL lla llb → EqL la lb → Lcos2 lb llb a b := sorry

theorem lcos2_lg_anga_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos2 lp l a b → Lcos2 lp l a b ∧ Q_Cong lp ∧ Q_Cong l ∧ Q_CongA_Acute a ∧ Q_CongA_Acute b := sorry

theorem lcos2_eq_trans_c :
    ∀ (l1 : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop) (l2 : Tpoint → Tpoint → Prop) (c d : Tpoint → Tpoint → Tpoint → Prop) (l3 : Tpoint → Tpoint → Prop) (e f : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos2 l1 a b l2 c d → Eq_Lcos2 l2 c d l3 e f → Eq_Lcos2 l1 a b l3 e f := sorry

theorem lcos_eq_lcos2_eq_c :
    ∀ (la lb : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute c → Eq_Lcos la a lb b → Eq_Lcos2 la a c lb b c := sorry

theorem lcos2_lg_not_null_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop), Lcos2 lp l a b → ¬ Q_Cong_Null l ∧ ¬ Q_Cong_Null lp := sorry

theorem lcos3_lcos_1_2_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c ↔ ∃ (la : Tpoint → Tpoint → Prop), Lcos la l a ∧ Lcos2 lp la b c := sorry

theorem lcos3_lcos_2_1_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c ↔ ∃ (lab : Tpoint → Tpoint → Prop), Lcos2 lab l a b ∧ Lcos lp lab c := sorry

theorem lcos3_permut3_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c → Lcos3 lp l b a c := sorry

theorem lcos3_permut1_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c → Lcos3 lp l a c b := sorry

theorem lcos3_permut2_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c → Lcos3 lp l c b a := sorry

theorem lcos3_exists_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Q_Cong l → ¬ Q_Cong_Null l → Q_CongA_Acute a → Q_CongA_Acute b → Q_CongA_Acute c → ∃ (lp : Tpoint → Tpoint → Prop), Lcos3 lp l a b c := sorry

theorem lcos3_eq_refl_c :
    ∀ (l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Q_Cong l → ¬ Q_Cong_Null l → Q_CongA_Acute a → Q_CongA_Acute b → Q_CongA_Acute c → Eq_Lcos3 l a b c l a b c := sorry

theorem lcos3_eq_sym_c :
    ∀ (l1 : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop) (l2 : Tpoint → Tpoint → Prop) (d e f : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos3 l1 a b c l2 d e f → Eq_Lcos3 l2 d e f l1 a b c := sorry

theorem lcos3_uniqueness_c :
    ∀ (l l1 l2 : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 l1 l a b c → Lcos3 l2 l a b c → EqL l1 l2 := sorry

theorem lcos3_eql_lcos3_c :
    ∀ (lla llb la lb : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 la lla a b c → EqL lla llb → EqL la lb → Lcos3 lb llb a b c := sorry

theorem lcos3_lg_anga_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c → Lcos3 lp l a b c ∧ Q_Cong lp ∧ Q_Cong l ∧ Q_CongA_Acute a ∧ Q_CongA_Acute b ∧ Q_CongA_Acute c := sorry

theorem lcos3_lg_not_null_c :
    ∀ (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop), Lcos3 lp l a b c → ¬ Q_Cong_Null l ∧ ¬ Q_Cong_Null lp := sorry

theorem lcos3_eq_trans_c :
    ∀ (l1 : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop) (l2 : Tpoint → Tpoint → Prop) (d e f : Tpoint → Tpoint → Tpoint → Prop) (l3 : Tpoint → Tpoint → Prop) (g h i : Tpoint → Tpoint → Tpoint → Prop), Eq_Lcos3 l1 a b c l2 d e f → Eq_Lcos3 l2 d e f l3 g h i → Eq_Lcos3 l1 a b c l3 g h i := sorry

theorem lcos_eq_lcos3_eq_c :
    ∀ (la lb : Tpoint → Tpoint → Prop) (a b c d : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute c → Q_CongA_Acute d → Eq_Lcos la a lb b → Eq_Lcos3 la a c d lb b c d := sorry

theorem lcos2_eq_lcos3_eq_c :
    ∀ (la lb : Tpoint → Tpoint → Prop) (a b c d e : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute e → Eq_Lcos2 la a b lb c d → Eq_Lcos3 la a b e lb c d e := sorry

#print axioms GeocoqTranslate.Tarski.Base.l13_6_c
#print axioms GeocoqTranslate.Tarski.Base.null_lcos_eql_c
#print axioms GeocoqTranslate.Tarski.Base.eql_lcos_null_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_lg_not_null_c
#print axioms GeocoqTranslate.Tarski.Base.perp_acute_out_c
#print axioms GeocoqTranslate.Tarski.Base.perp_out__acute_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_not_acute_c
#print axioms GeocoqTranslate.Tarski.Base.acute_not_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.perp_obtuse_bet_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const0_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const1_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_lg_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const_a_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const_ab_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const_cb_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_lg_anga_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eql_lcos_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_not_lg_null_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_const_o_c
#print axioms GeocoqTranslate.Tarski.Base.flat_not_acute_c
#print axioms GeocoqTranslate.Tarski.Base.acute_comp_not_acute_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_per_c
#print axioms GeocoqTranslate.Tarski.Base.is_null_anga_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_lg_c
#print axioms GeocoqTranslate.Tarski.Base.l13_7_c
#print axioms GeocoqTranslate.Tarski.Base.out_acute_c
#print axioms GeocoqTranslate.Tarski.Base.perp_acute_c
#print axioms GeocoqTranslate.Tarski.Base.null_lcos_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eqa_lcos_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eq_refl_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eq_sym_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eq_trans_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_eq_refl_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_eq_sym_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_eql_lcos2_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_lg_anga_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_eq_trans_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eq_lcos2_eq_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_lg_not_null_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_lcos_1_2_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_lcos_2_1_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_permut3_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_permut1_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_permut2_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_eq_refl_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_eq_sym_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_eql_lcos3_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_lg_anga_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_lg_not_null_c
#print axioms GeocoqTranslate.Tarski.Base.lcos3_eq_trans_c
#print axioms GeocoqTranslate.Tarski.Base.lcos_eq_lcos3_eq_c
#print axioms GeocoqTranslate.Tarski.Base.lcos2_eq_lcos3_eq_c
end GeocoqTranslate.Tarski.Base