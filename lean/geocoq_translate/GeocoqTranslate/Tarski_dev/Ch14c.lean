import GeocoqTranslate.Tarski_dev.Ch14b

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

theorem l14_36_a_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Out O A B → Bet O A C := sorry

theorem l14_36_b_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Out O A B → O ≠ A ∧ O ≠ C ∧ A ≠ C := sorry

theorem O_not_positive_c :
    ∀ (O E : Tpoint), ¬ Ps O E O := by
  intro b0 b1
  intro H
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  rcases H2 with _ | _
  · have H3 := (let H3 := rfl; H0 H3)
    exact (H3).elim
  · have H3 := (let H3 := rfl; H0 H3)
    exact (H3).elim
theorem pos_null_neg_c :
    ∀ (O E E' A MA : Tpoint), Opp O E E' A MA → Ps O E A ∨ O = A ∨ Ps O E MA := sorry

theorem sum_pos_pos_c :
    ∀ (O E E' A B AB : Tpoint), Ps O E A → Ps O E B → Sum O E E' A B AB → Ps O E AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have H2 := (let H2 := l6_6 b7; l6_7_c b0 b3 b1 b4 b6 H2)
  have HH := l14_36_b_c b0 b1 b2 b3 b4 b5 b8 H2
  obtain ⟨H3, H4⟩ := HH
  obtain ⟨_, _⟩ := H4
  have HH0 := l14_36_a_c b0 b1 b2 b3 b4 b5 b8 H2
  have H5 := l6_6 b6
  have H6 := bet_out (Ne.symm H3) HH0
  have HP := l6_7_c b0 b1 b3 b5 H5 H6
  exact l6_6 HP
theorem prod_pos_pos_c :
    ∀ (O E E' A B AB : Tpoint), Ps O E A → Ps O E B → Prod O E E' A B AB → Ps O E AB := sorry

theorem pos_not_neg_c :
    ∀ (O E A : Tpoint), Ps O E A → ¬ Ng O E A := by
  intro b0 b1 b2 b3
  intro H0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := b3
  obtain ⟨_, H6⟩ := H5
  rcases H6 with H7 | H7
  · exact H4 (between_equality H3 H7)
  · exact H2 (between_equality (between_symmetry H3) H7)
theorem neg_not_pos_c :
    ∀ (O E A : Tpoint), Ng O E A → ¬ Ps O E A := by
  intro b0 b1 b2 b3
  intro H0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := b3
  obtain ⟨_, H6⟩ := H5
  rcases H4 with H7 | H7
  · exact H1 (between_equality H6 H7)
  · exact H3 (between_equality (between_symmetry H6) H7)
theorem opp_pos_neg_c :
    ∀ (O E E' A MA : Tpoint), Ps O E A → Opp O E E' A MA → Ng O E MA := sorry

theorem opp_neg_pos_c :
    ∀ (O E E' A MA : Tpoint), Ng O E A → Opp O E E' A MA → Ps O E MA := sorry

theorem ltP_ar2_c :
    ∀ (O E E' A B : Tpoint), LtP O E E' A B → Ar2 O E E' A B A := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨D, H0⟩ := b5
  obtain ⟨H1, _⟩ := H0
  have H2 := diff_ar2_c b0 b1 b2 b4 b3 D H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, _⟩ := H6
  exact ⟨H3, (⟨H7, (⟨H5, H7⟩)⟩)⟩
theorem ltP_neq_c :
    ∀ (O E E' A B : Tpoint), LtP O E E' A B → A ≠ B := by
  intro b0 b1 b2 b3 b4 b5
  have HH := ltP_ar2_c b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := HH
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  intro H5
  subst H5
  obtain ⟨OO, H7⟩ := b5
  obtain ⟨H8, H9⟩ := H7
  have H10 := diff_uniqueness_c b0 b1 b2 b3 b3 OO b0 H8 (diff_null_c b0 b1 b2 b3 H0 H4)
  subst H10
  obtain ⟨H12, H13⟩ := H9
  obtain ⟨_, H14⟩ := H13
  rcases H14 with _ | _
  · have H15 := (let H15 := rfl; H12 H15)
    exact (H15).elim
  · have H15 := (let H15 := rfl; H12 H15)
    exact (H15).elim
theorem leP_refl_c :
    ∀ (O E E' A : Tpoint), LeP O E E' A A :=
  fun b0 b1 b2 b3 =>
  Or.inr rfl
theorem ltP_sum_pos_c :
    ∀ (O E E' A B C : Tpoint), Ps O E B → Sum O E E' A B C → LtP O E E' A C :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b4, (⟨((let H1 := sum_diff_c b0 b1 b2 b3 b4 b5 b7; H1)), b6⟩)⟩
theorem pos_opp_neg_c :
    ∀ (O E E' A mA : Tpoint), Ps O E A → Opp O E E' A mA → Ng O E mA := sorry

theorem diff_pos_diff_neg_c :
    ∀ (O E E' A B AmB BmA : Tpoint), Diff O E E' A B AmB → Diff O E E' B A BmA → Ps O E AmB → Ng O E BmA :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  (let H2 := diff_opp_c b0 b1 b2 b3 b4 b5 b6 b7 b8; pos_opp_neg_c b0 b1 b2 b5 b6 b9 H2)
theorem not_pos_and_neg_c :
    ∀ (O E A : Tpoint), ¬ (Ps O E A ∧ Ng O E A) := by
  intro b0 b1 b2
  intro H
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H0
  obtain ⟨H6, H7⟩ := H5
  rcases H7 with H8 | H8
  · exact H4 (between_equality H3 H8)
  · exact H6 (between_equality (between_symmetry H3) H8)
theorem leP_asym_c :
    ∀ (O E E' A B : Tpoint), LeP O E E' A B → LeP O E E' B A → A = B := by
  intro b0 b1 b2 b3 b4 b5 b6
  rcases b5 with H1 | H1
  · rcases b6 with H2 | H2
    · obtain ⟨BmA, H3⟩ := H1
      obtain ⟨H4, H5⟩ := H3
      obtain ⟨AmB, H6⟩ := H2
      obtain ⟨H7, H8⟩ := H6
      have HH := diff_pos_diff_neg_c b0 b1 b2 b3 b4 AmB BmA H7 H4 H8
      have HT := diff_pos_diff_neg_c b0 b1 b2 b4 b3 BmA AmB H4 H7 H5
      exact (((let HN := not_pos_and_neg_c b0 b1 AmB; HN (⟨H8, HT⟩)))).elim
    · exact Eq.symm H2
  · rcases b6 with _ | _
    · exact H1
    · exact H1
theorem leP_trans_c :
    ∀ (O E E' A B C : Tpoint), LeP O E E' A B → LeP O E E' B C → LeP O E E' A C := sorry

theorem leP_sum_leP_c :
    ∀ (O E E' A B C X Y Z : Tpoint), LeP O E E' A X → LeP O E E' B Y → Sum O E E' A B C → Sum O E E' X Y Z → LeP O E E' C Z := sorry

theorem square_pos_c :
    ∀ (O E E' A A2 : Tpoint), O ≠ A → Prod O E E' A A A2 → Ps O E A2 := sorry

theorem col_pos_or_neg_c :
    ∀ (O E X : Tpoint), O ≠ E → O ≠ X → Col O E X → Ps O E X ∨ Ng O E X := by
  intro b0 b1 b2 b3 b4 b5
  rcases b5 with H | H
  · exact Or.inl (⟨((fun H0 => b4 (Eq.symm H0))), (⟨((fun H0 => b3 (Eq.symm H0))), (Or.inr H)⟩)⟩)
  · rcases H with H0 | H0
    · exact Or.inl (⟨((fun H1 => b4 (Eq.symm H1))), (⟨((fun H1 => b3 (Eq.symm H1))), (Or.inl (between_symmetry H0))⟩)⟩)
    · exact Or.inr (⟨((fun H1 => b4 (Eq.symm H1))), (⟨((fun H1 => b3 (Eq.symm H1))), H0⟩)⟩)
theorem ltP_neg_c :
    ∀ (O E E' A : Tpoint), LtP O E E' A O → Ng O E A := sorry

theorem ps_le_c :
    ∀ (O E E' X : Tpoint), ¬ Col O E E' → Bet O X E ∨ Bet O E X → LeP O E E' O X := sorry

theorem lt_diff_ps_c :
    ∀ (O E E' X Y XMY : Tpoint), Col O E X → Col O E Y → LtP O E E' Y X → Diff O E E' X Y XMY → Ps O E XMY := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := b8
  obtain ⟨x1, x2⟩ := x0
  have HDiff0 := diff_uniqueness_c b0 b1 b2 b3 b4 b5 x b9 x1
  subst HDiff0
  exact x2
theorem col_2_le_or_ge_c :
    ∀ (O E E' A B : Tpoint), ¬ Col O E E' → Col O E A → Col O E B → LeP O E E' A B ∨ LeP O E E' B A := sorry

theorem compatibility_of_sum_with_order_c :
    ∀ (O E E' A B C APC BPC : Tpoint), LeP O E E' A B → Sum O E E' A C APC → Sum O E E' B C BPC → LeP O E E' APC BPC := sorry

theorem compatibility_of_prod_with_order_c :
    ∀ (O E E' A B AB : Tpoint), LeP O E E' O A → LeP O E E' O B → Prod O E E' A B AB → LeP O E E' O AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  rcases b6 with HLeA0 | HLeA0
  · rcases b7 with HLeB0 | HLeB0
    · have HNC := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  exact H0)
      have HColA := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact H2)
      have HColB := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact H3)
      have HColAB := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  exact H3)
      exact Or.inl (⟨b5, (⟨(diff_A_O_c b0 b1 b2 b5 HNC HColAB), (by
  obtain ⟨x, x0⟩ := HLeA0
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := HLeB0
  obtain ⟨x5, x6⟩ := x4
  have H1 := diff_uniqueness_c b0 b1 b2 b3 b0 b3 x (diff_A_O_c b0 b1 b2 b3 HNC HColA) x1
  have H2 := diff_uniqueness_c b0 b1 b2 b4 b0 b4 x3 (diff_A_O_c b0 b1 b2 b4 HNC HColB) x5
  subst H2
  subst H1
  exact prod_pos_pos_c b0 b1 b2 b3 b4 b5 x2 x6 b8)⟩)⟩)
    · subst HLeB0
      have HAB1 := prod_O_r_eq_c b0 b1 b2 b3 b5 b8
      subst HAB1
      exact leP_refl_c b5 b1 b2 b5
  · rcases b7 with HLeB0 | HLeB0
    · subst HLeA0
      have HAB1 := prod_O_l_eq_c b0 b1 b2 b4 b5 b8
      subst HAB1
      exact leP_refl_c b5 b1 b2 b5
    · subst HLeB0
      subst HLeA0
      have HAB2 := prod_O_l_eq_c b0 b1 b2 b0 b5 b8
      subst HAB2
      exact leP_refl_c b5 b1 b2 b5
theorem pos_inv_pos_c :
    ∀ (O E E' A IA : Tpoint), O ≠ A → LeP O E E' O A → Prod O E E' IA A E → LeP O E E' O IA := sorry

theorem le_pos_prod_le_c :
    ∀ (O E E' A B C AC BC : Tpoint), LeP O E E' A B → LeP O E E' O C → Prod O E E' A C AC → Prod O E E' B C BC → LeP O E E' AC BC := sorry

theorem bet_lt12_le23_c :
    ∀ (O E E' A B C : Tpoint), Bet A B C → LtP O E E' A B → LeP O E E' B C := sorry

theorem bet_lt12_le13_c :
    ∀ (O E E' A B C : Tpoint), Bet A B C → LtP O E E' A B → LeP O E E' A C :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  leP_trans_c b0 b1 b2 b3 b4 b5 (Or.inl b7) (bet_lt12_le23_c b0 b1 b2 b3 b4 b5 b6 b7)
theorem bet_lt21_le32_c :
    ∀ (O E E' A B C : Tpoint), Bet A B C → LtP O E E' B A → LeP O E E' C B := sorry

theorem bet_lt21_le31_c :
    ∀ (O E E' A B C : Tpoint), Bet A B C → LtP O E E' B A → LeP O E E' C A :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  leP_trans_c b0 b1 b2 b5 b4 b3 (bet_lt21_le32_c b0 b1 b2 b3 b4 b5 b6 b7) (Or.inl b7)
theorem opp_2_le_le_c :
    ∀ (O E E' A MA B MB : Tpoint), Opp O E E' A MA → Opp O E E' B MB → LeP O E E' A B → LeP O E E' MB MA := sorry

theorem diff_2_le_le_c :
    ∀ (O E E' A B C AMC BMC : Tpoint), Diff O E E' A C AMC → Diff O E E' B C BMC → LeP O E E' A B → LeP O E E' AMC BMC := sorry

#print axioms GeocoqTranslate.Tarski.Base.l14_36_a_c
#print axioms GeocoqTranslate.Tarski.Base.l14_36_b_c
#print axioms GeocoqTranslate.Tarski.Base.O_not_positive_c
#print axioms GeocoqTranslate.Tarski.Base.pos_null_neg_c
#print axioms GeocoqTranslate.Tarski.Base.sum_pos_pos_c
#print axioms GeocoqTranslate.Tarski.Base.prod_pos_pos_c
#print axioms GeocoqTranslate.Tarski.Base.pos_not_neg_c
#print axioms GeocoqTranslate.Tarski.Base.neg_not_pos_c
#print axioms GeocoqTranslate.Tarski.Base.opp_pos_neg_c
#print axioms GeocoqTranslate.Tarski.Base.opp_neg_pos_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_ar2_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_neq_c
#print axioms GeocoqTranslate.Tarski.Base.leP_refl_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_sum_pos_c
#print axioms GeocoqTranslate.Tarski.Base.pos_opp_neg_c
#print axioms GeocoqTranslate.Tarski.Base.diff_pos_diff_neg_c
#print axioms GeocoqTranslate.Tarski.Base.not_pos_and_neg_c
#print axioms GeocoqTranslate.Tarski.Base.leP_asym_c
#print axioms GeocoqTranslate.Tarski.Base.leP_trans_c
#print axioms GeocoqTranslate.Tarski.Base.leP_sum_leP_c
#print axioms GeocoqTranslate.Tarski.Base.square_pos_c
#print axioms GeocoqTranslate.Tarski.Base.col_pos_or_neg_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_neg_c
#print axioms GeocoqTranslate.Tarski.Base.ps_le_c
#print axioms GeocoqTranslate.Tarski.Base.lt_diff_ps_c
#print axioms GeocoqTranslate.Tarski.Base.col_2_le_or_ge_c
#print axioms GeocoqTranslate.Tarski.Base.compatibility_of_sum_with_order_c
#print axioms GeocoqTranslate.Tarski.Base.compatibility_of_prod_with_order_c
#print axioms GeocoqTranslate.Tarski.Base.pos_inv_pos_c
#print axioms GeocoqTranslate.Tarski.Base.le_pos_prod_le_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lt12_le23_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lt12_le13_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lt21_le32_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lt21_le31_c
#print axioms GeocoqTranslate.Tarski.Base.opp_2_le_le_c
#print axioms GeocoqTranslate.Tarski.Base.diff_2_le_le_c
end GeocoqTranslate.Tarski.Base