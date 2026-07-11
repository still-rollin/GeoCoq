import GeocoqTranslate.Tarski_dev.Ch14b

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

theorem l14_36_a_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Out O A B → Bet O A C := sorry

theorem l14_36_b_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Out O A B → O ≠ A ∧ O ≠ C ∧ A ≠ C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have HH := l14_36_a_c b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨H3, H4⟩ := H2
  exact ⟨(Ne.symm H1), (⟨((fun H5 => (by
  subst H5
  have HH1 := between_identity b0 b3 HH
  subst HH1
  rcases H4 with _ | _
  · have H9 := (let H9 := rfl; H1 H9)
    exact (H9).elim
  · have H9 := (let H9 := rfl; H1 H9)
    exact (H9).elim))), ((fun H5 => (by
  subst H5
  have HS := b6
  obtain ⟨H7, _⟩ := b6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨_, H11⟩ := H10
  have H12 := sum_A_O_c b3 H11
  have H13 := sum_uniquenessB_c b3 b4 b0 b3 HS H12
  exact ((H3 H13)).elim)))⟩)⟩
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
    ∀ (O E E' A MA : Tpoint), Opp O E E' A MA → Ps O E A ∨ O = A ∨ Ps O E MA := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b3 b0
  rcases o with H0 | H0
  · exact Or.inr (Or.inl (Eq.symm H0))
  · have HS := b5
    obtain ⟨H1, H2⟩ := b5
    obtain ⟨H3, H4⟩ := H1
    obtain ⟨H5, H6⟩ := H4
    obtain ⟨H7, _⟩ := H6
    have H8 := sum_cong_c b4 b3 b0 HS (Or.inr ((fun H8 => (let H9 := H0 H8; (H9).elim))))
    obtain ⟨H9, H10⟩ := H8
    obtain ⟨H11, H12⟩ := H10
    obtain ⟨H13, H14⟩ := H12
    obtain ⟨H15, H16⟩ := H14
    have HG := grid_not_par_c
    obtain ⟨_, H17⟩ := HG
    obtain ⟨_, H18⟩ := H17
    obtain ⟨_, H19⟩ := H18
    obtain ⟨H20, H21⟩ := H19
    obtain ⟨_, _⟩ := H21
    have H22 := l7_20_c b0 b3 b4 ((by colr)) H15
    rcases H22 with H23 | H23
    · subst H23
      rcases H16 with H25 | H25
      · have H26 := (let H26 := rfl; H25 H26)
        exact (H26).elim
      · have H26 := (let H26 := rfl; H25 H26)
        exact (H26).elim
    · have o0 := out_dec_c b0 b1 b3
      rcases o0 with H24 | H24
      · exact Or.inl (l6_6 H24)
      · exact Or.inr (Or.inr ((let H25 := (fun H25 => (by
  subst H25
  have H32 := is_midpoint_id_2_c b0 b3 H23
  subst H32
  rcases H16 with H35 | H35
  · have H36 := (let H36 := rfl; H0 H36)
    have H38 := (let H38 := rfl; H35 H38)
    exact (H36).elim
  · have H36 := (let H36 := rfl; H0 H36)
    have H38 := (let H38 := rfl; H35 H38)
    exact (H36).elim)); (by
  obtain ⟨H26, _⟩ := H23
  rcases H5 with H27 | H27
  · exact ⟨H25, (⟨(Ne.symm H20), (Or.inr H27)⟩)⟩
  · rcases H27 with H28 | H28
    · exact ⟨H25, (⟨(Ne.symm H20), (Or.inl (between_symmetry H28))⟩)⟩
    · exact ((H24 (⟨(Ne.symm H20), (⟨H0, ((let H29 := between_symmetry H26; (let HH := l5_2 H25 H29 H28; (by
  rcases H16 with H30 | _
  · rcases HH with _ | _
    · have H31 := (let H31 := rfl; H30 H31)
      exact (H31).elim
    · have H31 := (let H31 := rfl; H30 H31)
      exact (H31).elim
  · rcases HH with H30 | H30
    · exact Or.inr H30
    · exact Or.inl H30))))⟩)⟩))).elim))))
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
    ∀ (O E E' A MA : Tpoint), Ps O E A → Opp O E E' A MA → Ng O E MA := by
  intro b0 b1 b2 b3 b4 b5 b6
  have HH := opp_midpoint_c b0 b1 b2 b3 b4 b6
  obtain ⟨H1, H2⟩ := HH
  obtain ⟨H3, H4⟩ := b5
  obtain ⟨H5, H6⟩ := H4
  exact ⟨((fun H7 => (by
  subst H7
  have H9 := cong_identity b3 b0 b0 H2
  exact ((H3 H9)).elim))), (⟨H5, ((by
  rcases H6 with H7 | H7
  · exact outer_transitivity_between (between_symmetry H1) H7 (Ne.symm H3)
  · exact between_inner_transitivity (between_symmetry H1) H7))⟩)⟩
theorem opp_neg_pos_c :
    ∀ (O E E' A MA : Tpoint), Ng O E A → Opp O E E' A MA → Ps O E MA := by
  intro b0 b1 b2 b3 b4 b5 b6
  have HH := opp_midpoint_c b0 b1 b2 b3 b4 b6
  obtain ⟨H1, H2⟩ := HH
  obtain ⟨H3, H4⟩ := b5
  obtain ⟨H5, H6⟩ := H4
  exact l6_6 (⟨H5, (⟨((fun H7 => (by
  subst H7
  have H9 := cong_identity b3 b0 b0 H2
  exact ((H3 H9)).elim))), (l5_2 H3 H6 H1)⟩)⟩)
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
    ∀ (O E E' A mA : Tpoint), Ps O E A → Opp O E E' A mA → Ng O E mA := by
  intro b0 b1 b2 b3 b4 b5 b6
  have H1 := sum_ar2_c b0 b1 b2 b4 b3 b0 b6
  have H2 := opp_midpoint_c b0 b1 b2 b3 b4 b6
  obtain ⟨_, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, _⟩ := H5
  obtain ⟨H6, H7⟩ := H2
  obtain ⟨H8, H9⟩ := b5
  obtain ⟨H10, H11⟩ := H9
  exact ⟨((fun H12 => (by
  subst H12
  exact H8 ((let H14 := cong_identity b3 b0 b0 H7; H14))))), (⟨H10, ((by
  rcases H11 with H12 | H12
  · exact outer_transitivity_between (between_symmetry H6) H12 (Ne.symm H8)
  · exact between_symmetry (between_exchange3 (between_symmetry H12) H6)))⟩)⟩
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
    ∀ (O E E' A B C : Tpoint), LeP O E E' A B → LeP O E E' B C → LeP O E E' A C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b6 with H1 | H1
  · rcases b7 with H2 | H2
    · exact Or.inl ((by
  obtain ⟨dBA, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨dCB, H6⟩ := H2
  obtain ⟨H7, H8⟩ := H6
  have H9 := diff_ar2_c b0 b1 b2 b4 b3 dBA H4
  have H10 := diff_ar2_c b0 b1 b2 b5 b4 dCB H7
  obtain ⟨_, H11⟩ := H10
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H12
  obtain ⟨H14, H15⟩ := H9
  obtain ⟨_, H16⟩ := H15
  obtain ⟨_, H17⟩ := H16
  have HH := sum_exists_c dBA dCB H17 H13
  obtain ⟨dCA, H18⟩ := HH
  exact ⟨dCA, ((let HH0 := sum_diff_diff_b_c b0 b1 b2 b3 b4 b5 dBA dCB dCA H4 H7; ⟨(HH0 (sum_comm_c dBA dCB dCA H18)), (sum_pos_pos_c b0 b1 b2 dBA dCB dCA H5 H8 H18)⟩))⟩))
    · subst H2
      exact Or.inl H1
  · rcases b7 with H2 | H2
    · subst H1
      exact Or.inl H2
    · subst H2
      subst H1
      exact Or.inr rfl
theorem leP_sum_leP_c :
    ∀ (O E E' A B C X Y Z : Tpoint), LeP O E E' A X → LeP O E E' B Y → Sum O E E' A B C → Sum O E E' X Y Z → LeP O E E' C Z := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  have H3 := sum_ar2_c b0 b1 b2 b3 b4 b5 b11
  have H4 := sum_ar2_c b0 b1 b2 b6 b7 b8 b12
  obtain ⟨_, H5⟩ := H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H3
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H12
  rcases b9 with H14 | H14
  · rcases b10 with H15 | H15
    · obtain ⟨dXA, H16⟩ := H14
      obtain ⟨H17, H18⟩ := H16
      obtain ⟨dYB, H19⟩ := H15
      obtain ⟨H20, H21⟩ := H19
      have HH := diff_exists_c b0 b1 b2 b8 b5 H10 H9 H13
      obtain ⟨dZC, H22⟩ := HH
      exact Or.inl (⟨dZC, (⟨H22, ((let H23 := sum_diff2_diff_sum2_b_c b0 b1 b2 b3 b4 b5 b6 b7 b8 dXA dYB dZC b11 b12 H17 H20 H22; sum_pos_pos_c b0 b1 b2 dXA dYB dZC H18 H21 H23))⟩)⟩)
    · subst H15
      exact Or.inl ((by
  obtain ⟨dXA, H18⟩ := H14
  obtain ⟨H19, H20⟩ := H18
  have HH := diff_exists_c b0 b1 b2 b8 b5 H10 H9 H13
  obtain ⟨dZC, H21⟩ := HH
  exact ⟨dZC, (⟨H21, ((let H22 := sum_diff2_diff_sum2_b_c b0 b1 b2 b3 b4 b5 b6 b4 b8 dXA b0 dZC b11 b12 H19 (diff_null_c b0 b1 b2 b4 H10 H8) H21; (let H23 := sum_A_O_eq_c dXA dZC H22; (by
  subst H23
  exact H20))))⟩)⟩))
  · rcases b10 with H15 | H15
    · subst H14
      exact Or.inl ((by
  obtain ⟨dYB, H18⟩ := H15
  obtain ⟨H19, H20⟩ := H18
  have HH := diff_exists_c b0 b1 b2 b8 b5 H10 H9 H13
  obtain ⟨dZC, H21⟩ := HH
  exact ⟨dZC, (⟨H21, ((let H22 := sum_diff2_diff_sum2_b_c b0 b1 b2 b3 b4 b5 b3 b7 b8 b0 dYB dZC b11 b12 (diff_null_c b0 b1 b2 b3 H10 H6) H19 H21; (let H23 := sum_O_B_eq_c dYB dZC H22; (by
  subst H23
  exact H20))))⟩)⟩))
    · subst H14
      subst H15
      exact Or.inr (sum_uniqueness_c b3 b4 b5 b8 b11 b12)
theorem square_pos_c :
    ∀ (O E E' A A2 : Tpoint), O ≠ A → Prod O E E' A A A2 → Ps O E A2 := by
  intro b0 b1 b2 b3 b4 b5 b6
  have HNC := (by
  obtain ⟨H, _⟩ := b6
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  exact H0)
  have HColA := (by
  obtain ⟨H, _⟩ := b6
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact H3)
  have e := opp_exists_c b3 HColA
  obtain ⟨x, x0⟩ := e
  have HElim := x0
  have HElim0 := pos_null_neg_c b0 b1 b2 b3 x HElim
  rcases HElim0 with HElim1 | HElim1
  · exact prod_pos_pos_c b0 b1 b2 b3 b3 b4 HElim1 HElim1 b6
  · rcases HElim1 with HPs | HPs
    · have H := b5 HPs
      exact (H).elim
    · exact prod_pos_pos_c b0 b1 b2 x x b4 HPs HPs ((let e0 := opp_exists_c b1 ((by colr)); (by
  obtain ⟨x1, x2⟩ := e0
  exact prod_assoc1_c b1 b2 b3 x1 x x b3 b4 (opp_prod_c b0 b1 b2 x1 b3 x x2 x0) (prod_comm_c b0 b1 b2 x x1 b3 (opp_prod_c b0 b1 b2 x1 x b3 x2 (opp_comm_c b3 x x0))) b6)))
theorem col_pos_or_neg_c :
    ∀ (O E X : Tpoint), O ≠ E → O ≠ X → Col O E X → Ps O E X ∨ Ng O E X := by
  intro b0 b1 b2 b3 b4 b5
  rcases b5 with H | H
  · exact Or.inl (⟨((fun H0 => b4 (Eq.symm H0))), (⟨((fun H0 => b3 (Eq.symm H0))), (Or.inr H)⟩)⟩)
  · rcases H with H0 | H0
    · exact Or.inl (⟨((fun H1 => b4 (Eq.symm H1))), (⟨((fun H1 => b3 (Eq.symm H1))), (Or.inl (between_symmetry H0))⟩)⟩)
    · exact Or.inr (⟨((fun H1 => b4 (Eq.symm H1))), (⟨((fun H1 => b3 (Eq.symm H1))), H0⟩)⟩)
theorem ltP_neg_c :
    ∀ (O E E' A : Tpoint), LtP O E E' A O → Ng O E A := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  exact opp_pos_neg_c b0 b1 b2 x b3 x2 (diff_O_A_opp_c b0 b1 b2 x b3 (sum_diff_c b0 b1 b2 x b3 b0 (sum_comm_c b3 x b0 (diff_sum_c b0 b1 b2 b3 x b0 x1))))
theorem ps_le_c :
    ∀ (O E E' X : Tpoint), ¬ Col O E E' → Bet O X E ∨ Bet O E X → LeP O E E' O X := by
  intro b0 b1 b2 b3 b4 b5
  rcases (point_equality_decidability b0 b3) with HOX | HOX
  · exact Or.inr HOX
  · exact Or.inl (⟨b3, (⟨(diff_A_O_c b0 b1 b2 b3 ((by
  rcases b5 with _ | _
  · exact b4
  · exact b4)) ((by
  rcases b5 with H | H
  · exact (by colr)
  · exact bet_col_c b0 b1 b3 H))), ((let H := not_col_distincts_c b0 b1 b2 b4; (let H0 := H; (by
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact ⟨(Ne.symm HOX), (⟨(Ne.symm H2), b5⟩)⟩))))⟩)⟩)
theorem lt_diff_ps_c :
    ∀ (O E E' X Y XMY : Tpoint), Col O E X → Col O E Y → LtP O E E' Y X → Diff O E E' X Y XMY → Ps O E XMY := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := b8
  obtain ⟨x1, x2⟩ := x0
  have HDiff0 := diff_uniqueness_c b0 b1 b2 b3 b4 b5 x b9 x1
  subst HDiff0
  exact x2
theorem col_2_le_or_ge_c :
    ∀ (O E E' A B : Tpoint), ¬ Col O E E' → Col O E A → Col O E B → LeP O E E' A B ∨ LeP O E E' B A := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have HDiff1 := (let H := not_col_distincts_c b0 b1 b2 b5; (let H0 := H; (by
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact H2)))
  rcases (point_equality_decidability b3 b4) with HDiff2 | HDiff2
  · subst HDiff2
    exact Or.inl (Or.inr rfl)
  · have e := diff_exists_c b0 b1 b2 b4 b3 b5 b7 b6
    obtain ⟨x, x0⟩ := e
    have HColD := (let HD0 := diff_ar2_c b0 b1 b2 b4 b3 x x0; (by
  obtain ⟨_, H0⟩ := HD0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact H2))
    have HDiff3 := (fun H => (by
  subst H
  have HD1 := diff_null_eq_c b0 b1 b2 b4 b3 x0
  exact HDiff2 (Eq.symm HD1)))
    have HColD0 := col_pos_or_neg_c b0 b1 x HDiff1 HDiff3 HColD
    rcases HColD0 with HNgD | HNgD
    · exact Or.inl (Or.inl (⟨x, (⟨x0, HNgD⟩)⟩))
    · have e0 := diff_exists_c b0 b1 b2 b3 b4 b5 b6 b7
      obtain ⟨x1, x2⟩ := e0
      exact Or.inr (Or.inl (⟨x1, (⟨x2, (opp_neg_pos_c b0 b1 b2 x x1 HNgD (diff_opp_c b0 b1 b2 b4 b3 x x1 x0 x2))⟩)⟩))
theorem compatibility_of_sum_with_order_c :
    ∀ (O E E' A B C APC BPC : Tpoint), LeP O E E' A B → Sum O E E' A C APC → Sum O E E' B C BPC → LeP O E E' APC BPC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  rcases b8 with HLe0 | HLe0
  · exact Or.inl (by
  obtain ⟨x, x0⟩ := HLe0
  obtain ⟨x1, x2⟩ := x0
  exact ⟨x, (⟨((let HNC := (let HDiff0 := diff_ar2_c b0 b1 b2 b4 b3 x x1; (by
  obtain ⟨H0, H1⟩ := HDiff0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  exact H0)); sum_diff_c b0 b1 b2 b6 x b7 ((let HDiff0 := diff_sum_c b0 b1 b2 b3 x b4 x1; sum_assoc_1_c b0 b1 b2 b5 b3 x b6 b4 b7 (sum_comm_c b3 b5 b6 b9) HDiff0 (sum_comm_c b4 b5 b7 b10))))), x2⟩)⟩)
  · subst HLe0
    have H := sum_uniqueness_c b3 b5 b6 b7 b9 b10
    subst H
    exact leP_refl_c b0 b1 b2 b6
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
    ∀ (O E E' A IA : Tpoint), O ≠ A → LeP O E E' O A → Prod O E E' IA A E → LeP O E E' O IA := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b6 with HLe0 | HLe0
  · have HNC := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  exact H0)
    have HColA := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact H3)
    have HColIA := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact H2)
    have e := diff_exists_c b0 b1 b2 b4 b0 HNC HColIA ((by colr))
    obtain ⟨x, x0⟩ := e
    have H := diff_uniqueness_c b0 b1 b2 b4 b0 b4 x (diff_A_O_c b0 b1 b2 b4 HNC HColIA) x0
    subst H
    exact Or.inl (⟨b4, (⟨x0, (by
  obtain ⟨x1, x2⟩ := HLe0
  obtain ⟨x3, x4⟩ := x2
  have H1 := diff_uniqueness_c b0 b1 b2 b3 b0 b3 x1 (diff_A_O_c b0 b1 b2 b3 HNC HColA) x3
  subst H1
  have e0 := opp_exists_c b4 HColIA
  obtain ⟨x5, x6⟩ := e0
  have HElim := x6
  have HElim0 := pos_null_neg_c b0 b1 b2 b4 x5 HElim
  rcases HElim0 with HElim1 | HElim1
  · exact HElim1
  · rcases HElim1 with HPs3 | HPs3
    · subst HPs3
      have H2 := prod_uniqueness_c b0 b3 b0 b1 (prod_0_l_c b0 b1 b2 b3 HNC HColA) b7
      exact (((by
  subst H2
  exact HNC ((by colr))))).elim
    · have e1 := opp_exists_c b1 ((by colr))
      obtain ⟨x7, x8⟩ := e1
      have HColME := (by
  obtain ⟨H2, _⟩ := x8
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, _⟩ := H5
  obtain ⟨H6, _⟩ := x6
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, _⟩ := H8
  exact H4)
      have HProd1 := opp_prod_c b0 b1 b2 x7 b4 x5 x8 x6
      have HProd2 := prod_assoc1_c b1 b2 x7 b4 b3 x5 b1 x7 (prod_comm_c b0 b1 b2 b4 x7 x5 HProd1) b7 (prod_comm_c b0 b1 b2 b1 x7 x7 (prod_1_l_c b0 b1 b2 x7 HNC HColME))
      have HFalse := prod_pos_pos_c b0 b1 b2 x5 b3 x7 HPs3 x4 HProd2
      have HFalse0 := opp_pos_neg_c b0 b1 b2 x7 b1 HFalse (opp_comm_c b1 x7 x8)
      exact (((let HFalse1 := neg_not_pos_c b0 b1 b1 HFalse0; HFalse1 ((let H2 := not_col_distincts_c b0 b1 b2 HNC; (let H3 := H2; (by
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, _⟩ := H6
  exact ⟨(Ne.symm H5), (⟨(Ne.symm H5), (Or.inr (between_symmetry (between_symmetry (between_trivial b0 b1))))⟩)⟩))))))).elim)⟩)⟩)
  · subst HLe0
    have H := (let H := rfl; b5 H)
    exact (H).elim
theorem le_pos_prod_le_c :
    ∀ (O E E' A B C AC BC : Tpoint), LeP O E E' A B → LeP O E E' O C → Prod O E E' A C AC → Prod O E E' B C BC → LeP O E E' AC BC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have HNC := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H0)
  have HColA := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact H7)
  have HColB := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨_, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H2)
  have HColC := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have HColAC := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  exact H8)
  have HColBC := (by
  obtain ⟨H, _⟩ := b11
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := b10
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have e := diff_exists_c b0 b1 b2 b7 b6 HNC HColBC HColAC
  obtain ⟨x, x0⟩ := e
  exact compatibility_of_sum_with_order_c b0 b1 b2 b0 x b6 b6 b7 ((let e0 := diff_exists_c b0 b1 b2 b4 b3 HNC HColB HColA; (by
  obtain ⟨x1, x2⟩ := e0
  have HColBMA := (let HBMA0 := diff_ar2_c b0 b1 b2 b4 b3 x1 x2; (by
  obtain ⟨_, H0⟩ := HBMA0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact H2))
  have e1 := prod_exists_c x1 b5 HColBMA HColC
  obtain ⟨x3, x4⟩ := e1
  have H := sum_diff_c b0 b1 b2 b6 x3 b7 ((let HBMA0 := diff_sum_c b0 b1 b2 b3 x1 b4 x2; distr_r_c b1 b2 b3 x1 b5 b4 b6 x3 b7 HBMA0 b10 x4 b11))
  have H0 := diff_uniqueness_c b0 b1 b2 b7 b6 x x3 x0 H
  subst H0
  exact compatibility_of_prod_with_order_c b0 b1 b2 x1 b5 x ((let e2 := opp_exists_c b3 HColA; (by
  obtain ⟨x5, x6⟩ := e2
  have HColMA := (by
  obtain ⟨H1, _⟩ := x6
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact H3)
  exact compatibility_of_sum_with_order_c b0 b1 b2 b3 b4 x5 b0 x1 b8 (diff_sum_c b0 b1 b2 b3 x5 b0 (diff_O_A_c b0 b1 b2 b3 x5 HNC x6)) ((let HMA0 := diff_O_A_c b0 b1 b2 b3 x5 HNC x6; (let HBMA0 := diff_sum_c b0 b1 b2 b3 x1 b4 x2; (let HMA1 := diff_sum_c b0 b1 b2 b3 x5 b0 HMA0; sum_assoc_1_c b0 b1 b2 x1 b3 x5 b4 b0 x1 (sum_comm_c b3 x1 b4 HBMA0) HMA1 (sum_A_O_c x1 HColBMA)))))))) b9 x4))) (sum_O_B_c b6 HColAC) (sum_comm_c b6 x b7 (diff_sum_c b0 b1 b2 b6 x b7 x0))
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
    ∀ (O E E' A MA B MB : Tpoint), Opp O E E' A MA → Opp O E E' B MB → LeP O E E' A B → LeP O E E' MB MA := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HNC := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b7
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H0)
  have HColA := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b7
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  exact H8)
  have HColMA := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b7
  obtain ⟨_, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact H7)
  have HColB := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := b7
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have HColMB := (by
  obtain ⟨H, _⟩ := b8
  obtain ⟨_, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  obtain ⟨H4, _⟩ := b7
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H2)
  have e := sum_exists_c b4 b6 HColMA HColMB
  obtain ⟨x, x0⟩ := e
  have HMA := sum_assoc_2_c b0 b1 b2 b5 b6 b4 b0 x b4 (sum_comm_c b6 b5 b0 b8) (sum_comm_c b4 b6 x x0) (sum_comm_c b4 b0 b4 (sum_A_O_c b4 HColMA))
  have HMB := sum_assoc_2_c b0 b1 b2 b3 b4 b6 b0 x b6 (sum_comm_c b4 b3 b0 b7) x0 (sum_O_B_c b6 HColMB)
  have HLe0 := compatibility_of_sum_with_order_c b0 b1 b2 b3 b5 x b6 b4 b9 HMB HMA
  exact HLe0
theorem diff_2_le_le_c :
    ∀ (O E E' A B C AMC BMC : Tpoint), Diff O E E' A C AMC → Diff O E E' B C BMC → LeP O E E' A B → LeP O E E' AMC BMC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have HNC := (let HAMC0 := diff_ar2_c b0 b1 b2 b3 b5 b6 b8; (by
  obtain ⟨H, H0⟩ := HAMC0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, _⟩ := H1
  exact H))
  have HColC := (let HAMC0 := diff_ar2_c b0 b1 b2 b3 b5 b6 b8; (by
  obtain ⟨_, H0⟩ := HAMC0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, _⟩ := H1
  exact H2))
  have HColAMC := (let HAMC0 := diff_ar2_c b0 b1 b2 b3 b5 b6 b8; (by
  obtain ⟨_, H0⟩ := HAMC0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact H2))
  have HColBMC := (let HBMC0 := diff_ar2_c b0 b1 b2 b4 b5 b7 b9; (by
  obtain ⟨_, H0⟩ := HBMC0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact H2))
  have e := opp_exists_c b5 HColC
  obtain ⟨x, x0⟩ := e
  have HAMC' := (let HAMC0 := diff_sum_c b0 b1 b2 b5 b6 b3 b8; sum_assoc_1_c b0 b1 b2 b6 b5 x b3 b0 b6 (sum_comm_c b5 b6 b3 HAMC0) (sum_comm_c x b5 b0 x0) (sum_comm_c b0 b6 b6 (sum_O_B_c b6 HColAMC)))
  have HBMC' := (let HBMC0 := diff_sum_c b0 b1 b2 b5 b7 b4 b9; sum_assoc_1_c b0 b1 b2 b7 b5 x b4 b0 b7 (sum_comm_c b5 b7 b4 HBMC0) (sum_comm_c x b5 b0 x0) (sum_comm_c b0 b7 b7 (sum_O_B_c b7 HColBMC)))
  exact compatibility_of_sum_with_order_c b0 b1 b2 b3 b4 x b6 b7 b10 HAMC' HBMC'

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