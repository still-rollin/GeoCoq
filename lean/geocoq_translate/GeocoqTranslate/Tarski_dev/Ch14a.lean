import GeocoqTranslate.Tarski_dev.Ch13f

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

variable (O E E' : Tpoint)
variable (grid_ok : ¬ Col O E E')

theorem Pj_exists_c :
    ∀ (A B C : Tpoint), ∃ (D : Tpoint), Pj A B C D := by
  intro b0 b1 b2
  rcases (point_equality_decidability b0 b1) with H | H
  · subst H
    exact ⟨b2, (Or.inr rfl)⟩
  · have T := parallel_existence_c b0 b1 b2 H
    have H0 := T
    obtain ⟨x, H1⟩ := H0
    obtain ⟨x0, H2⟩ := H1
    obtain ⟨_, H3⟩ := H2
    obtain ⟨H4, H5⟩ := H3
    exact ⟨x0, ((let o := point_equality_decidability b2 x0; (by
  rcases o with H6 | H6
  · exact Or.inr H6
  · exact Or.inl (par_col2_par_c b0 b1 x x0 b2 x0 H6 H4 ((by colr)) ((by colr))))))⟩
theorem sum_to_sump_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Sump O E E' A B C := sorry
theorem sump_to_sum_c :
    ∀ (O E E' A B C : Tpoint), Sump O E E' A B C → Sum O E E' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨A', H4⟩ := H3
  obtain ⟨C', H5⟩ := H4
  obtain ⟨P', H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  exact ⟨(⟨((fun H13 => (by
  obtain ⟨H14, H15⟩ := H7
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨_, _⟩ := H19
  exact H18 (Or.inr (⟨H14, (⟨H16, (⟨H13, ((by colr))⟩)⟩)⟩))))), (⟨H0, (⟨H2, ((by
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨H16, _⟩ := H15
  exact H16))⟩)⟩)⟩), (⟨A', (⟨C', (⟨((by
  obtain ⟨_, H13⟩ := H7
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  rcases H16 with H17 | H17
  · exact Or.inl (par_symmetry_c b3 A' b1 b2 H17)
  · exact Or.inr H17)), (⟨((by
  obtain ⟨_, H13⟩ := H7
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨H16, H17⟩ := H15
  rcases H17 with _ | _
  · exact H16
  · exact H16)), (⟨((let o := point_equality_decidability A' C'; (by
  rcases o with H13 | H13
  · exact Or.inr H13
  · exact Or.inl ((by
  obtain ⟨_, H14⟩ := H11
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  obtain ⟨H17, _⟩ := H16
  exact par_col_par_c b0 b1 A' P' C' H13 H9 H17))))), (⟨((by
  obtain ⟨_, H13⟩ := H11
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  rcases H16 with H17 | H17
  · exact Or.inl (par_symmetry_c b4 C' b0 b2 H17)
  · exact Or.inr H17)), ((by
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  rcases H16 with H17 | H17
  · exact Or.inl (par_symmetry_c C' b5 b2 b1 (par_right_comm_c C' b5 b1 b2 H17))
  · exact Or.inr H17))⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem project_col_project_c :
    ∀ (A B C P P' X Y : Tpoint), A ≠ C → Col A B C → Proj P P' A B X Y → Proj P P' A C X Y := sorry
theorem project_trivial_c :
    ∀ (P A B X Y : Tpoint), A ≠ B → X ≠ Y → Col A B P → ¬ Par A B X Y → Proj P P A B X Y :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  ⟨b5, (⟨b6, (⟨b8, (⟨b7, (Or.inr rfl)⟩)⟩)⟩)⟩
theorem pj_col_project_c :
    ∀ (P P' A B X Y : Tpoint), A ≠ B → X ≠ Y → Col P' A B → ¬ Par A B X Y → Pj X Y P P' → Proj P P' A B X Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  rcases b10 with H4 | H4
  · exact ⟨b6, (⟨b7, (⟨b9, (⟨((by colr)), (Or.inl (par_symmetry_c b4 b5 b0 b1 H4))⟩)⟩)⟩)⟩
  · subst H4
    exact project_trivial_c b0 b2 b3 b4 b5 b6 b7 ((by colr)) b9
theorem sum_exists_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Sum O E E' A B C := sorry
theorem sum_uniqueness_c :
    ∀ (A B C1 C2 : Tpoint), Sum O E E' A B C1 → Sum O E E' A B C2 → C1 = C2 := sorry
theorem opp_exists_c :
    ∀ (A : Tpoint), Col O E A → ∃ (MA : Tpoint), Opp O E E' A MA := sorry
theorem opp0_c :
    Opp O E E' O O := sorry
theorem pj_trivial_c :
    ∀ (A B C : Tpoint), Pj A B C C :=
  fun b0 b1 b2 =>
  Or.inr rfl
theorem sum_O_O_c :
    Sum O E E' O O O := sorry
theorem sum_A_O_c :
    ∀ (A : Tpoint), Col O E A → Sum O E E' A O A := sorry
theorem sum_O_B_c :
    ∀ (B : Tpoint), Col O E B → Sum O E E' O B B := sorry
theorem opp0_uniqueness_c :
    ∀ (M : Tpoint), Opp O E E' O M → M = O := sorry
theorem proj_pars_c :
    ∀ (A A' C' : Tpoint), A ≠ O → Col O E A → Par O E A' C' → Proj A A' O E' E E' → Par_strict O E A' C' := sorry
theorem proj_col_c :
    ∀ (A A' C' : Tpoint), A = O → Col O E A → Par O E A' C' → Proj A A' O E' E E' → A' = O := sorry
theorem grid_not_par_c :
    ¬ Par O E E E' ∧ ¬ Par O E O E' ∧ ¬ Par O E' E E' ∧ O ≠ E ∧ O ≠ E' ∧ E ≠ E' := sorry
theorem proj_id_c :
    ∀ (A A' : Tpoint), Proj A A' O E' E E' → Col O E A → Col O E A' → A = O := sorry
theorem sum_O_B_eq_c :
    ∀ (B C : Tpoint), Sum O E E' O B C → B = C := sorry
theorem sum_A_O_eq_c :
    ∀ (A C : Tpoint), Sum O E E' A O C → A = C := sorry
theorem sum_par_strict_c :
    ∀ (A B C A' C' : Tpoint), Ar2 O E E' A B C → A ≠ O → Pj E E' A A' → Col O E' A' → Pj O E A' C' → Pj O E' B C' → Pj E' E C' C → A' ≠ O ∧ (Par_strict O E A' C' ∨ B = O) := sorry
theorem sum_A_B_A_c :
    ∀ (A B : Tpoint), Sum O E E' A B A → B = O := sorry
theorem sum_A_B_B_c :
    ∀ (A B : Tpoint), Sum O E E' A B B → A = O := sorry
theorem sum_uniquenessB_c :
    ∀ (A X Y C : Tpoint), Sum O E E' A X C → Sum O E E' A Y C → X = Y := sorry
theorem sum_uniquenessA_c :
    ∀ (B X Y C : Tpoint), Sum O E E' X B C → Sum O E E' Y B C → X = Y := sorry
theorem sum_B_null_c :
    ∀ (A B : Tpoint), Sum O E E' A B A → B = O := sorry
theorem sum_A_null_c :
    ∀ (A B : Tpoint), Sum O E E' A B B → A = O := sorry
theorem sum_plg_c :
    ∀ (A B C : Tpoint), Sum O E E' A B C → (A ≠ O ) ∨ ( B ≠ O) → ∃ (A' : Tpoint), ∃ (C' : Tpoint), Plg O B C' A' ∧ Plg C' A' A C := sorry
theorem sum_cong_c :
    ∀ (A B C : Tpoint), Sum O E E' A B C → (A ≠ O ∨ B ≠ O) → Parallelogram_flat O A C B := sorry
theorem sum_cong2_c :
    ∀ (A B C : Tpoint), Sum O E E' A B C → (A ≠ O ∨ B ≠ O) → (Cong O A B C ∧ Cong O B A C) := sorry
theorem sum_comm_c :
    ∀ (A B C : Tpoint), Sum O E E' A B C → Sum O E E' B A C := sorry
theorem cong_sum_c :
    ∀ (A B C : Tpoint), O ≠ C ∨ B ≠ A → Ar2 O E E' A B C → Cong O A B C → Cong O B A C → Sum O E E' A B C := sorry
theorem sum_iff_cong_c :
    ∀ (A B C : Tpoint), Ar2 O E E' A B C → (O ≠ C ∨ B ≠ A) → ((Cong O A B C ∧ Cong O B A C) ↔ Sum O E E' A B C) := sorry
theorem opp_comm_c :
    ∀ (X Y : Tpoint), Opp O E E' X Y → Opp O E E' Y X := sorry
theorem opp_uniqueness_c :
    ∀ (A MA1 MA2 : Tpoint), Opp O E E' A MA1 → Opp O E E' A MA2 → MA1 = MA2 := sorry
theorem pj_uniqueness_c :
    ∀ (O E E' A A' A'' : Tpoint), ¬ Col O E E' → Col O E A → Col O E' A' → Col O E' A'' → Pj E E' A A' → Pj E E' A A'' → A' = A'' := sorry
theorem pj_right_comm_c :
    ∀ (A B C D : Tpoint), Pj A B C D → Pj A B D C := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · exact Or.inl (par_left_comm_c b1 b0 b3 b2 (par_left_comm_c b0 b1 b3 b2 (par_right_comm_c b0 b1 b2 b3 H0)))
  · exact Or.inr (Eq.symm H0)
theorem pj_left_comm_c :
    ∀ (A B C D : Tpoint), Pj A B C D → Pj B A C D := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · exact Or.inl (par_left_comm_c b0 b1 b2 b3 H0)
  · exact Or.inr H0
theorem pj_comm_c :
    ∀ (A B C D : Tpoint), Pj A B C D → Pj B A D C :=
  fun b0 b1 b2 b3 b4 =>
  pj_left_comm_c b0 b1 b3 b2 (pj_right_comm_c b0 b1 b2 b3 b4)
theorem proj_preserves_sum_c :
    ∀ (O E E' A B C A' B' C' : Tpoint), Sum O E E' A B C → Ar1 O E' A' B' C' → Pj E E' A A' → Pj E E' B B' → Pj E E' C C' → Sum O E' E A' B' C' := sorry
theorem sum_assoc_1_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Sum O E E' A B AB → Sum O E E' B C BC → Sum O E E' A BC ABC → Sum O E E' AB C ABC := sorry
theorem sum_assoc_2_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Sum O E E' A B AB → Sum O E E' B C BC → Sum O E E' AB C ABC → Sum O E E' A BC ABC := sorry
theorem sum_assoc_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Sum O E E' A B AB → Sum O E E' B C BC → (Sum O E E' A BC ABC ↔ Sum O E E' AB C ABC) :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨(fun H1 => sum_assoc_1_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1), (fun H1 => sum_assoc_2_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1)⟩
theorem sum_y_axis_change_c :
    ∀ (O E E' E'' A B C : Tpoint), Sum O E E' A B C → ¬ Col O E E'' → Sum O E E'' A B C := sorry
theorem sum_x_axis_unit_change_c :
    ∀ (O E E' U A B C : Tpoint), Sum O E E' A B C → Col O E U → U ≠ O → Sum O U E' A B C := sorry
theorem change_grid_sum_0_c :
    ∀ (O E E' A B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E A B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' A A' → Pj O O' B B' → Pj O O' C C' → Sum O E E' A B C → A = O → Sum O' E' E A' B' C' := sorry
theorem change_grid_sum_c :
    ∀ (O E E' A B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E A B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' A A' → Pj O O' B B' → Pj O O' C C' → Sum O E E' A B C → Sum O' E' E A' B' C' := sorry
theorem double_null_null_c :
    ∀ (O E E' A : Tpoint), Sum O E E' A A O → A = O := sorry
theorem not_null_double_not_null_c :
    ∀ (O E E' A C : Tpoint), Sum O E E' A A C → A ≠ O → C ≠ O := sorry
theorem double_not_null_not_nul_c :
    ∀ (O E E' A C : Tpoint), Sum O E E' A A C → C ≠ O → A ≠ O := sorry
theorem diff_ar2_c :
    ∀ (O E E' A B AMB : Tpoint), Diff O E E' A B AMB → Ar2 O E E' A B AMB := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨MA, H0⟩ := b6
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := H1
  obtain ⟨H5, H6⟩ := H3
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, H10⟩ := H4
  obtain ⟨_, H11⟩ := H10
  obtain ⟨H12, _⟩ := H11
  exact ⟨H5, (⟨H7, (⟨H12, H9⟩)⟩)⟩
theorem diff_null_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Diff O E E' A A O := sorry
theorem diff_exists_c :
    ∀ (O E E' A B : Tpoint), ¬ Col O E E' → Col O E A → Col O E B → ∃ (D : Tpoint), Diff O E E' A B D := sorry
theorem diff_uniqueness_c :
    ∀ (O E E' A B D1 D2 : Tpoint), Diff O E E' A B D1 → Diff O E E' A B D2 → D1 = D2 := sorry
theorem sum_ar2_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Ar2 O E E' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, _⟩ := b6
  exact H0
theorem diff_A_O_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Diff O E E' A O A := sorry
theorem diff_O_A_c :
    ∀ (O E E' A mA : Tpoint), ¬ Col O E E' → Opp O E E' A mA → Diff O E E' O A mA := sorry
theorem diff_O_A_opp_c :
    ∀ (O E E' A mA : Tpoint), Diff O E E' O A mA → Opp O E E' A mA := sorry
theorem diff_uniquenessA_c :
    ∀ (O E E' A A' B C : Tpoint), Diff O E E' A B C → Diff O E E' A' B C → A = A' := sorry
theorem diff_uniquenessB_c :
    ∀ (O E E' A B B' C : Tpoint), Diff O E E' A B C → Diff O E E' A B' C → B = B' := sorry
theorem diff_null_eq_c :
    ∀ (O E E' A B : Tpoint), Diff O E E' A B O → A = B := by
  intro b0 b1 b2 b3 b4 b5
  have H0 := diff_ar2_c b0 b1 b2 b3 b4 b0 b5
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  have H5 := diff_null_c b0 b1 b2 b3 H1 H3
  exact diff_uniquenessB_c b0 b1 b2 b3 b3 b4 b0 H5 b5
theorem midpoint_opp_c :
    ∀ (O E E' A B : Tpoint), Ar2 O E E' O A B → Midpoint O A B → Opp O E E' A B := sorry
theorem sum_diff_c :
    ∀ (O E E' A B S : Tpoint), Sum O E E' A B S → Diff O E E' S A B := sorry
theorem diff_sum_c :
    ∀ (O E E' A B S : Tpoint), Diff O E E' S A B → Sum O E E' A B S := sorry
theorem diff_opp_c :
    ∀ (O E E' A B AmB BmA : Tpoint), Diff O E E' A B AmB → Diff O E E' B A BmA → Opp O E E' AmB BmA := sorry
theorem sum_stable_c :
    ∀ (O E E' A B C S1 S2 : Tpoint), A = B → Sum O E E' A C S1 → Sum O E E' B C S2 → S1 = S2 := sorry
theorem diff_stable_c :
    ∀ (O E E' A B C D1 D2 : Tpoint), A = B → Diff O E E' A C D1 → Diff O E E' B C D2 → D1 = D2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  subst b8
  exact diff_uniqueness_c b0 b1 b2 b3 b5 b6 b7 b9 b10
theorem plg_to_sum_c :
    ∀ (O E E' A B C : Tpoint), Ar2 O E E' A B C → Parallelogram_flat O A C B → Sum O E E' A B C := sorry
theorem opp_midpoint_c :
    ∀ (O E E' A MA : Tpoint), Opp O E E' A MA → Midpoint O A MA := sorry
theorem diff_to_plg_c :
    ∀ (O E E' A B dBA : Tpoint), A ≠ O ∨ B ≠ O → Diff O E E' B A dBA → Parallelogram_flat O A B dBA := sorry
theorem sum3_col_c :
    ∀ (O E E' A B C S : Tpoint), sum3 O E E' A B C S → ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C ∧ Col O E S := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨AB, H0⟩ := b7
  obtain ⟨H1, H2⟩ := H0
  have H3 := sum_ar2_c b0 b1 b2 b3 b4 AB H1
  have H4 := sum_ar2_c b0 b1 b2 AB b5 b6 H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H3
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, _⟩ := H12
  exact ⟨H5, (⟨H11, (⟨H13, (⟨H8, H9⟩)⟩)⟩)⟩
theorem sum3_permut_c :
    ∀ (O E E' A B C S : Tpoint), sum3 O E E' A B C S → sum3 O E E' C A B S := sorry
theorem sum3_comm_1_2_c :
    ∀ (O E E' A B C S : Tpoint), sum3 O E E' A B C S → sum3 O E E' B A C S := sorry
theorem sum3_comm_2_3_c :
    ∀ (O E E' A B C S : Tpoint), sum3 O E E' A B C S → sum3 O E E' A C B S :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  (let H0 := sum3_permut_c b0 b1 b2 b3 b4 b5 b6 b7; (let H1 := sum3_comm_1_2_c b0 b1 b2 b5 b3 b4 b6 H0; H1))
theorem sum3_exists_c :
    ∀ (O E E' A B C : Tpoint), Ar2 O E E' A B C → ∃ (S : Tpoint), sum3 O E E' A B C S := sorry
theorem sum3_uniqueness_c :
    ∀ (O E E' A B C S1 S2 : Tpoint), sum3 O E E' A B C S1 → sum3 O E E' A B C S2 → S1 = S2 := sorry
theorem sum4_col_c :
    ∀ (O E E' A B C D S : Tpoint), Sum4 O E E' A B C D S → ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C ∧ Col O E D ∧ Col O E S := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨ABC, H0⟩ := b8
  obtain ⟨H1, H2⟩ := H0
  have HH := sum3_col_c b0 b1 b2 b3 b4 b5 ABC H1
  have H3 := sum_ar2_c b0 b1 b2 ABC b6 b7 H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, H9⟩ := HH
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, _⟩ := H13
  exact ⟨H4, (⟨H10, (⟨H12, (⟨H14, (⟨H7, H8⟩)⟩)⟩)⟩)⟩
theorem sum22_col_c :
    ∀ (O E E' A B C D S : Tpoint), sum22 O E E' A B C D S → ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C ∧ Col O E D ∧ Col O E S := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨AB, H0⟩ := b8
  obtain ⟨CD, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  have H6 := sum_ar2_c b0 b1 b2 b3 b4 AB H2
  have H7 := sum_ar2_c b0 b1 b2 b5 b6 CD H4
  have H8 := sum_ar2_c b0 b1 b2 AB CD b7 H5
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H7
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨H16, _⟩ := H15
  obtain ⟨_, H17⟩ := H6
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, _⟩ := H19
  exact ⟨H9, (⟨H18, (⟨H20, (⟨H14, (⟨H16, H12⟩)⟩)⟩)⟩)⟩
theorem sum_to_sum3_c :
    ∀ (O E E' A B AB X S : Tpoint), Sum O E E' A B AB → Sum O E E' AB X S → sum3 O E E' A B X S :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ⟨b5, (⟨b8, b9⟩)⟩
theorem sum3_to_sum4_c :
    ∀ (O E E' A B C X ABC S : Tpoint), sum3 O E E' A B C ABC → Sum O E E' ABC X S → Sum4 O E E' A B C X S := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H1 := sum3_col_c b0 b1 b2 b3 b4 b5 b7 b9
  have H2 := sum_ar2_c b0 b1 b2 b7 b6 b8 b10
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, _⟩ := H4
  obtain ⟨_, H6⟩ := H1
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, _⟩ := H8
  exact ⟨b7, (⟨b9, b10⟩)⟩
theorem sum_A_exists_c :
    ∀ (O E E' A AB : Tpoint), Ar2 O E E' A AB O → ∃ (B : Tpoint), Sum O E E' A B AB := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := b5
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, _⟩ := H3
  have HH := diff_exists_c b0 b1 b2 b4 b3 H0 H4 H2
  obtain ⟨B, H5⟩ := HH
  exact ⟨B, ((let H6 := diff_sum_c b0 b1 b2 b3 B b4 H5; H6))⟩
theorem sum_B_exists_c :
    ∀ (O E E' B AB : Tpoint), Ar2 O E E' B AB O → ∃ (A : Tpoint), Sum O E E' A B AB := sorry
theorem sum4_equiv_c :
    ∀ (O E E' A B C D S : Tpoint), Sum4 O E E' A B C D S ↔ sum22 O E E' A B C D S := sorry
theorem sum4_permut_c :
    ∀ (O E E' A B C D S : Tpoint), Sum4 O E E' A B C D S → Sum4 O E E' D A B C S := sorry
theorem sum22_permut_c :
    ∀ (O E E' A B C D S : Tpoint), sum22 O E E' A B C D S → sum22 O E E' D A B C S := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have HH := sum4_equiv_c b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨x, x0⟩ := HH
  have H2 := x0 b8
  have H3 := sum4_permut_c b0 b1 b2 b3 b4 b5 b6 b7 H2
  have HH0 := sum4_equiv_c b0 b1 b2 b6 b3 b4 b5 b7
  obtain ⟨x1, x2⟩ := HH0
  exact x1 H3
theorem sum4_comm_c :
    ∀ (O E E' A B C D S : Tpoint), Sum4 O E E' A B C D S → Sum4 O E E' B A C D S := sorry
theorem sum22_comm_c :
    ∀ (O E E' A B C D S : Tpoint), sum22 O E E' A B C D S → sum22 O E E' B A C D S := sorry
theorem sum_abcd_c :
    ∀ (O E E' A B C D AB CD BC AD S : Tpoint), Sum O E E' A B AB → Sum O E E' C D CD → Sum O E E' B C BC → Sum O E E' A D AD → Sum O E E' AB CD S → Sum O E E' BC AD S := sorry
theorem sum_diff_diff_a_c :
    ∀ (O E E' A B C dBA dCB dCA : Tpoint), Diff O E E' B A dBA → Diff O E E' C B dCB → Diff O E E' C A dCA → Sum O E E' dCB dBA dCA := sorry
theorem sum_diff_diff_b_c :
    ∀ (O E E' A B C dBA dCB dCA : Tpoint), Diff O E E' B A dBA → Diff O E E' C B dCB → Sum O E E' dCB dBA dCA → Diff O E E' C A dCA := sorry
theorem sum_diff2_diff_sum2_a_c :
    ∀ (O E E' A B C X Y Z dXA dYB dZC : Tpoint), Sum O E E' A B C → Sum O E E' X Y Z → Diff O E E' X A dXA → Diff O E E' Y B dYB → Sum O E E' dXA dYB dZC → Diff O E E' Z C dZC := sorry
theorem sum_diff2_diff_sum2_b_c :
    ∀ (O E E' A B C X Y Z dXA dYB dZC : Tpoint), Sum O E E' A B C → Sum O E E' X Y Z → Diff O E E' X A dXA → Diff O E E' Y B dYB → Diff O E E' Z C dZC → Sum O E E' dXA dYB dZC := sorry
theorem sum_opp_c :
    ∀ (O E E' X MX : Tpoint), Sum O E E' X MX O → Opp O E E' X MX :=
  fun b0 b1 b2 b3 b4 b5 =>
  diff_O_A_opp_c b0 b1 b2 b3 b4 (sum_diff_c b0 b1 b2 b3 b4 b0 b5)
theorem sum_diff_diff_c :
    ∀ (O E E' AX BX CX AXMBX AXMCX BXMCX : Tpoint), Diff O E E' AX BX AXMBX → Diff O E E' AX CX AXMCX → Diff O E E' BX CX BXMCX → Sum O E E' AXMBX BXMCX AXMCX := sorry
#print axioms GeocoqTranslate.Tarski.Base.Pj_exists_c
#print axioms GeocoqTranslate.Tarski.Base.sum_to_sump_c
#print axioms GeocoqTranslate.Tarski.Base.sump_to_sum_c
#print axioms GeocoqTranslate.Tarski.Base.project_col_project_c
#print axioms GeocoqTranslate.Tarski.Base.project_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.pj_col_project_c
#print axioms GeocoqTranslate.Tarski.Base.sum_exists_c
#print axioms GeocoqTranslate.Tarski.Base.sum_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.opp_exists_c
#print axioms GeocoqTranslate.Tarski.Base.opp0_c
#print axioms GeocoqTranslate.Tarski.Base.pj_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.sum_O_O_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_O_c
#print axioms GeocoqTranslate.Tarski.Base.sum_O_B_c
#print axioms GeocoqTranslate.Tarski.Base.opp0_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.proj_pars_c
#print axioms GeocoqTranslate.Tarski.Base.proj_col_c
#print axioms GeocoqTranslate.Tarski.Base.grid_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.proj_id_c
#print axioms GeocoqTranslate.Tarski.Base.sum_O_B_eq_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_O_eq_c
#print axioms GeocoqTranslate.Tarski.Base.sum_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_B_A_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_B_B_c
#print axioms GeocoqTranslate.Tarski.Base.sum_uniquenessB_c
#print axioms GeocoqTranslate.Tarski.Base.sum_uniquenessA_c
#print axioms GeocoqTranslate.Tarski.Base.sum_B_null_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_null_c
#print axioms GeocoqTranslate.Tarski.Base.sum_plg_c
#print axioms GeocoqTranslate.Tarski.Base.sum_cong_c
#print axioms GeocoqTranslate.Tarski.Base.sum_cong2_c
#print axioms GeocoqTranslate.Tarski.Base.sum_comm_c
#print axioms GeocoqTranslate.Tarski.Base.cong_sum_c
#print axioms GeocoqTranslate.Tarski.Base.sum_iff_cong_c
#print axioms GeocoqTranslate.Tarski.Base.opp_comm_c
#print axioms GeocoqTranslate.Tarski.Base.opp_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.pj_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.pj_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.pj_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.pj_comm_c
#print axioms GeocoqTranslate.Tarski.Base.proj_preserves_sum_c
#print axioms GeocoqTranslate.Tarski.Base.sum_assoc_1_c
#print axioms GeocoqTranslate.Tarski.Base.sum_assoc_2_c
#print axioms GeocoqTranslate.Tarski.Base.sum_assoc_c
#print axioms GeocoqTranslate.Tarski.Base.sum_y_axis_change_c
#print axioms GeocoqTranslate.Tarski.Base.sum_x_axis_unit_change_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_sum_0_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_sum_c
#print axioms GeocoqTranslate.Tarski.Base.double_null_null_c
#print axioms GeocoqTranslate.Tarski.Base.not_null_double_not_null_c
#print axioms GeocoqTranslate.Tarski.Base.double_not_null_not_nul_c
#print axioms GeocoqTranslate.Tarski.Base.diff_ar2_c
#print axioms GeocoqTranslate.Tarski.Base.diff_null_c
#print axioms GeocoqTranslate.Tarski.Base.diff_exists_c
#print axioms GeocoqTranslate.Tarski.Base.diff_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.sum_ar2_c
#print axioms GeocoqTranslate.Tarski.Base.diff_A_O_c
#print axioms GeocoqTranslate.Tarski.Base.diff_O_A_c
#print axioms GeocoqTranslate.Tarski.Base.diff_O_A_opp_c
#print axioms GeocoqTranslate.Tarski.Base.diff_uniquenessA_c
#print axioms GeocoqTranslate.Tarski.Base.diff_uniquenessB_c
#print axioms GeocoqTranslate.Tarski.Base.diff_null_eq_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_opp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff_c
#print axioms GeocoqTranslate.Tarski.Base.diff_sum_c
#print axioms GeocoqTranslate.Tarski.Base.diff_opp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_stable_c
#print axioms GeocoqTranslate.Tarski.Base.diff_stable_c
#print axioms GeocoqTranslate.Tarski.Base.plg_to_sum_c
#print axioms GeocoqTranslate.Tarski.Base.opp_midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.diff_to_plg_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_col_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_permut_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_comm_1_2_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_comm_2_3_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_exists_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.sum4_col_c
#print axioms GeocoqTranslate.Tarski.Base.sum22_col_c
#print axioms GeocoqTranslate.Tarski.Base.sum_to_sum3_c
#print axioms GeocoqTranslate.Tarski.Base.sum3_to_sum4_c
#print axioms GeocoqTranslate.Tarski.Base.sum_A_exists_c
#print axioms GeocoqTranslate.Tarski.Base.sum_B_exists_c
#print axioms GeocoqTranslate.Tarski.Base.sum4_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.sum4_permut_c
#print axioms GeocoqTranslate.Tarski.Base.sum22_permut_c
#print axioms GeocoqTranslate.Tarski.Base.sum4_comm_c
#print axioms GeocoqTranslate.Tarski.Base.sum22_comm_c
#print axioms GeocoqTranslate.Tarski.Base.sum_abcd_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff_diff_a_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff_diff_b_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff2_diff_sum2_a_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff2_diff_sum2_b_c
#print axioms GeocoqTranslate.Tarski.Base.sum_opp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_diff_diff_c
end GeocoqTranslate.Tarski.Base