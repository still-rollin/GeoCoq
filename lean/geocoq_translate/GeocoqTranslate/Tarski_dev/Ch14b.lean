import GeocoqTranslate.Tarski_dev.Ch14a

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

variable (O E E' : Tpoint)
variable (grid_ok : ¬ Col O E E')

theorem prod_to_prodp_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prodp O E E' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨B', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H0
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  have H13 := ⟨((fun H13 => H7 ((by
  subst H13
  exact (by colr))))), ((fun H13 => H7 ((by
  subst H13
  exact (by colr)))))⟩
  exact ⟨H9, (⟨H11, (⟨B', ((by
  obtain ⟨H14, H15⟩ := H13
  exact ⟨(pj_col_project_c b4 B' b0 b2 b1 b2 H14 H15 ((by colr)) ((fun H16 => (by
  rcases H16 with H17 | H17
  · have H18 := (by
  obtain ⟨_, x0⟩ := H17
  exact x0)
    exact H18 (⟨b2, (⟨((by colr)), ((by colr))⟩)⟩)
  · exact H7 ((by
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, H19⟩ := H18
  obtain ⟨H20, _⟩ := H19
  have H21 := H7 H20
  exact (H21).elim))))) H3), (pj_col_project_c B' b5 b0 b1 b3 b2 ((fun H16 => (by
  subst H16
  exact H7 ((by colr))))) ((fun H16 => (by
  subst H16
  exact ((H7 H9)).elim))) ((by colr)) ((fun H16 => (let o := point_equality_decidability b0 b3; (by
  rcases o with H17 | H17
  · subst H17
    rcases H16 with H19 | H19
    · have H20 := (by
  obtain ⟨_, x0⟩ := H19
  exact x0)
      exact H20 (⟨b0, (⟨((by colr)), ((by colr))⟩)⟩)
    · obtain ⟨_, H20⟩ := H19
      obtain ⟨_, H21⟩ := H20
      obtain ⟨_, H22⟩ := H21
      exact H7 ((by colr))
  · rcases H16 with H18 | H18
    · have H19 := (by
  obtain ⟨_, x0⟩ := H18
  exact x0)
      exact H19 (⟨b3, (⟨((by colr)), ((by colr))⟩)⟩)
    · obtain ⟨_, H19⟩ := H18
      obtain ⟨_, H20⟩ := H19
      obtain ⟨H21, _⟩ := H20
      exact H7 ((by colr)))))) ((by
  rcases H6 with H16 | H16
  · exact Or.inl (par_left_comm_c b2 b3 B' b5 H16)
  · exact Or.inr H16)))⟩))⟩)⟩)⟩
theorem project_pj_c :
    ∀ (P P' A B X Y : Tpoint), Proj P P' A B X Y → Pj X Y P P' := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H0⟩ := b6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  rcases H3 with H4 | H4
  · exact Or.inl (par_symmetry_c b0 b1 b4 b5 H4)
  · exact Or.inr H4
theorem prodp_to_prod_c :
    ∀ (O E E' A B C : Tpoint), Prodp O E E' A B C → Prod O E E' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨B', H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨(((by
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, _⟩ := H9
  obtain ⟨H11, H12⟩ := H5
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨_, _⟩ := H16
  exact ⟨((fun H17 => H15 (Or.inr (⟨H11, (⟨H13, (⟨H17, ((by colr))⟩)⟩)⟩)))), (⟨H0, (⟨H2, H10⟩)⟩)⟩))), (⟨B', (⟨(project_pj_c b4 B' b0 b2 b1 b2 H5), (⟨((by
  obtain ⟨_, H7⟩ := H5
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  rcases H11 with _ | _
  · exact H10
  · exact H10)), (project_pj_c B' b5 b0 b1 b2 b3 ((by
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, H14⟩ := H12
  exact ⟨H7, (⟨(Ne.symm H9), (⟨((fun H15 => (by
  rcases H15 with H16 | H16
  · have H17 := (by
  obtain ⟨_, x0⟩ := H16
  exact x0)
    exact H17 (⟨b3, (⟨((by colr)), ((by colr))⟩)⟩)
  · obtain ⟨H17, H18⟩ := H16
    obtain ⟨_, H19⟩ := H18
    obtain ⟨H20, H21⟩ := H19
    exact H11 (Or.inr (⟨H17, (⟨H9, (⟨((by colr)), ((by colr))⟩)⟩)⟩))))), (⟨H13, ((by
  rcases H14 with H15 | H15
  · exact Or.inl (par_right_comm_c B' b5 b3 b2 H15)
  · exact Or.inr H15))⟩)⟩)⟩)⟩)))⟩)⟩)⟩)⟩
theorem prod_exists_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Prod O E E' A B C := sorry

theorem prod_uniqueness_c :
    ∀ (A B C1 C2 : Tpoint), Prod O E E' A B C1 → Prod O E E' A B C2 → C1 = C2 := sorry

theorem prod_0_l_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' O A O := sorry

theorem prod_0_r_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' A O O :=
  fun b0 b1 b2 b3 b4 b5 =>
  ⟨(⟨b4, (⟨b5, (⟨((by colr)), ((by colr))⟩)⟩)⟩), (⟨b0, (⟨(pj_trivial_c b1 b2 b0), (⟨((by colr)), (pj_trivial_c b2 b3 b0)⟩)⟩)⟩)⟩
theorem prod_1_l_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' E A A := sorry

theorem prod_1_r_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' A E A := by
  intro b0 b1 b2 b3 b4 b5
  exact ⟨(⟨b4, (⟨b5, (⟨((by colr)), b5⟩)⟩)⟩), (⟨b2, ((let HH := grid_not_par_c; (by
  obtain ⟨_, H2⟩ := HH
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  exact ⟨(Or.inl (Or.inr (⟨H6, (⟨H6, (⟨((by colr)), ((by colr))⟩)⟩)⟩))), (⟨((by colr)), (Or.inl ((let H7 := (fun H7 => (by
  subst H7
  exact ((b4 b5)).elim)); Or.inr (⟨H7, (⟨H7, (⟨((by colr)), ((by colr))⟩)⟩)⟩))))⟩)⟩)))⟩)⟩
theorem inv_exists_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → A ≠ O → ∃ (IA : Tpoint), Prod O E E' IA A E := sorry

theorem prod_null_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B O → A = O ∨ B = O := sorry

theorem prod_y_axis_change_c :
    ∀ (O E E' E'' A B C : Tpoint), Prod O E E' A B C → ¬ Col O E E'' → Prod O E E'' A B C := sorry

theorem proj_preserves_prod_c :
    ∀ (O E E' A B C A' B' C' : Tpoint), Prod O E E' A B C → Ar1 O E' A' B' C' → Pj E E' A A' → Pj E E' B B' → Pj E E' C C' → Prod O E' E A' B' C' := sorry

theorem prod_assoc1_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' A BC ABC → Prod O E E' AB C ABC) := sorry

theorem prod_assoc2_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' AB C ABC → Prod O E E' A BC ABC) := sorry

theorem prod_assoc_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' A BC ABC ↔ Prod O E E' AB C ABC) :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨(fun H1 => prod_assoc1_c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1), (fun H1 => prod_assoc2_c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1)⟩
theorem prod_comm_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prod O E E' B A C := sorry

theorem prod_O_l_eq_c :
    ∀ (O E E' B C : Tpoint), Prod O E E' O B C → C = O := sorry

theorem prod_O_r_eq_c :
    ∀ (O E E' A C : Tpoint), Prod O E E' A O C → C = O := sorry

theorem prod_uniquenessA_c :
    ∀ (O E E' A A' B C : Tpoint), B ≠ O → Prod O E E' A B C → Prod O E E' A' B C → A = A' := sorry

theorem prod_uniquenessB_c :
    ∀ (O E E' A B B' C : Tpoint), A ≠ O → Prod O E E' A B C → Prod O E E' A B' C → B = B' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  (let H2 := prod_comm_c b0 b1 b2 b3 b4 b6 b8; (let H3 := prod_comm_c b0 b1 b2 b3 b5 b6 b9; prod_uniquenessA_c b0 b1 b2 b4 b5 b3 b6 b7 H2 H3))
theorem distr_l_c :
    ∀ (O E E' A B C D AB AC AD : Tpoint), Sum O E E' B C D → Prod O E E' A B AB → Prod O E E' A C AC → (Prod O E E' A D AD → Sum O E E' AB AC AD) := sorry

theorem distr_r_c :
    ∀ (O E E' A B C D AC BC DC : Tpoint), Sum O E E' A B D → Prod O E E' A C AC → Prod O E E' B C BC → (Prod O E E' D C DC → Sum O E E' AC BC DC) :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 =>
  (let H3 := prod_comm_c b0 b1 b2 b3 b5 b7 b11; (let H4 := prod_comm_c b0 b1 b2 b4 b5 b8 b12; (let H5 := prod_comm_c b0 b1 b2 b6 b5 b9 b13; distr_l_c b1 b2 b5 b3 b4 b6 b7 b8 b9 b10 H3 H4 H5)))
theorem prod_1_l_eq_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B B → A = E ∨ B = O := by
  intro b0 b1 b2 b3 b4 b5
  have HP := b5
  obtain ⟨H0, _⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := H3
  have HH := prod_1_l_c b0 b1 b2 b4 H1 H4
  have o := point_equality_decidability b4 b0
  rcases o with H5 | H5
  · exact Or.inr H5
  · exact Or.inl (prod_uniquenessA_c b0 b1 b2 b3 b1 b4 b4 H5 HP HH)
theorem prod_1_r_eq_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B A → B = E ∨ A = O :=
  fun b0 b1 b2 b3 b4 b5 =>
  (let H0 := prod_comm_c b0 b1 b2 b3 b4 b3 b5; prod_1_l_eq_c b0 b1 b2 b4 b3 H0)
theorem change_grid_prod_l_O_c :
    ∀ (O E E' B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E O B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' O A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' O B C → Prod O' E' E A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  have HP := b16
  obtain ⟨H6, _⟩ := b16
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  have H10 := (let HP0 := prod_O_l_eq_c b0 b1 b2 b3 b4 HP; HP0)
  subst H10
  have H11 := (by
  rcases b13 with H11 | H11
  · exact H11
  · subst H11
    obtain ⟨_, H13⟩ := b11
    obtain ⟨H14, H15⟩ := H13
    obtain ⟨_, _⟩ := H15
    exact (((let H16 := (by
  obtain ⟨_, x0⟩ := b9
  exact x0); H16 (⟨b0, (⟨((by colr)), ((by colr))⟩)⟩)))).elim)
  rcases H11 with H12 | H12
  · exact (((let H13 := (by
  obtain ⟨_, x0⟩ := H12
  exact x0); H13 (⟨b0, (⟨((by colr)), ((by colr))⟩)⟩)))).elim
  · obtain ⟨_, H13⟩ := H12
    obtain ⟨H14, H15⟩ := H13
    obtain ⟨H16, H17⟩ := H15
    have H18 := l6_21_c b0 b5 b2 b5 b6 b5 ((fun H18 => (let H19 := (by
  obtain ⟨_, x0⟩ := b9
  exact x0); H19 (⟨b0, (⟨((by colr)), H18⟩)⟩)))) ((by
  obtain ⟨H18, H19⟩ := b11
  obtain ⟨_, H20⟩ := H19
  obtain ⟨_, _⟩ := H20
  exact Ne.symm H18)) ((by colr)) ((by colr)) ((by
  obtain ⟨_, H18⟩ := b11
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨_, _⟩ := H20
  exact (by colr))) ((by colr))
    subst H18
    have H20 := (by
  rcases b15 with H20 | H20
  · exact H20
  · subst H20
    exact (((by
  obtain ⟨_, H22⟩ := b11
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, H24⟩ := H23
  have H25 := (by
  obtain ⟨_, x0⟩ := b9
  exact x0)
  exact H25 (⟨b0, (⟨((by colr)), ((by colr))⟩)⟩)))).elim)
    rcases H20 with H21 | H21
    · exact (((let H22 := (by
  obtain ⟨_, x0⟩ := H21
  exact x0); H22 (⟨b0, (⟨((by colr)), ((by colr))⟩)⟩)))).elim
    · obtain ⟨_, H22⟩ := H21
      obtain ⟨H23, H24⟩ := H22
      obtain ⟨H25, H26⟩ := H24
      have H27 := l6_21_c b0 b5 b2 b5 b8 b5 ((fun H27 => (let H28 := (by
  obtain ⟨_, x0⟩ := b9
  exact x0); H28 (⟨b0, (⟨((by colr)), H27⟩)⟩)))) ((by
  obtain ⟨H27, H28⟩ := b11
  obtain ⟨_, H29⟩ := H28
  obtain ⟨_, _⟩ := H29
  exact Ne.symm H27)) ((by colr)) ((by colr)) ((by
  obtain ⟨_, H27⟩ := b11
  obtain ⟨_, H28⟩ := H27
  obtain ⟨_, H29⟩ := H28
  exact (by colr))) ((by colr))
      subst H27
      exact prod_0_l_c b5 b2 b1 b7 ((fun H29 => (let H30 := (by
  obtain ⟨_, x0⟩ := b9
  exact x0); H30 (⟨b1, (⟨((by colr)), ((by colr))⟩)⟩)))) ((by
  obtain ⟨_, H29⟩ := b11
  obtain ⟨_, H30⟩ := H29
  obtain ⟨H31, _⟩ := H30
  exact H31))
theorem change_grid_prod1_c :
    ∀ (O E E' B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E E B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' E A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' E B C → Prod O' E' E A' B' C' := sorry

theorem change_grid_prod_c :
    ∀ (O E E' A B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E A B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' A A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' A B C → Prod O' E' E A' B' C' := sorry

theorem prod_sym_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prod O E E' B A C :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  prod_comm_c b0 b1 b2 b3 b4 b5 b6
theorem l14_31_1_c :
    ∀ (O E E' A B C D : Tpoint), Ar2_4 O E E' A B C D → C ≠ O → (∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) → Prod O C E' A B D := sorry

theorem l14_31_2_c :
    ∀ (O E E' A B C D : Tpoint), Ar2_4 O E E' A B C D → C ≠ O → Prod O C E' A B D → (∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) := sorry

theorem prod_x_axis_unit_change_c :
    ∀ (O E E' A B C D U : Tpoint), Ar2_4 O E E' A B C D → Col O E U → U ≠ O → ( ∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) → ( ∃ (Y : Tpoint), Prod O U E' A B Y ∧ Prod O U E' C D Y) := sorry

theorem opp_prod_c :
    ∀ (O E E' ME X MX : Tpoint), Opp O E E' E ME → Opp O E E' X MX → Prod O E E' X ME MX := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have HNC := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H0)
  have HCol1 := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact H7)
  have HCol2 := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have e := sum_exists_c b1 b3 ((by colr)) HCol1
  obtain ⟨x, x0⟩ := e
  have H := sum_uniqueness_c b1 b3 b0 x (diff_sum_c b0 b1 b2 b1 b3 b0 (diff_O_A_c b0 b1 b2 b1 b3 HNC b6)) x0
  subst H
  have e0 := prod_exists_c b4 b1 HCol2 ((by colr))
  obtain ⟨x1, x2⟩ := e0
  have H0 := prod_uniqueness_c b4 b1 b4 x1 (prod_1_r_c b0 b1 b2 b4 HNC HCol2) x2
  subst H0
  have e1 := prod_exists_c b4 b0 HCol2 ((by colr))
  obtain ⟨x3, x4⟩ := e1
  have H1 := prod_uniqueness_c b4 b0 b0 x3 (prod_0_r_c b0 b1 b2 b4 HNC HCol2) x4
  subst H1
  have e2 := prod_exists_c b4 b3 HCol2 HCol1
  obtain ⟨x5, x6⟩ := e2
  have HOpp3 := distr_l_c b1 b2 b4 b1 b3 b0 b4 x5 b0 x0 x2 x6 x4
  have HOpp4 := sum_opp_c b0 b1 b2 b4 x5 HOpp3
  have H2 := opp_uniqueness_c b4 b5 x5 b7 HOpp4
  subst H2
  exact x6
theorem distr_l_diff_c :
    ∀ (O E E' A B C BMC AB AC ABMC : Tpoint), Diff O E E' B C BMC → Prod O E E' A B AB → Prod O E E' A C AC → Prod O E E' A BMC ABMC → Diff O E E' AB AC ABMC :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 =>
  (let HBMC0 := diff_sum_c b0 b1 b2 b5 b6 b4 b10; sum_diff_c b0 b1 b2 b8 b9 b7 (distr_l_c b1 b2 b3 b5 b6 b4 b8 b9 b7 HBMC0 b12 b13 b11))
theorem diff_of_squares_c :
    ∀ (O E E' A B A2 B2 A2MB2 APB AMB F : Tpoint), Prod O E E' A A A2 → Prod O E E' B B B2 → Diff O E E' A2 B2 A2MB2 → Sum O E E' A B APB → Diff O E E' A B AMB → Prod O E E' APB AMB F → A2MB2 = F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  have HNC := (let HA2MB3 := diff_ar2_c b0 b1 b2 b5 b6 b7 b13; (by
  obtain ⟨H, H0⟩ := HA2MB3
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, _⟩ := H1
  exact H))
  have HColA := (by
  obtain ⟨H, _⟩ := b16
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b12
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := b11
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, _⟩ := H12
  exact H13)
  have HColB := (by
  obtain ⟨H, _⟩ := b16
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b12
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  obtain ⟨H9, _⟩ := b11
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  exact H8)
  have HColAMB := (by
  obtain ⟨H, _⟩ := b16
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := b12
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := b11
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  exact H3)
  have e := prod_exists_c b3 b9 HColA HColAMB
  obtain ⟨x, x0⟩ := e
  have HColF1 := (by
  obtain ⟨H, _⟩ := x0
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := b16
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := b12
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  obtain ⟨H14, _⟩ := b11
  obtain ⟨_, H16⟩ := H14
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, _⟩ := H17
  exact H3)
  have e0 := prod_exists_c b4 b9 HColB HColAMB
  obtain ⟨x1, x2⟩ := e0
  have HColF2 := (by
  obtain ⟨H, _⟩ := x2
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := x0
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := b16
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  obtain ⟨H14, _⟩ := b12
  obtain ⟨_, H16⟩ := H14
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, _⟩ := H17
  obtain ⟨H19, _⟩ := b11
  obtain ⟨_, H21⟩ := H19
  obtain ⟨_, H22⟩ := H21
  obtain ⟨_, _⟩ := H22
  exact H3)
  have e1 := sum_exists_c x x1 HColF1 HColF2
  obtain ⟨x3, x4⟩ := e1
  have H := sum_uniqueness_c x x1 b10 x3 (distr_r_c b1 b2 b3 b4 b9 b8 x x1 b10 b14 x0 x2 b16) x4
  subst H
  have e2 := prod_exists_c b3 b4 HColA HColB
  obtain ⟨x5, x6⟩ := e2
  have HColA2 := (by
  obtain ⟨H0, _⟩ := x6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := x2
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := x0
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  obtain ⟨H14, _⟩ := b16
  obtain ⟨_, H16⟩ := H14
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, _⟩ := H17
  obtain ⟨H19, _⟩ := b12
  obtain ⟨_, H21⟩ := H19
  obtain ⟨_, H22⟩ := H21
  obtain ⟨_, _⟩ := H22
  obtain ⟨H24, _⟩ := b11
  obtain ⟨_, H26⟩ := H24
  obtain ⟨_, H27⟩ := H26
  obtain ⟨_, H28⟩ := H27
  exact H28)
  have HColAB := (by
  obtain ⟨H0, _⟩ := x6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := x2
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨H9, _⟩ := x0
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  obtain ⟨H14, _⟩ := b16
  obtain ⟨_, H16⟩ := H14
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, _⟩ := H17
  obtain ⟨H19, _⟩ := b12
  obtain ⟨_, H21⟩ := H19
  obtain ⟨_, H22⟩ := H21
  obtain ⟨_, _⟩ := H22
  obtain ⟨H24, _⟩ := b11
  obtain ⟨_, H26⟩ := H24
  obtain ⟨_, H27⟩ := H26
  obtain ⟨_, _⟩ := H27
  exact H3)
  have e3 := diff_exists_c b0 b1 b2 b5 x5 HNC HColA2 HColAB
  obtain ⟨x7, x8⟩ := e3
  have H0 := diff_uniqueness_c b0 b1 b2 b5 x5 x7 x x8 (distr_l_diff_c b0 b1 b2 b3 b3 b4 b9 b5 x5 x b15 b11 x6 x0)
  have e4 := prod_exists_c b4 b3 HColB HColA
  obtain ⟨x9, x10⟩ := e4
  have HColB2 := (by
  obtain ⟨H1, _⟩ := x10
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  obtain ⟨H5, _⟩ := x6
  obtain ⟨_, H7⟩ := H5
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, _⟩ := H8
  obtain ⟨H10, _⟩ := x2
  obtain ⟨_, H12⟩ := H10
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, _⟩ := H13
  obtain ⟨H15, _⟩ := x0
  obtain ⟨_, H17⟩ := H15
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, _⟩ := H18
  obtain ⟨H20, _⟩ := b16
  obtain ⟨_, H22⟩ := H20
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  obtain ⟨H25, _⟩ := b12
  obtain ⟨_, H27⟩ := H25
  obtain ⟨_, H28⟩ := H27
  obtain ⟨_, H29⟩ := H28
  obtain ⟨H30, _⟩ := b11
  obtain ⟨_, H32⟩ := H30
  obtain ⟨_, H33⟩ := H32
  obtain ⟨_, _⟩ := H33
  exact H29)
  have HColBA := (by
  obtain ⟨H1, _⟩ := x10
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, _⟩ := x6
  obtain ⟨_, H7⟩ := H5
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, _⟩ := H8
  obtain ⟨H10, _⟩ := x2
  obtain ⟨_, H12⟩ := H10
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, _⟩ := H13
  obtain ⟨H15, _⟩ := x0
  obtain ⟨_, H17⟩ := H15
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, _⟩ := H18
  obtain ⟨H20, _⟩ := b16
  obtain ⟨_, H22⟩ := H20
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  obtain ⟨H25, _⟩ := b12
  obtain ⟨_, H27⟩ := H25
  obtain ⟨_, H28⟩ := H27
  obtain ⟨_, _⟩ := H28
  obtain ⟨H30, _⟩ := b11
  obtain ⟨_, H32⟩ := H30
  obtain ⟨_, H33⟩ := H32
  obtain ⟨_, _⟩ := H33
  exact H4)
  have e5 := diff_exists_c b0 b1 b2 x9 b6 HNC HColBA HColB2
  obtain ⟨x11, x12⟩ := e5
  have H1 := diff_uniqueness_c b0 b1 b2 x9 b6 x11 x1 x12 (distr_l_diff_c b0 b1 b2 b4 b3 b4 b9 x9 b6 x1 b15 x10 b12 x2)
  have H2 := prod_uniqueness_c b3 b4 x5 x9 x6 (prod_comm_c b0 b1 b2 b4 b3 x9 x10)
  subst H2
  subst H1
  subst H0
  exact diff_uniqueness_c b0 b1 b2 b5 b6 b7 b10 b13 (sum_diff_diff_b_c b0 b1 b2 b6 x5 b5 x11 x7 b10 x12 x8 x4)
theorem eq_squares_eq_or_opp_c :
    ∀ (O E E' A B A2 : Tpoint), Prod O E E' A A A2 → Prod O E E' B B A2 → A = B ∨ Opp O E E' A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have HNC := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H0)
  have HColA := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  exact H8)
  have HColA2 := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have HColB := (by
  obtain ⟨H, _⟩ := b7
  obtain ⟨_, H1⟩ := H
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := b6
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3)
  have e := diff_exists_c b0 b1 b2 b5 b5 HNC HColA2 HColA2
  obtain ⟨x, x0⟩ := e
  have H := diff_uniqueness_c b0 b1 b2 b5 b5 b0 x (diff_null_c b0 b1 b2 b5 HNC HColA2) x0
  have e0 := sum_exists_c b3 b4 HColA HColB
  obtain ⟨x1, x2⟩ := e0
  have HColAPB := (by
  obtain ⟨H0, _⟩ := x2
  obtain ⟨_, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  exact H4)
  have e1 := diff_exists_c b0 b1 b2 b3 b4 HNC HColA HColB
  obtain ⟨x3, x4⟩ := e1
  subst H
  have HColAMB := (let HAMB0 := diff_sum_c b0 b1 b2 b4 x3 b3 x4; (by
  obtain ⟨H0, _⟩ := HAMB0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  obtain ⟨H4, _⟩ := x2
  obtain ⟨_, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact H3))
  have e2 := prod_exists_c x1 x3 HColAPB HColAMB
  obtain ⟨x5, x6⟩ := e2
  have H1 := diff_of_squares_c b0 b1 b2 b3 b4 b5 b5 b0 x1 x3 x5 b6 b7 x0 x2 x4 x6
  subst H1
  have H3 := prod_null_c b0 b1 b2 x1 x3 x6
  rcases H3 with H4 | H4
  · subst H4
    exact Or.inr (sum_opp_c x1 b1 b2 b3 b4 x2)
  · subst H4
    exact Or.inl (diff_null_eq_c x3 b1 b2 b3 b4 x4)
theorem diff_2_prod_c :
    ∀ (O E E' A B AMB BMA ME : Tpoint), Opp O E E' E ME → Diff O E E' A B AMB → Diff O E E' B A BMA → Prod O E E' AMB ME BMA :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  opp_prod_c b0 b1 b2 b7 b5 b6 b8 (diff_opp_c b0 b1 b2 b3 b4 b5 b6 b9 b10)

#print axioms GeocoqTranslate.Tarski.Base.prod_to_prodp_c
#print axioms GeocoqTranslate.Tarski.Base.project_pj_c
#print axioms GeocoqTranslate.Tarski.Base.prodp_to_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_c
#print axioms GeocoqTranslate.Tarski.Base.inv_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_null_c
#print axioms GeocoqTranslate.Tarski.Base.prod_y_axis_change_c
#print axioms GeocoqTranslate.Tarski.Base.proj_preserves_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc1_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc_c
#print axioms GeocoqTranslate.Tarski.Base.prod_comm_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessA_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessB_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_c
#print axioms GeocoqTranslate.Tarski.Base.distr_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_l_O_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod1_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_sym_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_1_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_x_axis_unit_change_c
#print axioms GeocoqTranslate.Tarski.Base.opp_prod_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_diff_c
#print axioms GeocoqTranslate.Tarski.Base.diff_of_squares_c
#print axioms GeocoqTranslate.Tarski.Base.eq_squares_eq_or_opp_c
#print axioms GeocoqTranslate.Tarski.Base.diff_2_prod_c
end GeocoqTranslate.Tarski.Base
#print axioms GeocoqTranslate.Tarski.Base.prod_to_prodp_c
#print axioms GeocoqTranslate.Tarski.Base.project_pj_c
#print axioms GeocoqTranslate.Tarski.Base.prodp_to_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_c
#print axioms GeocoqTranslate.Tarski.Base.inv_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_null_c
#print axioms GeocoqTranslate.Tarski.Base.prod_y_axis_change_c
#print axioms GeocoqTranslate.Tarski.Base.proj_preserves_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc1_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc_c
#print axioms GeocoqTranslate.Tarski.Base.prod_comm_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessA_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessB_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_c
#print axioms GeocoqTranslate.Tarski.Base.distr_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_l_O_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod1_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_sym_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_1_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_x_axis_unit_change_c
#print axioms GeocoqTranslate.Tarski.Base.opp_prod_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_diff_c
#print axioms GeocoqTranslate.Tarski.Base.diff_of_squares_c
#print axioms GeocoqTranslate.Tarski.Base.eq_squares_eq_or_opp_c
#print axioms GeocoqTranslate.Tarski.Base.diff_2_prod_c
end GeocoqTranslate.Tarski.Base