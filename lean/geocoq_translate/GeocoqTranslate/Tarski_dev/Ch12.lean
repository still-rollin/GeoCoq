import GeocoqTranslate.Tarski_dev.Ch11

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem par_reflexivity_c :
    ∀ (A B : Tpoint), A ≠ B → Par A B A B :=
  fun b0 b1 b2 =>
  (Or.inr (⟨b2, (⟨b2, (⟨(col_trivial_1_c b0 b1), (col_trivial_3_c b1 b0)⟩)⟩)⟩))
theorem par_strict_irreflexivity_c :
    ∀ (A B : Tpoint), ¬ Par_strict A B A B := by
  intro b0 b1
  intro H
  obtain ⟨_, H0⟩ := H
  exact H0 (⟨b0, (⟨(col_trivial_1_c b0 b1), (col_trivial_1_c b0 b1)⟩)⟩)
theorem not_par_strict_id_c :
    ∀ (A B C : Tpoint), ¬ Par_strict A B A C := by
  intro b0 b1 b2
  intro H
  obtain ⟨_, H0⟩ := H
  exact H0 (⟨b0, (⟨(col_trivial_1_c b0 b1), (col_trivial_1_c b0 b2)⟩)⟩)
theorem par_id_c :
    ∀ (A B C : Tpoint), Par A B A C → Col A B C := sorry
theorem par_strict_not_col_1_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → ¬ Col A B C := by
  intro b0 b1 b2 b3 b4
  obtain ⟨_, H0⟩ := b4
  intro H1
  exact H0 (⟨b2, (⟨(col_permutation_5_c b2 b1 b0 (col_permutation_3_c b0 b1 b2 H1)), (col_trivial_1_c b2 b3)⟩)⟩)
theorem par_strict_not_col_2_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → ¬ Col B C D := by
  intro b0 b1 b2 b3 b4
  obtain ⟨_, H0⟩ := b4
  intro H1
  exact H0 (⟨b1, (⟨(col_trivial_3_c b1 b0), H1⟩)⟩)
theorem par_strict_not_col_3_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → ¬ Col C D A := by
  intro b0 b1 b2 b3 b4
  obtain ⟨_, H0⟩ := b4
  intro H1
  exact H0 (⟨b0, (⟨(col_trivial_1_c b0 b1), (col_permutation_5_c b0 b3 b2 (col_permutation_3_c b2 b3 b0 H1))⟩)⟩)
theorem par_strict_not_col_4_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → ¬ Col A B D := by
  intro b0 b1 b2 b3 b4
  obtain ⟨_, H0⟩ := b4
  intro H1
  exact H0 (⟨b3, (⟨(col_permutation_5_c b3 b1 b0 (col_permutation_3_c b0 b1 b3 H1)), (col_trivial_3_c b3 b2)⟩)⟩)
theorem par_strict_not_cols_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → ¬ Col A B C ∧ ¬ Col B C D ∧ ¬ Col C D A ∧ ¬ Col A B D :=
  fun b0 b1 b2 b3 b4 =>
  ⟨(par_strict_not_col_1_c b0 b1 b2 b3 b4), (⟨(par_strict_not_col_2_c b0 b1 b2 b3 b4), (⟨(par_strict_not_col_3_c b0 b1 b2 b3 b4), (par_strict_not_col_4_c b0 b1 b2 b3 b4)⟩)⟩)⟩

theorem par_strict_symmetry_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par_strict C D A B := by
  intro b0 b1 b2 b3 b4
  obtain ⟨H0, H1⟩ := b4
  exact ⟨(coplanar_perm_16_c b0 b1 b2 b3 H0), ((fun H2 => H1 ((by
  obtain ⟨X, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  exact ⟨X, (⟨H5, H4⟩)⟩))))⟩

theorem par_symmetry_c :
    ∀ (A B C D : Tpoint), Par A B C D → Par C D A B := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · exact Or.inl (par_strict_symmetry_c b0 b1 b2 b3 H0)
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨H5, H6⟩ := H4
    exact Or.inr (⟨H3, (⟨H1, (⟨((by colr)), ((by colr))⟩)⟩)⟩)

theorem par_strict_left_comm_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par_strict B A C D := by
  intro b0 b1 b2 b3 b4
  have H0 := b4
  obtain ⟨H1, H2⟩ := H0
  exact ⟨(coplanar_perm_6_c b0 b1 b2 b3 H1), ((fun H3 => H2 ((by
  obtain ⟨X, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨X, (⟨((by colr)), H6⟩)⟩))))⟩

theorem par_strict_right_comm_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par_strict A B D C := by
  intro b0 b1 b2 b3 b4
  have H0 := b4
  obtain ⟨H1, H2⟩ := H0
  exact ⟨(coplanar_perm_1_c b0 b1 b2 b3 H1), ((fun H3 => H2 ((by
  obtain ⟨X, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨X, (⟨H5, ((by colr))⟩)⟩))))⟩

theorem par_strict_comm_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par_strict B A D C :=
  fun b0 b1 b2 b3 b4 =>
  (let H0 := par_strict_left_comm_c b0 b1 b2 b3 b4; par_strict_right_comm_c b1 b0 b2 b3 H0)

theorem par_left_comm_c :
    ∀ (A B C D : Tpoint), Par A B C D → Par B A C D := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · exact Or.inl (par_strict_left_comm_c b0 b1 b2 b3 H0)
  · exact Or.inr ((by
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  exact ⟨(Ne.symm H1), (⟨H3, (⟨H6, H5⟩)⟩)⟩))

theorem par_right_comm_c :
    ∀ (A B C D : Tpoint), Par A B C D → Par A B D C :=
  fun b0 b1 b2 b3 b4 =>
  (let H0 := par_symmetry_c b0 b1 b2 b3 b4; par_symmetry_c b3 b2 b0 b1 (par_left_comm_c b2 b3 b0 b1 H0))

theorem par_comm_c :
    ∀ (A B C D : Tpoint), Par A B C D → Par B A D C :=
  fun b0 b1 b2 b3 b4 =>
  par_left_comm_c b0 b1 b3 b2 (par_right_comm_c b0 b1 b2 b3 b4)

theorem par_strict_distinct_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := sorry
theorem par_neq1_c :
    ∀ (A B C D : Tpoint), Par A B C D → A ≠ B := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · have H1 := par_strict_distinct_c b0 b1 b2 b3 H0
    obtain ⟨H2, H3⟩ := H1
    obtain ⟨_, H4⟩ := H3
    obtain ⟨_, H5⟩ := H4
    obtain ⟨_, H6⟩ := H5
    obtain ⟨_, _⟩ := H6
    exact H2
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨_, H3⟩ := H2
    obtain ⟨_, _⟩ := H3
    exact H1

theorem par_neq2_c :
    ∀ (A B C D : Tpoint), Par A B C D → C ≠ D :=
  fun b0 b1 b2 b3 b4 =>
  (let H0 := par_symmetry_c b0 b1 b2 b3 b4; par_neq1_c b2 b3 b0 b1 H0)

theorem Par_cases_c :
    ∀ (A B C D : Tpoint), Par A B C D ∨ Par B A C D ∨ Par A B D C ∨ Par B A D C ∨ Par C D A B ∨ Par C D B A ∨ Par D C A B ∨ Par D C B A → Par A B C D := by
  intro b0 b1 b2 b3 b4
  have H0 := b4
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact par_left_comm_c b1 b0 b2 b3 H2
    · rcases H2 with H3 | H3
      · exact par_left_comm_c b1 b0 b2 b3 (par_left_comm_c b0 b1 b2 b3 (par_right_comm_c b0 b1 b3 b2 H3))
      · rcases H3 with H4 | H4
        · exact par_left_comm_c b1 b0 b2 b3 (par_left_comm_c b0 b1 b2 b3 (par_comm_c b1 b0 b3 b2 H4))
        · rcases H4 with H5 | H5
          · exact par_left_comm_c b1 b0 b2 b3 (par_left_comm_c b0 b1 b2 b3 (par_symmetry_c b2 b3 b0 b1 H5))
          · rcases H5 with H6 | H6
            · exact par_left_comm_c b1 b0 b2 b3 (par_symmetry_c b2 b3 b1 b0 H6)
            · rcases H6 with H7 | H7
              · exact par_left_comm_c b1 b0 b2 b3 (par_comm_c b0 b1 b3 b2 (par_symmetry_c b3 b2 b0 b1 H7))
              · exact par_left_comm_c b1 b0 b2 b3 (par_right_comm_c b1 b0 b3 b2 (par_symmetry_c b3 b2 b1 b0 H7))

theorem Par_perm_c :
    ∀ (A B C D : Tpoint), Par A B C D → Par A B C D ∧ Par B A C D ∧ Par A B D C ∧ Par B A D C ∧ Par C D A B ∧ Par C D B A ∧ Par D C A B ∧ Par D C B A :=
  fun b0 b1 b2 b3 b4 =>
  ⟨b4, (⟨(par_left_comm_c b0 b1 b2 b3 b4), (⟨(par_left_comm_c b1 b0 b3 b2 (par_left_comm_c b0 b1 b3 b2 (par_right_comm_c b0 b1 b2 b3 b4))), (⟨(par_left_comm_c b0 b1 b3 b2 (par_left_comm_c b1 b0 b3 b2 (par_comm_c b0 b1 b2 b3 b4))), (⟨(par_left_comm_c b3 b2 b0 b1 (par_left_comm_c b2 b3 b0 b1 (par_symmetry_c b0 b1 b2 b3 b4))), (⟨(par_left_comm_c b3 b2 b1 b0 (par_comm_c b2 b3 b0 b1 (par_symmetry_c b0 b1 b2 b3 b4))), (⟨(par_left_comm_c b2 b3 b0 b1 (par_symmetry_c b0 b1 b2 b3 b4)), (par_comm_c b2 b3 b0 b1 (par_symmetry_c b0 b1 b2 b3 b4))⟩)⟩)⟩)⟩)⟩)⟩)⟩

theorem Par_strict_cases_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D ∨ Par_strict B A C D ∨ Par_strict A B D C ∨ Par_strict B A D C ∨ Par_strict C D A B ∨ Par_strict C D B A ∨ Par_strict D C A B ∨ Par_strict D C B A → Par_strict A B C D := by
  intro b0 b1 b2 b3 b4
  have H0 := b4
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact par_strict_left_comm_c b1 b0 b2 b3 H2
    · rcases H2 with H3 | H3
      · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_left_comm_c b1 b0 b2 b3 (par_strict_comm_c b0 b1 b3 b2 H3)))
      · rcases H3 with H4 | H4
        · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_left_comm_c b1 b0 b2 b3 (par_strict_right_comm_c b1 b0 b3 b2 H4)))
        · rcases H4 with H5 | H5
          · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_symmetry_c b2 b3 b0 b1 H5))
          · rcases H5 with H6 | H6
            · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_left_comm_c b1 b0 b2 b3 (par_strict_symmetry_c b2 b3 b1 b0 H6)))
            · rcases H6 with H7 | H7
              · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_right_comm_c b0 b1 b3 b2 (par_strict_symmetry_c b3 b2 b0 b1 H7)))
              · exact par_strict_left_comm_c b1 b0 b2 b3 (par_strict_left_comm_c b0 b1 b2 b3 (par_strict_comm_c b1 b0 b3 b2 (par_strict_symmetry_c b3 b2 b1 b0 H7)))

theorem Par_strict_perm_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par_strict A B C D ∧ Par_strict B A C D ∧ Par_strict A B D C ∧ Par_strict B A D C ∧ Par_strict C D A B ∧ Par_strict C D B A ∧ Par_strict D C A B ∧ Par_strict D C B A :=
  fun b0 b1 b2 b3 b4 =>
  ⟨b4, (⟨(par_strict_left_comm_c b0 b1 b2 b3 b4), (⟨(par_strict_left_comm_c b1 b0 b3 b2 (par_strict_left_comm_c b0 b1 b3 b2 (par_strict_right_comm_c b0 b1 b2 b3 b4))), (⟨(par_strict_left_comm_c b0 b1 b3 b2 (par_strict_left_comm_c b1 b0 b3 b2 (par_strict_comm_c b0 b1 b2 b3 b4))), (⟨(par_strict_left_comm_c b3 b2 b0 b1 (par_strict_left_comm_c b2 b3 b0 b1 (par_strict_symmetry_c b0 b1 b2 b3 b4))), (⟨(par_strict_left_comm_c b3 b2 b1 b0 (par_strict_comm_c b2 b3 b0 b1 (par_strict_symmetry_c b0 b1 b2 b3 b4))), (⟨(par_strict_left_comm_c b2 b3 b0 b1 (par_strict_symmetry_c b0 b1 b2 b3 b4)), (par_strict_comm_c b2 b3 b0 b1 (par_strict_symmetry_c b0 b1 b2 b3 b4))⟩)⟩)⟩)⟩)⟩)⟩)⟩

theorem l12_6_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → OS A B C D := sorry
theorem pars__os3412_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → OS C D A B :=
  fun b0 b1 b2 b3 b4 =>
  l12_6_c b2 b3 b0 b1 (par_strict_symmetry_c b0 b1 b2 b3 b4)

theorem perp_dec_c :
    ∀ (A B C D : Tpoint), Perp A B C D ∨ ¬ Perp A B C D := sorry
theorem col_cop2_perp2__col_c :
    ∀ (X1 X2 Y1 Y2 A B : Tpoint), Perp X1 X2 A B → Perp Y1 Y2 A B → Col X1 Y1 Y2 → Coplanar A B X2 Y1 → Coplanar A B X2 Y2 → Col X2 Y1 Y2 := sorry

theorem col_perp2_ncol__col_c :
    ∀ (X1 X2 Y1 Y2 A B : Tpoint), Perp X1 X2 A B → Perp Y1 Y2 A B → Col X1 Y1 Y2 → ¬ Col X1 A B → Col X2 Y1 Y2 := sorry
theorem l12_9_c :
    ∀ (A1 A2 B1 B2 C1 C2 : Tpoint), Coplanar C1 C2 A1 B1 → Coplanar C1 C2 A1 B2 → Coplanar C1 C2 A2 B1 → Coplanar C1 C2 A2 B2 → Perp A1 A2 C1 C2 → Perp B1 B2 C1 C2 → Par A1 A2 B1 B2 := sorry
theorem parallel_existence_c :
    ∀ (A B P : Tpoint), A ≠ B → ∃ (C : Tpoint), ∃ (D : Tpoint), C ≠ D ∧ Par A B C D ∧ Col P C D := sorry
theorem par_col_par_c :
    ∀ (A B C D D' : Tpoint), C ≠ D' → Par A B C D → Col C D D' → Par A B C D' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b6 with H2 | H2
  · exact Or.inl ((let H3 := par_strict_distinct_c b0 b1 b2 b3 H2; (let H4 := H3; (by
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H2
  exact ⟨(col_cop__cop_c b0 b1 b2 b3 b4 H10 H9 b7), ((fun H12 => H11 ((by
  obtain ⟨P, H13⟩ := H12
  obtain ⟨H14, H15⟩ := H13
  exact ⟨P, (⟨H14, ((by colr))⟩)⟩))))⟩))))
  · exact Or.inr ((by
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  exact ⟨H3, (⟨b5, (⟨((by colr)), ((by colr))⟩)⟩)⟩))

theorem parallel_existence1_c :
    ∀ (A B P : Tpoint), A ≠ B → ∃ (Q : Tpoint), Par A B P Q := by
  intro b0 b1 b2 b3
  have T := parallel_existence_c b0 b1 b2 b3
  have H0 := T
  obtain ⟨x, H1⟩ := H0
  obtain ⟨x0, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  rcases (point_equality_decidability x b2) with H7 | H7
  · subst H7
    exact ⟨x0, H5⟩
  · exact ⟨x, (par_right_comm_c b0 b1 x b2 (par_col_par_c b0 b1 x x0 b2 H7 H5 ((by colr))))⟩

theorem par_not_col_c :
    ∀ (A B C D X : Tpoint), Par_strict A B C D → Col X A B → ¬ Col X C D := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro H1
  obtain ⟨_, H2⟩ := b5
  exact H2 (⟨b4, (⟨b6, H1⟩)⟩)
theorem not_strict_par1_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B C := sorry
theorem not_strict_par2_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  not_strict_par1_c b0 b1 b3 b2 b4 (par_right_comm_c b0 b1 b2 b3 b5) b6 ((by colr))

theorem not_strict_par_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B C ∧ Col A B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨(not_strict_par1_c b0 b1 b2 b3 b4 b5 b6 b7), (not_strict_par2_c b0 b1 b2 b3 b4 b5 b6 b7)⟩

theorem col2_par__col4_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B C ∧ Col A B D ∧ Col A C D ∧ Col B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have a := not_strict_par_c b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨x, x0⟩ := a
  have H4 := par_symmetry_c b0 b1 b2 b3 b5
  have a0 := not_strict_par_c b2 b3 b0 b1 b4 H4 b7 b6
  obtain ⟨x1, x2⟩ := a0
  exact ⟨x, (⟨x0, (⟨((by colr)), ((by colr))⟩)⟩)⟩

theorem not_par_not_col_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → ¬ Par A B A C → ¬ Col A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  (fun H2 => b5 (Or.inr (⟨b3, (⟨b4, (⟨(col_trivial_1_c b0 b2), (col_permutation_5_c b1 b2 b0 (col_permutation_1_c b0 b1 b2 H2))⟩)⟩)⟩)))
theorem not_par_inter_uniqueness_c :
    ∀ (A B C D X Y : Tpoint), A ≠ B → C ≠ D → ¬ Par A B C D → Col A B X → Col C D X → Col A B Y → Col C D Y → X = Y := sorry

theorem inter_uniqueness_not_par_c :
    ∀ (A B C D P : Tpoint), ¬ Col A B C → Col A B P → Col C D P → ¬ Par A B C D := sorry

theorem col_not_col_not_par_c :
    ∀ (A B C D : Tpoint), (∃ (P : Tpoint), Col A B P ∧ Col C D P) → (∃ (Q : Tpoint), Col C D Q ∧ ¬ Col A B Q) → ¬ Par A B C D := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨P, H1⟩ := b4
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨Q, H4⟩ := b5
  obtain ⟨H5, H6⟩ := H4
  intro H7
  rcases H7 with H8 | H8
  · obtain ⟨_, H9⟩ := H8
    exact H9 (⟨P, (⟨(col_permutation_5_c P b1 b0 (col_permutation_5_c P b0 b1 (col_permutation_2_c b0 b1 P H2))), (col_permutation_5_c P b3 b2 (col_permutation_5_c P b2 b3 (col_permutation_2_c b2 b3 P H3)))⟩)⟩)
  · obtain ⟨_, H9⟩ := H8
    obtain ⟨H10, H11⟩ := H9
    obtain ⟨H12, H13⟩ := H11
    exact H6 (col3_c b2 b3 b0 b1 Q H10 (col_permutation_5_c b2 b0 b3 (col_permutation_4_c b0 b2 b3 H12)) (col_permutation_5_c b2 b1 b3 (col_permutation_4_c b1 b2 b3 H13)) H5)
theorem par_distincts_c :
    ∀ (A B C D : Tpoint), Par A B C D → (Par A B C D ∧ A ≠ B ∧ C ≠ D) := by
  intro b0 b1 b2 b3 b4
  exact ⟨b4, ((by
  rcases b4 with H0 | H0
  · have H1 := par_strict_distinct_c b0 b1 b2 b3 H0
    have H2 := H1
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨_, H5⟩ := H4
    obtain ⟨_, H6⟩ := H5
    obtain ⟨_, H7⟩ := H6
    obtain ⟨_, H8⟩ := H7
    exact ⟨H3, H8⟩
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨_, _⟩ := H4
    exact ⟨H1, H3⟩))⟩

theorem par_not_col_strict_c :
    ∀ (A B C D P : Tpoint), Par A B C D → Col C D P → ¬ Col A B P → Par_strict A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b5 with H2 | H2
  · exact H2
  · obtain ⟨_, H3⟩ := H2
    obtain ⟨H4, H5⟩ := H3
    obtain ⟨H6, H7⟩ := H5
    exact ((b7 (col3_c b2 b3 b0 b1 b4 H4 (col_permutation_5_c b2 b0 b3 (col_permutation_4_c b0 b2 b3 H6)) (col_permutation_5_c b2 b1 b3 (col_permutation_4_c b1 b2 b3 H7)) b6))).elim
theorem col_cop_perp2__pars_c :
    ∀ (P Q A B C D : Tpoint), ¬ Col A B P → Col C D P → Coplanar A B C D → Perp A B P Q → Perp C D P Q → Par_strict A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact par_not_col_strict_c b2 b3 b4 b5 b0 ((let H4 := not_col_distincts_c b2 b3 b0 b6; (let H5 := H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  have H7 := perp_distinct_c b4 b5 b0 b1 b10
  have H9 := H7
  obtain ⟨H10, _⟩ := H9
  have H11 := col_cop__cop_c b2 b3 b4 b5 b0 b8 H10 b7
  have H12 := col_cop__cop_c b2 b3 b5 b4 b0 ((let H12 := perp__coplanar_c b4 b5 b0 b1 b10; (let H13 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_1_c b2 b3 b4 b5 b8))) (Ne.symm H10) ((by colr))
  exact l12_9_c b2 b3 b4 b5 b0 b1 (coplanar_perm_2_c b0 b2 b1 b4 (coplanar_trans_1_c b3 b0 b2 b1 b4 (not_col_permutation_5_c b3 b2 b0 (not_col_permutation_4_c b2 b3 b0 b6)) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_8_c b2 b3 b0 b1 H14))) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_10_c b2 b3 b4 b0 H11))))) (coplanar_perm_2_c b0 b2 b1 b5 (coplanar_trans_1_c b3 b0 b2 b1 b5 (not_col_permutation_5_c b3 b2 b0 (not_col_permutation_4_c b2 b3 b0 b6)) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_8_c b2 b3 b0 b1 H14))) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_10_c b2 b3 b5 b0 H12))))) (coplanar_perm_2_c b0 b3 b1 b4 (coplanar_trans_1_c b2 b0 b3 b1 b4 (not_col_permutation_5_c b2 b3 b0 b6) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_2_c b2 b3 b0 b1 H14))) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_4_c b2 b3 b4 b0 H11))))) (coplanar_perm_2_c b0 b3 b1 b5 (coplanar_trans_1_c b2 b0 b3 b1 b5 (not_col_permutation_5_c b2 b3 b0 b6) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_2_c b2 b3 b0 b1 H14))) ((let H13 := perp__coplanar_c b4 b5 b0 b1 b10; (let H14 := perp__coplanar_c b2 b3 b0 b1 b9; coplanar_perm_4_c b2 b3 b5 b0 H12))))) b9 b10)))) b7 b6

theorem all_one_side_par_strict_c :
    ∀ (A B C D : Tpoint), C ≠ D → (∀ (P : Tpoint), Col C D P → OS A B C P) → Par_strict A B C D := sorry
theorem par_col_par_2_c :
    ∀ (A B C D P : Tpoint), A ≠ P → Col A B P → Par A B C D → Par A P C D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  par_symmetry_c b2 b3 b0 b4 ((let H2 := par_symmetry_c b0 b1 b2 b3 b7; par_col_par_c b2 b3 b0 b1 b4 b5 H2 b6))

theorem par_col2_par_c :
    ∀ (A B C D E F : Tpoint), E ≠ F → Par A B C D → Col C D E → Col C D F → Par A B E F := sorry
theorem par_col2_par_bis_c :
    ∀ (A B C D E F : Tpoint), E ≠ F → Par A B C D → Col E F C → Col E F D → Par A B E F := sorry

theorem par_strict_col_par_strict_c :
    ∀ (A B C D E : Tpoint), C ≠ E → Par_strict A B C D → Col C D E → Par_strict A B C E := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have H2 := par_col_par_2_c b2 b3 b0 b1 b4 b5 b7 (par_symmetry_c b0 b1 b2 b3 (Or.inl b6))
  rcases H2 with H3 | H3
  · exact par_strict_symmetry_c b2 b4 b0 b1 H3
  · obtain ⟨_, H4⟩ := H3
    obtain ⟨_, H5⟩ := H4
    obtain ⟨H6, _⟩ := H5
    obtain ⟨_, H7⟩ := b6
    exact ((H7 (⟨b2, (⟨H6, ((by colr))⟩)⟩))).elim

theorem par_strict_col2_par_strict_c :
    ∀ (A B C D E F : Tpoint), E ≠ F → Par_strict A B C D → Col C D E → Col C D F → Par_strict A B E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have H3 := par_strict_distinct_c b0 b1 b2 b3 b7
  have H4 := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H7⟩ := H5
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H6, H11⟩ := b7
  exact ⟨(col2_cop__cop_c b0 b1 b2 b3 b4 b5 H6 H10 b8 b9), ((fun H12 => H11 ((by
  obtain ⟨X, H13⟩ := H12
  obtain ⟨H14, H15⟩ := H13
  exact ⟨X, (⟨H14, ((by colr))⟩)⟩))))⟩

theorem line_dec_c :
    ∀ (B1 B2 C1 C2 : Tpoint), (Col C1 B1 B2 ∧ Col C2 B1 B2) ∨ ¬ (Col C1 B1 B2 ∧ Col C2 B1 B2) := by
  intro b0 b1 b2 b3
  have o := col_dec_c b2 b0 b1
  rcases o with H | H
  · have o0 := col_dec_c b3 b0 b1
    rcases o0 with H0 | H0
    · exact Or.inl (⟨H, H0⟩)
    · exact Or.inr ((fun H1 => (by
  obtain ⟨_, H3⟩ := H1
  have H2 := H0 H3
  exact (H2).elim)))
  · have o0 := col_dec_c b3 b0 b1
    rcases o0 with _ | H0
    · exact Or.inr ((fun H1 => (by
  obtain ⟨H2, _⟩ := H1
  have H3 := H H2
  exact (H3).elim)))
    · exact Or.inr ((fun H1 => (by
  obtain ⟨H2, H3⟩ := H1
  have H4 := H H2
  have H5 := H0 H3
  exact (H4).elim)))

theorem par_distinct_c :
    ∀ (A B C D : Tpoint), Par A B C D → A ≠ B ∧ C ≠ D := by
  intro b0 b1 b2 b3 b4
  rcases b4 with H0 | H0
  · have H1 := par_strict_distinct_c b0 b1 b2 b3 H0
    obtain ⟨H2, H3⟩ := H1
    obtain ⟨_, H4⟩ := H3
    obtain ⟨_, H5⟩ := H4
    obtain ⟨_, H6⟩ := H5
    obtain ⟨_, H7⟩ := H6
    exact ⟨((fun H8 => (let H9 := H2 H8; (H9).elim))), ((fun H8 => (let H9 := H7 H8; (H9).elim)))⟩
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨_, _⟩ := H4
    exact ⟨((fun H5 => (let H6 := H1 H5; (H6).elim))), ((fun H5 => (let H6 := H3 H5; (H6).elim)))⟩

theorem par_col4__par_c :
    ∀ (A B C D E F G H : Tpoint), E ≠ F → G ≠ H → Par A B C D → Col A B E → Col A B F → Col C D G → Col C D H → Par E F G H :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 =>
  par_col2_par_c b4 b5 b2 b3 b6 b7 b9 (par_symmetry_c b2 b3 b4 b5 (par_col2_par_c b2 b3 b0 b1 b4 b5 b8 (par_symmetry_c b0 b1 b2 b3 b10) b11 b12)) b13 b14

theorem par_strict_col4__par_strict_c :
    ∀ (A B C D E F G H : Tpoint), E ≠ F → G ≠ H → Par_strict A B C D → Col A B E → Col A B F → Col C D G → Col C D H → Par_strict E F G H :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 =>
  par_strict_col2_par_strict_c b4 b5 b2 b3 b6 b7 b9 (par_strict_symmetry_c b2 b3 b4 b5 (par_strict_col2_par_strict_c b2 b3 b0 b1 b4 b5 b8 (par_strict_symmetry_c b0 b1 b2 b3 b10) b11 b12)) b13 b14

theorem par_strict_one_side_c :
    ∀ (A B C D P : Tpoint), Par_strict A B C D → Col C D P → OS A B C P := by
  intro b0 b1 b2 b3 b4 b5 b6
  have o := point_equality_decidability b2 b4
  rcases o with x | x
  · subst x
    have HPar0 := par_strict_not_col_1_c b0 b1 b2 b3 b5
    exact one_side_reflexivity_c b0 b1 b2 (not_col_permutation_5_c b2 b1 b0 (not_col_permutation_3_c b0 b1 b2 HPar0))
  · exact l12_6_c b0 b1 b2 b4 (par_strict_col_par_strict_c b0 b1 b2 b3 b4 x b5 b6)

theorem par_strict_all_one_side_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → (∀ (P : Tpoint), Col C D P → OS A B C P) :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  par_strict_one_side_c b0 b1 b2 b3 b5 b4 b6

theorem inter_distincts_c :
    ∀ (A B C D X : Tpoint), Inter A B C D X → A ≠ B ∧ C ≠ D := sorry
theorem inter_trivial_c :
    ∀ (A B X : Tpoint), ¬ Col A B X → Inter A X B X X := by
  intro b0 b1 b2 b3
  have H0 := not_col_distincts_c b0 b1 b2 b3
  have H1 := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H4⟩ := H2
  obtain ⟨H3, _⟩ := H4
  exact ⟨H3, (⟨(⟨b1, (⟨(col_trivial_1_c b1 b2), ((fun H5 => b3 (col_permutation_5_c b0 b2 b1 (col_permutation_1_c b1 b0 b2 H5))))⟩)⟩), (⟨(col_trivial_2_c b0 b2), (col_trivial_2_c b1 b2)⟩)⟩)⟩
theorem inter_sym_c :
    ∀ (A B C D X : Tpoint), Inter A B C D X → Inter C D A B X := sorry

theorem inter_left_comm_c :
    ∀ (A B C D X : Tpoint), Inter A B C D X → Inter B A C D X := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := b5
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨P, H6⟩ := H2
  obtain ⟨H7, H8⟩ := H6
  exact ⟨H0, (⟨(⟨P, (⟨H7, ((fun H9 => H8 (col_permutation_5_c P b1 b0 H9)))⟩)⟩), (⟨(col_permutation_5_c b1 b4 b0 (col_permutation_1_c b0 b1 b4 H4)), H5⟩)⟩)⟩
theorem inter_right_comm_c :
    ∀ (A B C D X : Tpoint), Inter A B C D X → Inter A B D C X := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := b5
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨P, H6⟩ := H2
  obtain ⟨H7, H8⟩ := H6
  exact ⟨(Ne.symm H0), (⟨(⟨P, (⟨(col_permutation_5_c P b2 b3 H7), H8⟩)⟩), (⟨H4, (col_permutation_5_c b3 b4 b2 (col_permutation_1_c b2 b3 b4 H5))⟩)⟩)⟩
theorem inter_comm_c :
    ∀ (A B C D X : Tpoint), Inter A B C D X → Inter B A D C X :=
  fun b0 b1 b2 b3 b4 b5 =>
  inter_left_comm_c b0 b1 b3 b2 b4 (inter_right_comm_c b0 b1 b2 b3 b4 b5)

theorem l12_17_c :
    ∀ (A B C D P : Tpoint), A ≠ B → Midpoint P A C → Midpoint P B D → Par A B C D := sorry
theorem l12_18_a_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → Par A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H5 := l7_21_c b0 b1 b2 b3 b4 b7 b8 b5 b6 b9 b10
  obtain ⟨H6, H7⟩ := H5
  exact l12_17_c b0 b1 b2 b3 b4 ((fun H8 => (by
  subst H8
  exact b7 ((by colr))))) H6 H7

theorem l12_18_b_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → Par B C D A := sorry
theorem l12_18_c_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → TS B D A C := sorry
theorem l12_18_d_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → TS A C B D := sorry
theorem l12_18_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → Par A B C D ∧ Par B C D A ∧ TS B D A C ∧ TS A C B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨(l12_18_a_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (⟨(l12_18_b_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (⟨(l12_18_c_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (l12_18_d_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10)⟩)⟩)⟩

theorem par_two_sides_two_sides_c :
    ∀ (A B C D : Tpoint), Par A B C D → TS B D A C → TS A C B D := sorry
theorem par_one_or_two_sides_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → TS A C B D ∧ TS B D A C ∨ OS A C B D ∧ OS B D A C := sorry
theorem l12_21_b_c :
    ∀ (A B C D : Tpoint), TS A C B D → CongA B A C D C A → Par A B C D := sorry
theorem l12_22_aux_c :
    ∀ (A B C D P : Tpoint), P ≠ A → A ≠ C → Bet P A C → OS P A B D → CongA B A P D C P → Par A B C D := sorry
theorem l12_22_b_c :
    ∀ (A B C D P : Tpoint), Out P A C → OS P A B D → CongA B A P D C P → Par A B C D := sorry
theorem par_strict_par_c :
    ∀ (A B C D : Tpoint), Par_strict A B C D → Par A B C D :=
  fun b0 b1 b2 b3 b4 =>
  Or.inl b4
theorem col_par_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Col A B C → Par A B B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  Or.inr (⟨((fun H2 => (let H3 := b3 H2; (H3).elim))), (⟨((fun H2 => (let H3 := b4 H2; (H3).elim))), (⟨b5, (col_trivial_1_c b1 b2)⟩)⟩)⟩)
theorem acute_col_perp__out_c :
    ∀ (A B C A' : Tpoint), Acute A B C → Col B C A' → Perp B C A A' → Out B A' C := sorry
theorem acute_col_perp__out_1_c :
    ∀ (A B C A' : Tpoint), Acute A B C → Col B C A' → Perp B A A A' → Out B A' C := sorry

theorem conga_cop_inangle_per2__inangle_c :
    ∀ (A B C P T : Tpoint), Per A B C → InAngle T A B C → CongA P B A P B C → Per B P T → Coplanar A B C P → InAngle P A B C := sorry

theorem perp_not_par_c :
    ∀ (A B X Y : Tpoint), Perp A B X Y → ¬ Par A B X Y := sorry

theorem cong_conga_perp_c :
    ∀ (A B C P : Tpoint), TS B P A C → Cong A B C B → CongA A B P C B P → Perp A C B P := sorry
theorem perp_inter_exists_c :
    ∀ (A B C D : Tpoint), Perp A B C D → ∃ (P : Tpoint), Col A B P ∧ Col C D P := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  obtain ⟨x7, x8⟩ := x6
  exact ⟨x, (⟨((by colr)), ((by colr))⟩)⟩

theorem perp_inter_perp_in_c :
    ∀ (A B C D : Tpoint), Perp A B C D → ∃ (P : Tpoint), Col A B P ∧ Col C D P ∧ Perp_at P A B C D := by
  intro b0 b1 b2 b3 b4
  have HH := perp_inter_exists_c b0 b1 b2 b3 b4
  obtain ⟨P, H0⟩ := HH
  obtain ⟨H1, H2⟩ := H0
  exact ⟨P, (⟨H1, (⟨H2, (l8_14_2_1b_bis_c b0 b1 b2 b3 P b4 ((by colr)) ((by colr)))⟩)⟩)⟩

theorem l12_9_2D_c :
    ∀ (A1 A2 B1 B2 C1 C2 : Tpoint), Perp A1 A2 C1 C2 → Perp B1 B2 C1 C2 → Par A1 A2 B1 B2 := sorry

#print axioms GeocoqTranslate.Tarski.Base.par_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_irreflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_strict_id_c
#print axioms GeocoqTranslate.Tarski.Base.par_id_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_not_col_1_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_not_col_2_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_not_col_3_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_not_col_4_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_not_cols_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.par_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_comm_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.par_neq1_c
#print axioms GeocoqTranslate.Tarski.Base.par_neq2_c
#print axioms GeocoqTranslate.Tarski.Base.Par_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Par_perm_c
#print axioms GeocoqTranslate.Tarski.Base.Par_strict_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Par_strict_perm_c
#print axioms GeocoqTranslate.Tarski.Base.l12_6_c
#print axioms GeocoqTranslate.Tarski.Base.pars__os3412_c
#print axioms GeocoqTranslate.Tarski.Base.perp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop2_perp2__col_c
#print axioms GeocoqTranslate.Tarski.Base.col_perp2_ncol__col_c
#print axioms GeocoqTranslate.Tarski.Base.l12_9_c
#print axioms GeocoqTranslate.Tarski.Base.parallel_existence_c
#print axioms GeocoqTranslate.Tarski.Base.par_col_par_c
#print axioms GeocoqTranslate.Tarski.Base.parallel_existence1_c
#print axioms GeocoqTranslate.Tarski.Base.par_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par1_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par2_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par_c
#print axioms GeocoqTranslate.Tarski.Base.col2_par__col4_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_inter_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.inter_uniqueness_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.col_not_col_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.par_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.par_not_col_strict_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop_perp2__pars_c
#print axioms GeocoqTranslate.Tarski.Base.all_one_side_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.par_col_par_2_c
#print axioms GeocoqTranslate.Tarski.Base.par_col2_par_c
#print axioms GeocoqTranslate.Tarski.Base.par_col2_par_bis_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_col_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_col2_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.line_dec_c
#print axioms GeocoqTranslate.Tarski.Base.par_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.par_col4__par_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_col4__par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_all_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.inter_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.inter_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.inter_sym_c
#print axioms GeocoqTranslate.Tarski.Base.inter_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.inter_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.inter_comm_c
#print axioms GeocoqTranslate.Tarski.Base.l12_17_c
#print axioms GeocoqTranslate.Tarski.Base.l12_18_a_c
#print axioms GeocoqTranslate.Tarski.Base.l12_18_b_c
#print axioms GeocoqTranslate.Tarski.Base.l12_18_c_c
#print axioms GeocoqTranslate.Tarski.Base.l12_18_d_c
#print axioms GeocoqTranslate.Tarski.Base.l12_18_c
#print axioms GeocoqTranslate.Tarski.Base.par_two_sides_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.par_one_or_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.l12_21_b_c
#print axioms GeocoqTranslate.Tarski.Base.l12_22_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l12_22_b_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_par_c
#print axioms GeocoqTranslate.Tarski.Base.col_par_c
#print axioms GeocoqTranslate.Tarski.Base.acute_col_perp__out_c
#print axioms GeocoqTranslate.Tarski.Base.acute_col_perp__out_1_c
#print axioms GeocoqTranslate.Tarski.Base.conga_cop_inangle_per2__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.perp_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.cong_conga_perp_c
#print axioms GeocoqTranslate.Tarski.Base.perp_inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.perp_inter_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.l12_9_2D_c
end GeocoqTranslate.Tarski.Base