import GeocoqTranslate.Tarski_dev.Ch11
import GeocoqTranslate.Tarski_dev.TarskiFinish
import GeocoqTranslate.Tarski_dev.TarskiConA

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
  intro b0 b1 H
  obtain ⟨_, H0⟩ := H
  exact H0 (⟨b0, (⟨(col_trivial_1_c b0 b1), (col_trivial_1_c b0 b1)⟩)⟩)
theorem not_par_strict_id_c :
    ∀ (A B C : Tpoint), ¬ Par_strict A B A C := by
  intro b0 b1 b2 H
  obtain ⟨_, H0⟩ := H
  exact H0 (⟨b0, (⟨(col_trivial_1_c b0 b1), (col_trivial_1_c b0 b2)⟩)⟩)
theorem par_id_c :
    ∀ (A B C : Tpoint), Par A B A C → Col A B C :=
  fun A B C H =>
  Or.elim H
    (fun H0 : Par_strict A B A C =>
      False.elim (not_par_strict_id_c A B C H0))
    (fun H0 : A ≠ B ∧ A ≠ C ∧ Col A A C ∧ Col B A C =>
      let ⟨_, _, _, H3⟩ := H0
      col_permutation_5_c A C B (col_permutation_1_c B A C H3))
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
    ∀ (A B C D : Tpoint), Par_strict A B C D → A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := by
  intro A B C D ⟨_, hX⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hAB; apply hX; exact ⟨C, by subst hAB; exact ⟨col_trivial_2_c C A, col_trivial_1_c C D⟩⟩
  · intro hAC; apply hX; exact ⟨A, by subst hAC; exact ⟨col_trivial_1_c A B, col_trivial_1_c A D⟩⟩
  · intro hAD; apply hX; exact ⟨A, by subst hAD; exact ⟨col_trivial_1_c A B, col_trivial_3_c A C⟩⟩
  · intro hBC; apply hX; exact ⟨B, by subst hBC; exact ⟨col_trivial_3_c B A, col_trivial_1_c B D⟩⟩
  · intro hBD; apply hX; exact ⟨B, by subst hBD; exact ⟨col_trivial_3_c B A, col_trivial_3_c B C⟩⟩
  · intro hCD; apply hX; exact ⟨B, by subst hCD; exact ⟨col_trivial_3_c B A, col_trivial_2_c B C⟩⟩
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
    ∀ (A B C D : Tpoint), Par_strict A B C D → OS A B C D :=
  fun A B C D H =>
  let ⟨H0, H1⟩ := H
  let HH := cop_nts_os_c A B C D
  HH H0
    (fun H2 : Col C A B => H1 ⟨C, H2, col_trivial_1_c C D⟩)
    (fun H2 : Col D A B => H1 ⟨D, H2, col_trivial_3_c D C⟩)
    (fun H2 : TS A B C D =>
      let ⟨_, _, T, H6, H7⟩ := H2
      H1 ⟨T, H6, col_permutation_4_c C T D (bet_col_c C T D H7)⟩)
theorem perp_dec_c :
    ∀ (A B C D : Tpoint), Perp A B C D ∨ ¬ Perp A B C D := by
  intro b0 b1 b2 b3
  have o := col_dec_c b0 b1 b2
  rcases o with H | H
  · have o0 := perp_in_dec_c b2 b0 b1 b2 b3
    rcases o0 with H0 | H0
    · exact Or.inl (l8_14_2_1a_c b2 b0 b1 b2 b3 H0)
    · exact Or.inr ((fun H1 => H0 (perp_in_right_comm_c b0 b1 b3 b2 b2 (l8_15_1_c b0 b1 b3 b2 ((let H2 := perp_distinct_c b0 b1 b2 b3 H1; (by
  obtain ⟨_, _⟩ := H2
  exact H))) (perp_right_comm_c b0 b1 b2 b3 H1)))))
  · obtain ⟨P, HP⟩ := (l8_18_existence_c b0 b1 b2 H)
    obtain ⟨H0, H1⟩ := HP
    have o0 := point_equality_decidability b2 b3
    rcases o0 with H2 | H2
    · rw [H2] at *
      exact Or.inr ((fun H3 => (let H4 := perp_distinct_c b0 b1 b3 b3 H3; (by
  obtain ⟨_, H5⟩ := H4
  have H6 := (let H6 := rfl; H5 H6)
  exact (H6).elim))))
    · have o1 := col_dec_c P b2 b3
      rcases o1 with H3 | H3
      · exact Or.inl ((let H4 := perp_distinct_c b0 b1 b2 P H1; (by
  obtain ⟨_, _⟩ := H4
  exact perp_col1_c b0 b1 b2 P b3 H2 H1 ((by colr)))))
      · exact Or.inr ((fun H4 => H3 ((by colr))))
theorem l12_9_c :
    ∀ (A1 A2 B1 B2 C1 C2 : Tpoint), Coplanar C1 C2 A1 B1 → Coplanar C1 C2 A1 B2 → Coplanar C1 C2 A2 B1 → Coplanar C1 C2 A2 B2 → Perp A1 A2 C1 C2 → Perp B1 B2 C1 C2 → Par A1 A2 B1 B2 := by
  intro A1 A2 B1 B2 C1 C2 hCopA1B1 hCopA1B2 hCopA2B1 hCopA2B2 hPerpA hPerpB
  obtain ⟨hA1A2, hC1C2⟩ := perp_distinct_c A1 A2 C1 C2 hPerpA
  obtain ⟨hB1B2, _⟩ := perp_distinct_c B1 B2 C1 C2 hPerpB
  rcases col_dec_c A1 B1 B2 with hCol | hNCol
  · apply Or.inr
    refine ⟨hA1A2, hB1B2, hCol, ?_⟩
    rcases point_equality_decidability A1 B2 with hEq | hNe
    · subst hEq
      have h1 : Col A1 A2 B1 :=
        cop_perp2_col_c A1 A2 B1 C1 C2 hCopA2B1 hPerpA (perp_left_comm_c B1 A1 C1 C2 hPerpB)
      colr
    · have hPerpAB2 : Perp A1 B2 C1 C2 :=
        perp_left_comm_c B2 A1 C1 C2
          (perp_col_c B2 B1 C1 C2 A1 hNe.symm (perp_left_comm_c B1 B2 C1 C2 hPerpB) (by colr))
      rcases point_equality_decidability A1 B1 with hEq2 | hNe2
      · subst hEq2
        have h2 : Col A1 A2 B2 := cop_perp2_col_c A1 A2 B2 C1 C2 hCopA2B2 hPerpA hPerpAB2
        colr
      · have hPerpAB1 : Perp A1 B1 C1 C2 :=
          perp_left_comm_c B1 A1 C1 C2
            (perp_col_c B1 B2 C1 C2 A1 hNe2.symm hPerpB (by colr))
        have h3 : Col A1 A2 B1 := cop_perp2_col_c A1 A2 B1 C1 C2 hCopA2B1 hPerpA hPerpAB1
        colr
  · apply Or.inl
    constructor
    · have hPnc : ¬ Col C1 C2 A1 ∨ ¬ Col C1 C2 A2 :=
        perp_not_col2_c C1 C2 A1 A2 (perp_sym_c A1 A2 C1 C2 hPerpA)
      rcases hPnc with hNCol1 | hNCol2
      · have hTriv : Coplanar C1 C2 A1 A1 :=
          coplanar_perm_4_c C1 A1 A1 C2 (col_coplanar_c C1 A1 A1 C2 (col_trivial_2_c C1 A1))
        have hCopA1A2 : Coplanar C1 C2 A1 A2 :=
          coplanar_perm_16_c A1 A2 C1 C2 (perp_coplanar_c A1 A2 C1 C2 hPerpA)
        exact coplanar_pseudo_trans_c A1 A2 B1 B2 C1 C2 A1 hNCol1 hTriv hCopA1A2 hCopA1B1 hCopA1B2
      · have hTriv : Coplanar C1 C2 A2 A2 :=
          coplanar_perm_4_c C1 A2 A2 C2 (col_coplanar_c C1 A2 A2 C2 (col_trivial_2_c C1 A2))
        have hCopA2A1 : Coplanar C1 C2 A2 A1 :=
          coplanar_perm_17_c A1 A2 C1 C2 (perp_coplanar_c A1 A2 C1 C2 hPerpA)
        exact coplanar_pseudo_trans_c A1 A2 B1 B2 C1 C2 A2 hNCol2 hCopA2A1 hTriv hCopA2B1 hCopA2B2
    · rintro ⟨X, hXA, hXB⟩
      apply hNCol
      rcases point_equality_decidability X A1 with hXeq | hXne
      · subst hXeq
        exact hXB
      · have hPerpXA1 : Perp X A1 C1 C2 :=
          perp_left_comm_c A1 X C1 C2
            (perp_col_c A1 A2 C1 C2 X hXne.symm hPerpA (by colr))
        rcases point_equality_decidability X B1 with hXeq2 | hXne2
        · subst hXeq2
          have h4 : Col X A1 B2 := cop_perp2_col_c X A1 B2 C1 C2 hCopA1B2 hPerpXA1 hPerpB
          colr
        · have hPerpXB1 : Perp X B1 C1 C2 :=
            perp_left_comm_c B1 X C1 C2
              (perp_col_c B1 B2 C1 C2 X hXne2.symm hPerpB (by colr))
          have h5 : Col X A1 B1 := cop_perp2_col_c X A1 B1 C1 C2 hCopA1B1 hPerpXA1 hPerpXB1
          colr
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
  exact ⟨(col_cop_cop_c b0 b1 b2 b3 b4 H10 H9 b7), ((fun H12 => H11 ((by
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
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B C :=
  fun A B C D X H H0 H1 =>
  Or.elim H
    (fun H2 : Par_strict A B C D =>
      And.elim
        (fun _ (H3 : ¬ ∃ X0, Col X0 A B ∧ Col X0 C D) =>
          let H4 : ∃ X0, Col X0 A B ∧ Col X0 C D :=
            ⟨X, ⟨col_permutation_5_c X B A (col_permutation_3_c A B X H0),
                 col_permutation_5_c X D C (col_permutation_3_c C D X H1)⟩⟩
          False.elim (H3 H4))
        H2)
    (fun H2 : A ≠ B ∧ C ≠ D ∧ Col A C D ∧ Col B C D =>
      And.elim
        (fun _ (H3 : C ≠ D ∧ Col A C D ∧ Col B C D) =>
          And.elim
            (fun (H4 : C ≠ D) (H5 : Col A C D ∧ Col B C D) =>
              And.elim
                (fun (H6 : Col A C D) (H7 : Col B C D) =>
                  col_permutation_1_c C A B
                    (col_transitivity_1_c C D A B H4
                      (col_permutation_5_c C A D (col_permutation_4_c A C D H6))
                      (col_permutation_5_c C B D (col_permutation_4_c B C D H7))))
                H5)
            H3)
        H2)
theorem not_strict_par2_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  not_strict_par1_c b0 b1 b3 b2 b4 (par_right_comm_c b0 b1 b2 b3 b5) b6 ((by colr))
theorem not_strict_par_c :
    ∀ (A B C D X : Tpoint), Par A B C D → Col A B X → Col C D X → Col A B C ∧ Col A B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨(not_strict_par1_c b0 b1 b2 b3 b4 b5 b6 b7), (not_strict_par2_c b0 b1 b2 b3 b4 b5 b6 b7)⟩
theorem not_par_not_col_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → ¬ Par A B A C → ¬ Col A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  (fun H2 => b5 (Or.inr (⟨b3, (⟨b4, (⟨(col_trivial_1_c b0 b2), (col_permutation_5_c b1 b2 b0 (col_permutation_1_c b0 b1 b2 H2))⟩)⟩)⟩)))
theorem not_par_inter_uniqueness_c :
    ∀ (A B C D X Y : Tpoint), A ≠ B → C ≠ D → ¬ Par A B C D → Col A B X → Col C D X → Col A B Y → Col C D Y → X = Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  have o := point_equality_decidability b2 b5
  rcases o with H6 | H6
  · rw [H6] at *
    have o0 := point_equality_decidability b2 b4
    rcases o0 with H9 | H9
    · rw [H9] at *
      exact rfl
    · exact l6_21_c b2 b3 b0 b1 b4 b2 ((fun H10 => b8 (Or.inr (⟨b6, (⟨b7, (⟨((by colr)), ((let H11 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H12 := (((b4 , BinNums.xI (BinNums.xO BinNums.xH)))) % list; (let H13 := interp H12 b4; fun H14 H15 H16 => (let H17 := (by colr); fun H18 H19 H20 H21 H22 => (let H23 := (by colr); (by colr)))))) b6 b7 H9 b9 b10 b12 b11 H10))⟩)⟩)⟩)))) b6 b10 b12 b9 b11
  · exact l6_21_c b0 b1 b2 b3 b4 b5 ((fun H7 => b8 (Or.inr (⟨b6, (⟨b7, (⟨((let H8 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H9 := (((b5 , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H10 := interp H9 b5; fun H11 H12 H13 => (let H14 := (by colr); fun H15 H16 H17 H18 H19 => (let H20 := (by colr); (by colr)))))) b6 b7 H6 b9 b10 b11 b12 H7)), ((let H8 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H9 := (((b5 , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H10 := interp H9 b5; fun H11 H12 H13 => (let H14 := (by colr); fun H15 H16 H17 H18 H19 => (let H20 := (by colr); (by colr)))))) b6 b7 H6 b9 b10 b11 b12 H7))⟩)⟩)⟩)))) b7 b9 b11 b10 b12
theorem inter_uniqueness_not_par_c :
    ∀ (A B C D P : Tpoint), ¬ Col A B C → Col A B P → Col C D P → ¬ Par A B C D := by
  intro H2
  rcases H2 with H3 | H3
  · obtain ⟨_, H4⟩ := H3
    exact H4 (⟨b4, (⟨((by colr)), ((by colr))⟩)⟩)
  · obtain ⟨H4, H5⟩ := H3
    obtain ⟨H6, H7⟩ := H5
    obtain ⟨H8, H9⟩ := H7
    exact b5 ((let H10 := not_col_distincts_c b0 b1 b2 b5; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H12
  obtain ⟨H14, H15⟩ := H13
  have H16 := tarski_to_col_theory.Tarski_is_a_Col_theory
  exact ((let H17 := (((b4 , BinNums.xI (BinNums.xO BinNums.xH)))) % list; (let H18 := interp H17 b4; fun H19 H20 H21 H22 => (let H23 := (by colr); fun H24 H25 H26 H27 => (let H28 := (by colr); (by colr)))))) H4 H6 H14 H15 b6 b7 H8 H9))))
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
theorem all_one_side_par_strict_c :
    ∀ (A B C D : Tpoint), C ≠ D → (∀ (P : Tpoint), Col C D P → OS A B C P) → Par_strict A B C D := sorry

theorem par_col_par_2_c :
    ∀ (A B C D P : Tpoint), A ≠ P → Col A B P → Par A B C D → Par A P C D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  par_symmetry_c b2 b3 b0 b4 ((let H2 := par_symmetry_c b0 b1 b2 b3 b7; par_col_par_c b2 b3 b0 b1 b4 b5 H2 b6))
theorem par_col2_par_c :
    ∀ (A B C D E F : Tpoint), E ≠ F → Par A B C D → Col C D E → Col C D F → Par A B E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have o := point_equality_decidability b2 b4
  rcases o with H3 | H3
  · rw [H3] at *
    exact par_col_par_c b0 b1 b2 b3 b5 b6 b7 b9
  · exact par_col_par_c b0 b1 b4 b2 b5 b6 (par_right_comm_c b0 b1 b2 b4 (par_col_par_c b0 b1 b2 b3 b4 H3 b7 b8)) ((by colr))
theorem par_col2_par_bis_c :
    ∀ (A B C D E F : Tpoint), E ≠ F → Par A B C D → Col E F C → Col E F D → Par A B E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  par_col2_par_c b0 b1 b2 b3 b4 b5 b6 b7 ((let H3 := par_neq1_c b0 b1 b2 b3 b7; (let H4 := par_neq2_c b0 b1 b2 b3 b7; (let H5 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H6 := (((b5 , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H7 := interp H6 b5; fun H8 H9 H10 => (let H11 := (by colr); fun H12 H13 => (let H14 := (by colr); (by colr)))))) b6 H3 H4 b8 b9)))) ((let H3 := par_neq1_c b0 b1 b2 b3 b7; (let H4 := par_neq2_c b0 b1 b2 b3 b7; (let H5 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H6 := (((b5 , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H7 := interp H6 b5; fun H8 H9 H10 => (let H11 := (by colr); fun H12 H13 => (let H14 := (by colr); (by colr)))))) b6 H3 H4 b8 b9))))
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
  exact ⟨(col2_cop_cop_c b0 b1 b2 b3 b4 b5 H6 H10 b8 b9), ((fun H12 => H11 ((by
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
    ∀ (A B C D X : Tpoint), Inter A B C D X → A ≠ B ∧ C ≠ D := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨x, x0⟩ := b5
  obtain ⟨x1, x2⟩ := x0
  exact ((by
  obtain ⟨x3, x4⟩ := x1
  obtain ⟨x5, x6⟩ := x4
  exact fun _ => (let H4 := not_col_distincts_c x3 b0 b1 x6; (let H5 := H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  exact ⟨H8, x⟩))))) x2
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
    ∀ (A B C D X : Tpoint), Inter A B C D X → Inter C D A B X := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := b5
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨P, H6⟩ := H2
  obtain ⟨H7, H8⟩ := H6
  have H9 := (fun H9 => (by
  rw [H9] at *
  exact H8 (col_trivial_2_c P b0)))
  exact ⟨H9, (⟨((let o := point_equality_decidability b0 b4; (by
  rcases o with H10 | H10
  · rw [H10] at *
    exact ⟨b1, (⟨(col_trivial_3_c b1 b0), ((fun H12 => H8 (col3_c b2 b3 P b0 b1 H0 ((by colr)) H5 ((by colr)))))⟩)⟩
  · exact ⟨b0, (⟨(col_trivial_1_c b0 b1), ((fun H11 => H8 ((let H12 := col3_c b2 b3 b0 P b4 H0 ((by colr)) ((by colr)) H5; (let H13 := not_col_distincts_c P b0 b1 H8; (let H14 := H13; (by
  obtain ⟨_, H15⟩ := H14
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨_, H18⟩ := H17
  have H19 := tarski_to_col_theory.Tarski_is_a_Col_theory
  exact ((let H20 := (((P , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H21 := interp H20 P; fun H22 H23 H24 H25 H26 => (let H27 := (by colr); fun H28 H29 H30 H31 H32 => (let H33 := (by colr); (by colr)))))) H0 H9 H10 H16 H18 H4 H5 H7 H11 H12)))))))⟩)⟩))), (⟨H5, H4⟩)⟩)⟩
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
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → Par B C D A := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H5 := l7_21_c b0 b1 b2 b3 b4 b7 b8 b5 b6 b9 b10
  exact l12_18_a_c b1 b2 b3 b0 b4 b6 ((by cong_r)) ((fun H6 => b7 ((let H7 : Col b1 b2 b4 := (by colr); (by colr))))) ((fun H6 => (by
  rw [H6] at *
  exact b7 (col_trivial_3_c b0 b1)))) b10 ((by colr))
theorem l12_18_c_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → TS B D A C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H5 := l7_21_c b0 b1 b2 b3 b4 b7 b8 b5 b6 b9 b10
  exact ⟨((fun H6 => b7 ((let H7 : Col b0 b1 b4 := (by colr); (by colr))))), (⟨((fun H6 => b7 ((let H7 : Col b1 b4 b2 := (by colr); (by colr))))), (⟨b4, (⟨((by colr)), ((by
  obtain ⟨H6, _⟩ := H5
  obtain ⟨H7, _⟩ := H6
  exact H7))⟩)⟩)⟩)⟩
theorem l12_18_d_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → TS A C B D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H5 := l7_21_c b0 b1 b2 b3 b4 b7 b8 b5 b6 b9 b10
  exact l12_18_c_c b1 b0 b3 b2 b4 ((by cong_r)) ((by cong_r)) ((fun H6 => b7 ((let H7 : Col b0 b1 b4 := (by colr); (by colr))))) ((fun H6 => (by
  rw [H6] at *
  exact b7 (col_trivial_3_c b0 b1)))) b10 b9
theorem l12_18_c :
    ∀ (A B C D P : Tpoint), Cong A B C D → Cong B C D A → ¬ Col A B C → B ≠ D → Col A P C → Col B P D → Par A B C D ∧ Par B C D A ∧ TS B D A C ∧ TS A C B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨(l12_18_a_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (⟨(l12_18_b_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (⟨(l12_18_c_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10), (l12_18_d_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10)⟩)⟩)⟩
theorem par_two_sides_two_sides_c :
    ∀ (A B C D : Tpoint), Par A B C D → TS B D A C → TS A C B D := by
  intro b0 b1 b2 b3 b4 b5
  have H1 := par_distincts_c b0 b1 b2 b3 b4
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  rcases H2 with H4 | H4
  · have H5 := ts_distincts_c b1 b3 b0 b2 b5
    have H6 := H5
    obtain ⟨_, H7⟩ := H6
    obtain ⟨_, H8⟩ := H7
    obtain ⟨_, H9⟩ := H8
    obtain ⟨_, H10⟩ := H9
    obtain ⟨_, H11⟩ := H10
    obtain ⟨_, H12⟩ := b5
    obtain ⟨H13, H14⟩ := H12
    obtain ⟨T, H15⟩ := H14
    obtain ⟨H16, H17⟩ := H15
    exact ⟨((fun H18 => (let H19 : Col T b1 b2 := (by colr); H13 ((by colr))))), (⟨((fun H18 => (let H19 : Col T b2 b3 := (by colr); H13 ((by colr))))), (⟨T, (⟨((let H18 := bet_col_c b0 T b2 H17; (by colr))), ((by
  rcases H16 with H18 | H18
  · have HH := outer_pasch_c b2 b3 T b0 b1 (between_symmetry H17) (between_symmetry H18)
    obtain ⟨X, H19⟩ := HH
    obtain ⟨H20, H21⟩ := H19
    obtain ⟨_, H22⟩ := H4
    exact ((H22 (⟨X, (⟨((by colr)), ((by colr))⟩)⟩))).elim
  · rcases H18 with H19 | H19
    · have HH := outer_pasch_c b0 b1 T b2 b3 H17 H19
      obtain ⟨X, H20⟩ := HH
      obtain ⟨H21, H22⟩ := H20
      exact (((by
  obtain ⟨_, H23⟩ := H4
  exact H23 (⟨X, (⟨((by colr)), ((by colr))⟩)⟩)))).elim
    · exact between_symmetry H19))⟩)⟩)⟩)⟩
  · obtain ⟨_, H5⟩ := b5
    obtain ⟨H6, _⟩ := H5
    obtain ⟨_, H7⟩ := H4
    obtain ⟨_, H8⟩ := H7
    obtain ⟨_, H9⟩ := H8
    exact ((H6 ((by colr)))).elim
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
theorem perp_not_par_c :
    ∀ (A B X Y : Tpoint), Perp A B X Y → ¬ Par A B X Y := by
  intro b0 b1 b2 b3 b4
  have HH := b4
  obtain ⟨P, H0⟩ := HH
  intro H1
  rcases H1 with H2 | H2
  · have H3 := (by
  obtain ⟨_, x0⟩ := H2
  exact x0)
    exact H3 (⟨P, ((let H4 := perp_in_col_c b0 b1 b2 b3 P H0; (by
  obtain ⟨H5, H6⟩ := H4
  exact ⟨((by colr)), ((by colr))⟩)))⟩)
  · obtain ⟨H3, H4⟩ := H2
    obtain ⟨H5, H6⟩ := H4
    obtain ⟨H7, H8⟩ := H6
    have o := point_equality_decidability b0 b3
    rcases o with H9 | H9
    · rw [H9] at *
      have H14 := l8_14_2_1b_c P b0 b1 b2 b0 b0 H0 (col_trivial_1_c b0 b1) H7
      rw [H14] at *
      have H16 := perp_in_comm_c b0 b1 b2 b0 b0 H0
      have H17 := perp_in_per_c b1 b0 b2 H16
      have H18 := per_not_col_c b1 b0 b2 (Ne.symm H3) (Ne.symm H5) H17
      exact H18 ((by colr))
    · have H10 := fun H10 H11 H12 => (by
  obtain ⟨x, _⟩ := l8_16_1_c b0 b1 b2 b0 b3 H10 H11 H12
  exact x)
      exact H10 ((let H11 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H12 := (((b3 , BinNums.xO (BinNums.xO BinNums.xH)))) % list; (let H13 := interp H12 b3; fun H14 H15 H16 => (let H17 := (by colr); fun H18 H19 => (let H20 := (by colr); (by colr)))))) H3 H5 H9 H7 H8)) (col_trivial_3_c b0 b1) b4 ((let H11 := tarski_to_col_theory.Tarski_is_a_Col_theory; ((let H12 := (((b3 , BinNums.xO (BinNums.xO BinNums.xH)))) % list; (let H13 := interp H12 b3; fun H14 H15 H16 => (let H17 := (by colr); fun H18 H19 => (let H20 := (by colr); (by colr)))))) H3 H5 H9 H7 H8))
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
    ∀ (A1 A2 B1 B2 C1 C2 : Tpoint), Perp A1 A2 C1 C2 → Perp B1 B2 C1 C2 → Par A1 A2 B1 B2 :=
  fun b0 b1 b2 b3 b4 b5 =>
  l12_9_c b0 b1 b2 b3 b4 b5 (all_coplanar_c b4 b5 b0 b2) (all_coplanar_c b4 b5 b0 b3) (all_coplanar_c b4 b5 b1 b2) (all_coplanar_c b4 b5 b1 b3)
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
#print axioms GeocoqTranslate.Tarski.Base.perp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.l12_9_c
#print axioms GeocoqTranslate.Tarski.Base.parallel_existence_c
#print axioms GeocoqTranslate.Tarski.Base.par_col_par_c
#print axioms GeocoqTranslate.Tarski.Base.parallel_existence1_c
#print axioms GeocoqTranslate.Tarski.Base.par_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par1_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par2_c
#print axioms GeocoqTranslate.Tarski.Base.not_strict_par_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_inter_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.inter_uniqueness_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.col_not_col_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.par_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.par_not_col_strict_c
#print axioms GeocoqTranslate.Tarski.Base.all_one_side_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.par_col_par_2_c
#print axioms GeocoqTranslate.Tarski.Base.par_col2_par_c
#print axioms GeocoqTranslate.Tarski.Base.par_col2_par_bis_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_col_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.par_strict_col2_par_strict_c
#print axioms GeocoqTranslate.Tarski.Base.line_dec_c
#print axioms GeocoqTranslate.Tarski.Base.par_distinct_c
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
#print axioms GeocoqTranslate.Tarski.Base.perp_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.cong_conga_perp_c
#print axioms GeocoqTranslate.Tarski.Base.perp_inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.perp_inter_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.l12_9_2D_c
end GeocoqTranslate.Tarski.Base