import GeocoqTranslate.Tarski_dev.Ch12b

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem per2_col_eq_c :
    ∀ (A P P' B : Tpoint), A ≠ P → A ≠ P' → Per A P B → Per A P' B → Col P A P' → P = P' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have o := point_equality_decidability b1 b3
  rcases o with H4 | H4
  · subst H4
    have H6 := l8_9_c b0 b2 b1 b7 (col_permutation_5_c b0 b1 b2 (col_permutation_4_c b1 b0 b2 b8))
    rcases H6 with H7 | H7
    · exact ((b5 H7)).elim
    · exact H7
  · have o0 := point_equality_decidability b2 b3
    rcases o0 with H5 | H5
    · subst H5
      have H7 := l8_9_c b0 b1 b2 b6 (col_permutation_5_c b0 b2 b1 (col_permutation_1_c b1 b0 b2 b8))
      rcases H7 with H8 | H8
      · exact ((b4 H8)).elim
      · exact Eq.symm H8
    · have H6 := per_perp_in_c b0 b1 b3 b4 H4 b6
      have H7 := per_perp_in_c b0 b2 b3 b5 H5 b7
      have H8 := perp_in_comm_c b0 b1 b1 b3 b1 H6
      have H9 := perp_in_comm_c b0 b2 b2 b3 b2 H7
      have H10 := perp_in_perp_bis_c b1 b0 b3 b1 b1 H8
      have H11 := perp_in_perp_bis_c b2 b0 b3 b2 b2 H9
      rcases H10 with H12 | H12
      · rcases H11 with H13 | H13
        · exact l8_18_uniqueness_c b1 b0 b3 b1 b2 (perp_not_col_c b1 b0 b3 H12) (col_trivial_3_c b1 b0) H12 b8 (perp_left_comm_c b0 b1 b3 b2 (perp_col_c b0 b2 b3 b2 b1 b4 (perp_comm_c b2 b0 b2 b3 (perp_comm_c b0 b2 b3 b2 (perp_comm_c b2 b0 b2 b3 (perp_right_comm_c b2 b0 b3 b2 H13)))) (col_permutation_5_c b0 b1 b2 (col_permutation_4_c b1 b0 b2 b8))))
        · have H14 := perp_distinct_c b2 b2 b3 b2 H13
          obtain ⟨H15, _⟩ := H14
          have H16 := (let H16 := rfl; H15 H16)
          exact (H16).elim
      · rcases H11 with _ | _
        · have H13 := perp_distinct_c b1 b1 b3 b1 H12
          obtain ⟨H14, _⟩ := H13
          have H15 := (let H15 := rfl; H14 H15)
          exact (H15).elim
        · have H13 := perp_distinct_c b1 b1 b3 b1 H12
          obtain ⟨H14, _⟩ := H13
          have H15 := (let H15 := rfl; H14 H15)
          exact (H15).elim
theorem per2_preserves_diff_c :
    ∀ (O A B A' B' : Tpoint), O ≠ A' → O ≠ B' → Col O A' B' → Per O A' A → Per O B' B → A' ≠ B' → A ≠ B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  intro H5
  subst H5
  exact b10 (per2_col_eq_c b0 b3 b4 b1 b5 b6 b8 b9 ((by colr)))
theorem per23_preserves_bet_c :
    ∀ (A B C B' C' : Tpoint), Bet A B C → A ≠ B' → A ≠ C' → Col A B' C' → Per A B' B → Per A C' C → Bet A B' C' := sorry

theorem per23_preserves_bet_inv_c :
    ∀ (A B C B' C' : Tpoint), Bet A B' C' → A ≠ B' → Col A B C → Per A B' B → Per A C' C → Bet A B C := sorry

theorem per13_preserves_bet_c :
    ∀ (A B C A' C' : Tpoint), Bet A B C → B ≠ A' → B ≠ C' → Col A' B C' → Per B A' A → Per B C' C → Bet A' B C' := sorry

theorem per13_preserves_bet_inv_c :
    ∀ (A B C A' C' : Tpoint), Bet A' B C' → B ≠ A' → B ≠ C' → Col A B C → Per B A' A → Per B C' C → Bet A B C := sorry

theorem per3_preserves_bet1_c :
    ∀ (O A B C A' B' C' : Tpoint), Col O A B → Bet A B C → O ≠ A' → O ≠ B' → O ≠ C' → Per O A' A → Per O B' B → Per O C' C → Col A' B' C' → Col O A' B' → Bet A' B' C' := sorry

theorem per3_preserves_bet2_aux_c :
    ∀ (O A B C B' C' : Tpoint), Col O A C → A ≠ C' → Bet A B' C' → O ≠ A → O ≠ B' → O ≠ C' → Per O B' B → Per O C' C → Col A B C → Col O A C' → Bet A B C := sorry

theorem per3_preserves_bet2_c :
    ∀ (O A B C A' B' C' : Tpoint), Col O A C → A' ≠ C' → Bet A' B' C' → O ≠ A' → O ≠ B' → O ≠ C' → Per O A' A → Per O B' B → Per O C' C → Col A B C → Col O A' C' → Bet A B C := sorry

theorem symmetry_preserves_per_c :
    ∀ (A P B A' P' : Tpoint), Per B P A → Midpoint B A A' → Midpoint B P P' → Per B P' A' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have HS := symmetric_point_construction_c b0 b1
  obtain ⟨C, H2⟩ := HS
  have HS0 := symmetric_point_construction_c C b2
  obtain ⟨C', H3⟩ := HS0
  have HH := symmetry_preserves_midpoint_c b0 b1 C b3 b4 C' b2 b6 b7 H3 H2
  exact ⟨C', (⟨HH, ((by
  obtain ⟨X, H4⟩ := b5
  obtain ⟨H5, H6⟩ := H4
  have H7 := symmetric_point_uniqueness_c b0 b1 X C H5 H2
  rw [H7] at *
  obtain ⟨_, _⟩ := H5
  obtain ⟨_, _⟩ := HH
  obtain ⟨_, H10⟩ := H3
  obtain ⟨_, _⟩ := H2
  obtain ⟨_, _⟩ := b7
  obtain ⟨_, H11⟩ := b6
  exact (by cong_r)))⟩)⟩
theorem l13_1_aux_c :
    ∀ (A B C P Q R : Tpoint), ¬ Col A B C → Midpoint P B C → Midpoint Q A C → Midpoint R A B → ∃ (X : Tpoint), ∃ (Y : Tpoint), Perp_at R X Y A B ∧ Perp X Y P Q ∧ Coplanar A B C X ∧ Coplanar A B C Y := sorry

theorem l13_1_c :
    ∀ (A B C P Q R : Tpoint), ¬ Col A B C → Midpoint P B C → Midpoint Q A C → Midpoint R A B → ∃ (X : Tpoint), ∃ (Y : Tpoint), Perp_at R X Y A B ∧ Perp X Y P Q := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have e := l13_1_aux_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨H5, H6⟩ := x2
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact ⟨x, (⟨x1, (⟨H5, H7⟩)⟩)⟩
theorem per_lt_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → Per A B C → Lt A B A C ∧ Lt C B A C := by
  intro b0 b1 b2 b3 b4 b5
  have H2 := l11_46_c b0 b1 b2 b3 (Ne.symm b4) (Or.inl b5)
  obtain ⟨H3, H4⟩ := H2
  exact ⟨(lt_left_comm_c b1 b0 b0 b2 H3), (lt_left_comm_c b1 b2 b0 b2 H4)⟩
theorem cong_perp_conga_c :
    ∀ (A B C P : Tpoint), Cong A B C B → Perp A C B P → CongA A B P C B P ∧ TS B P A C := sorry

theorem perp_per_bet_c :
    ∀ (A B C P : Tpoint), ¬ Col A B C → Col A P C → Per A B C → Perp_at P P B A C → Bet A P C := sorry

theorem ts_per_per_ts_c :
    ∀ (A B C D : Tpoint), TS A B C D → Per B C A → Per B D A → TS C D A B := sorry

theorem l13_2_1_c :
    ∀ (A B C D E : Tpoint), TS A B C D → Per B C A → Per B D A → Col C D E → Perp A E C D → CongA C A B D A B → CongA B A C D A E ∧ CongA B A D C A E ∧ Bet C E D := sorry

theorem triangle_mid_par_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → Midpoint P B C → Midpoint Q A C → Par_strict A B Q P := sorry

theorem l13_2_c :
    ∀ (A B C D E : Tpoint), TS A B C D → Per B C A → Per B D A → Col C D E → Perp A E C D → CongA B A C D A E ∧ CongA B A D C A E ∧ Bet C E D := sorry

theorem perp2_refl_c :
    ∀ (A B P : Tpoint), A ≠ B → Perp2 A B A B P := by
  intro b0 b1 b2 b3
  have o := col_dec_c b0 b1 b2
  rcases o with H0 | H0
  · have HH := not_col_exists_c b0 b1 b3
    obtain ⟨X, H1⟩ := HH
    have HH0 := l10_15_c b0 b1 b2 X H0 H1
    obtain ⟨Q, H2⟩ := HH0
    obtain ⟨H3, _⟩ := H2
    exact ⟨Q, (⟨b2, (⟨(col_trivial_3_c b2 Q), (⟨(perp_comm_c b2 Q b1 b0 (perp_comm_c Q b2 b0 b1 (perp_sym_c b0 b1 Q b2 H3))), (perp_comm_c b2 Q b1 b0 (perp_comm_c Q b2 b0 b1 (perp_sym_c b0 b1 Q b2 H3)))⟩)⟩)⟩)⟩
  · have HH := l8_18_existence_c b0 b1 b2 H0
    obtain ⟨Q, H1⟩ := HH
    obtain ⟨_, H2⟩ := H1
    exact ⟨b2, (⟨Q, (⟨(col_trivial_1_c b2 Q), (⟨(perp_comm_c Q b2 b1 b0 (perp_comm_c b2 Q b0 b1 (perp_sym_c b0 b1 b2 Q H2))), (perp_comm_c Q b2 b1 b0 (perp_comm_c b2 Q b0 b1 (perp_sym_c b0 b1 b2 Q H2)))⟩)⟩)⟩)⟩
theorem perp2_sym_c :
    ∀ (A B C D P : Tpoint), Perp2 A B C D P → Perp2 C D A B P := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨X, H0⟩ := b5
  obtain ⟨Y, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨X, (⟨Y, (⟨H2, (⟨H5, H4⟩)⟩)⟩)⟩
theorem perp2_left_comm_c :
    ∀ (A B C D P : Tpoint), Perp2 A B C D P → Perp2 B A C D P := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨X, H0⟩ := b5
  obtain ⟨Y, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨X, (⟨Y, (⟨H2, (⟨(perp_comm_c Y X b0 b1 (perp_comm_c X Y b1 b0 (perp_comm_c Y X b0 b1 (perp_left_comm_c X Y b0 b1 H4)))), H5⟩)⟩)⟩)⟩
theorem perp2_right_comm_c :
    ∀ (A B C D P : Tpoint), Perp2 A B C D P → Perp2 A B D C P := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨X, H0⟩ := b5
  obtain ⟨Y, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨X, (⟨Y, (⟨H2, (⟨H4, (perp_comm_c Y X b2 b3 (perp_comm_c X Y b3 b2 (perp_comm_c Y X b2 b3 (perp_left_comm_c X Y b2 b3 H5))))⟩)⟩)⟩)⟩
theorem perp2_comm_c :
    ∀ (A B C D P : Tpoint), Perp2 A B C D P → Perp2 B A D C P := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨X, H0⟩ := b5
  obtain ⟨Y, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨X, (⟨Y, (⟨H2, (⟨(perp_comm_c Y X b0 b1 (perp_comm_c X Y b1 b0 (perp_comm_c Y X b0 b1 (perp_left_comm_c X Y b0 b1 H4)))), (perp_comm_c Y X b2 b3 (perp_comm_c X Y b3 b2 (perp_comm_c Y X b2 b3 (perp_left_comm_c X Y b2 b3 H5))))⟩)⟩)⟩)⟩
theorem perp2_pseudo_trans_c :
    ∀ (A B C D E F P : Tpoint), Perp2 A B C D P → Perp2 C D E F P → ¬ Col C D P → Perp2 A B E F P := sorry

theorem perp2_preserves_bet23_c :
    ∀ (O A B A' B' : Tpoint), Bet O A B → Col O A' B' → ¬ Col O A A' → Perp2 A A' B B' O → Bet O A' B' := sorry

theorem perp2_preserves_bet13_c :
    ∀ (O B C B' C' : Tpoint), Bet B O C → Col O B' C' → ¬ Col O B B' → Perp2 B C' C B' O → Bet B' O C' := sorry

theorem is_image_perp_in_c :
    ∀ (A A' X Y : Tpoint), A ≠ A' → X ≠ Y → Reflect A A' X Y → ∃ (P : Tpoint), Perp_at P A A' X Y := by
  intro b0 b1 b2 b3 b4 b5 b6
  rcases b6 with H2 | H2
  · obtain ⟨_, H3⟩ := H2
    obtain ⟨H4, H5⟩ := H3
    obtain ⟨P, H6⟩ := H4
    obtain ⟨H7, H8⟩ := H6
    rcases H5 with H9 | H9
    · exact ⟨P, (perp_in_sym_c b2 b3 b0 b1 P (perp_in_right_comm_c b2 b3 b1 b0 P (l8_14_2_1b_bis_c b2 b3 b1 b0 P H9 (col_permutation_5_c P b3 b2 (col_permutation_3_c b2 b3 P H8)) (midpoint_col_c b1 P b0 H7))))⟩
    · have H10 := midpoint_col_c b1 P b0 H7
      subst H9
      have H12 := (let H12 := rfl; b4 H12)
      exact (H12).elim
  · obtain ⟨H3, _⟩ := H2
    exact ((b5 H3)).elim
theorem perp_inter_perp_in_n_c :
    ∀ (A B C D : Tpoint), Perp A B C D → ∃ P : Tpoint, Col A B P ∧ Col C D P ∧ Perp_at P A B C D := sorry

theorem perp2_perp_in_c :
    ∀ (A B C D O : Tpoint), Perp2 A B C D O → ¬ Col O A B ∧ ¬ Col O C D → ∃ (P : Tpoint), ∃ (Q : Tpoint), Col A B P ∧ Col C D Q ∧ Col O P Q ∧ Perp_at P O P A B ∧ Perp_at Q O Q C D := sorry

theorem l13_8_c :
    ∀ (O P Q U V : Tpoint), U ≠ O → V ≠ O → Col O P Q → Col O U V → Per P U O → Per Q V O → (Out O P Q ↔ Out O U V) := sorry

theorem perp_in_rewrite_c :
    ∀ (A B C D P : Tpoint), Perp_at P A B C D → Perp_at P A P P C ∨ Perp_at P A P P D ∨ Perp_at P B P P C ∨ Perp_at P B P P D := sorry

theorem perp_out_acute_c :
    ∀ (A B C C' : Tpoint), Out B A C' → Perp A B C C' → Acute A B C := sorry

theorem perp_bet_obtuse_c :
    ∀ (A B C C' : Tpoint), B ≠ C' → Perp A B C C' → Bet A B C' → Obtuse A B C := sorry

theorem perp2_trans_c :
    ∀ (A B C D E F P : Tpoint), Perp2 A B C D P → Perp2 C D E F P → Perp2 A B E F P := sorry

theorem perp2_par_c :
    ∀ (A B C D O : Tpoint), Perp2 A B C D O → Par A B C D := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨X, H0⟩ := b5
  obtain ⟨Y, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact l12_9_2D_c b0 b1 b2 b3 X Y (perp_comm_c b1 b0 Y X (perp_comm_c b0 b1 X Y (perp_sym_c X Y b0 b1 H3))) (perp_comm_c b3 b2 Y X (perp_comm_c b2 b3 X Y (perp_sym_c X Y b2 b3 H4)))
#print axioms GeocoqTranslate.Tarski.Base.per2_col_eq_c
#print axioms GeocoqTranslate.Tarski.Base.per2_preserves_diff_c
#print axioms GeocoqTranslate.Tarski.Base.per23_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.per23_preserves_bet_inv_c
#print axioms GeocoqTranslate.Tarski.Base.per13_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.per13_preserves_bet_inv_c
#print axioms GeocoqTranslate.Tarski.Base.per3_preserves_bet1_c
#print axioms GeocoqTranslate.Tarski.Base.per3_preserves_bet2_aux_c
#print axioms GeocoqTranslate.Tarski.Base.per3_preserves_bet2_c
#print axioms GeocoqTranslate.Tarski.Base.symmetry_preserves_per_c
#print axioms GeocoqTranslate.Tarski.Base.l13_1_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l13_1_c
#print axioms GeocoqTranslate.Tarski.Base.per_lt_c
#print axioms GeocoqTranslate.Tarski.Base.cong_perp_conga_c
#print axioms GeocoqTranslate.Tarski.Base.perp_per_bet_c
#print axioms GeocoqTranslate.Tarski.Base.ts_per_per_ts_c
#print axioms GeocoqTranslate.Tarski.Base.l13_2_1_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_mid_par_c
#print axioms GeocoqTranslate.Tarski.Base.l13_2_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_refl_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_sym_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_pseudo_trans_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_preserves_bet23_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_preserves_bet13_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.perp_inter_perp_in_n_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.l13_8_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_rewrite_c
#print axioms GeocoqTranslate.Tarski.Base.perp_out_acute_c
#print axioms GeocoqTranslate.Tarski.Base.perp_bet_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_trans_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_par_c
end GeocoqTranslate.Tarski.Base