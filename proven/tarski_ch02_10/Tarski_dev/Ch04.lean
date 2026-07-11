import GeocoqTranslate.Tarski_dev.Ch03

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem col_permutation_1_c (A B C : Tpoint) (h : Col A B C) : Col B C A := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr H0)
  · rcases H0 with H1 | H1
    · exact Or.inl H1
    · exact Or.inr (Or.inl H1)

theorem col_permutation_2_c (A B C : Tpoint) (h : Col A B C) : Col C A B := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inl H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inr H1)
    · exact Or.inl H1

theorem col_permutation_3_c (A B C : Tpoint) (h : Col A B C) : Col C B A := by
  rcases h with H0 | H0
  · exact Or.inl (between_symmetry H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inr (between_symmetry H1))
    · exact Or.inr (Or.inl (between_symmetry H1))

theorem col_permutation_4_c (A B C : Tpoint) (h : Col A B C) : Col B A C := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr (between_symmetry H0))
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inl (between_symmetry H1))
    · exact Or.inl (between_symmetry H1)

theorem col_permutation_5_c (A B C : Tpoint) (h : Col A B C) : Col A C B := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inl (between_symmetry H0))
  · rcases H0 with H1 | H1
    · exact Or.inl (between_symmetry H1)
    · exact Or.inr (Or.inr (between_symmetry H1))

theorem not_col_permutation_1_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col B C A :=
  (fun H0 => h (col_permutation_5_c A C B (col_permutation_3_c B C A H0)))

theorem not_col_permutation_2_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col C A B :=
  (fun H0 => h (col_permutation_5_c A C B (col_permutation_4_c C A B H0)))

theorem not_col_permutation_3_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col C B A :=
  (fun H0 => h (col_permutation_5_c A C B (col_permutation_2_c C B A H0)))

theorem not_col_permutation_4_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col B A C :=
  (fun H0 => h (col_permutation_5_c A C B (col_permutation_1_c B A C H0)))

theorem not_col_permutation_5_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A C B :=
  (fun H0 => h (col_permutation_5_c A C B H0))

theorem Col_cases_c (A B C : Tpoint)
    (h : Col A B C ∨ Col A C B ∨ Col B A C ∨
         Col B C A ∨ Col C A B ∨ Col C B A) : Col A B C := by
  rcases h with h | h | h | h | h | h
  · exact h
  · exact col_permutation_5_c A C B h
  · exact col_permutation_4_c B A C h
  · exact col_permutation_2_c B C A h
  · exact col_permutation_1_c C A B h
  · exact col_permutation_3_c C B A h

theorem Col_perm_c (A B C : Tpoint) (h : Col A B C) :
    Col A B C ∧ Col A C B ∧ Col B A C ∧
    Col B C A ∧ Col C A B ∧ Col C B A :=
  ⟨h, col_permutation_5_c A B C h, col_permutation_4_c A B C h,
   col_permutation_1_c A B C h, col_permutation_2_c A B C h, col_permutation_3_c A B C h⟩

theorem col_trivial_1_c (A B : Tpoint) : Col A A B :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_trivial B A))))

theorem col_trivial_2_c (A B : Tpoint) : Col A B B :=
  Or.inr (Or.inl (between_symmetry (between_symmetry (between_trivial2 B A))))

theorem col_trivial_3_c (A B : Tpoint) : Col A B A :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial B A)))))

theorem l4_13_c (A B C A' B' C' : Tpoint)
    (h₁ : Col A B C)
    (h₂ : Cong_3 A B C A' B' C') :
    Col A' B' C' := by
  have H1 := h₁
  rcases H1 with H2 | H2
  · exact Or.inl (l4_6 H2 h₂)
  · rcases H2 with H3 | H3
    · exact Or.inr (Or.inl (l4_6 H3 (cong_3_swap_2_c B A C B' A' C' (cong_3_swap_c A B C A' B' C' h₂))))
    · exact Or.inr (Or.inr (l4_6 H3 (cong_3_swap_c A C B A' C' B' (cong_3_swap_2_c A B C A' B' C' h₂))))

theorem l4_14_c (A B C A' B' : Tpoint)
    (h₁ : Col A B C) (h₂ : Cong A B A' B') :
    ∃ C', Cong_3 A B C A' B' C' := by
  rcases h₁ with H1 | H1
  · have sg := segment_construction A' B' B C
    obtain ⟨C', H2⟩ := sg
    obtain ⟨H3, H4⟩ := H2
    exact ⟨C', ((let H5 := l2_11 H1 H3 h₂ (cong_symmetry H4); ⟨h₂, (⟨H5, (cong_symmetry H4)⟩)⟩))⟩
  · rcases H1 with H2 | H2
    · have H3 := l4_5 (between_symmetry H2) h₂
      obtain ⟨C', H4⟩ := H3
      obtain ⟨_, H5⟩ := H4
      exact ⟨C', (cong_3_swap_2_c A C B A' C' B' H5)⟩
    · have sg := segment_construction B' A' A C
      obtain ⟨C', H3⟩ := sg
      obtain ⟨H4, H5⟩ := H3
      exact ⟨C', ((let H6 := l2_11 (between_symmetry H2) H4 (cong_symmetry (cong_symmetry (cong_commutativity h₂))) (cong_symmetry H5); ⟨h₂, (⟨(cong_symmetry H5), H6⟩)⟩))⟩

theorem l4_18_c (A B C C' : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' :=
  cong_identity C C' C (l4_17 hAB hCol (cong_symmetry h₁) (cong_symmetry h₂))

theorem l4_19_c (A B C C' : Tpoint)
    (hBet : Bet A C B)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' := by
  have o := point_equality_decidability A B
  rcases o with H2 | H2
  · subst H2
    have H4 := between_identity A C hBet
    subst H4
    have H6 := cong_symmetry h₁
    have H7 := cong_identity A C' A H6
    subst H7
    exact rfl
  · exact l4_18_c A B C C' H2 (col_permutation_5_c A C B (bet_col_c A C B hBet)) h₁ h₂

theorem not_col_distincts_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A B C ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  refine ⟨h, ?_, ?_, ?_⟩
  · rintro rfl; exact h (Or.inl (between_trivial2_c _ _))
  · rintro rfl; exact h (Or.inl (between_trivial_c _ _))
  · rintro rfl; exact h (Or.inr (Or.inr (between_trivial2_c _ _)))

theorem NCol_cases_c (A B C : Tpoint)
    (h : ¬ Col A B C ∨ ¬ Col A C B ∨ ¬ Col B A C ∨
         ¬ Col B C A ∨ ¬ Col C A B ∨ ¬ Col C B A) : ¬ Col A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact not_col_permutation_5_c A C B H2
    · rcases H2 with H3 | H3
      · exact not_col_permutation_5_c A C B (not_col_permutation_1_c B A C H3)
      · rcases H3 with H4 | H4
        · exact not_col_permutation_5_c A C B (not_col_permutation_3_c B C A H4)
        · rcases H4 with H5 | H5
          · exact not_col_permutation_5_c A C B (not_col_permutation_4_c C A B H5)
          · exact not_col_permutation_5_c A C B (not_col_permutation_2_c C B A H5)

theorem NCol_perm_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A B C ∧ ¬ Col A C B ∧ ¬ Col B A C ∧
    ¬ Col B C A ∧ ¬ Col C A B ∧ ¬ Col C B A :=
  ⟨h, (⟨(not_col_permutation_5_c A B C h), (⟨(not_col_permutation_5_c B C A (not_col_permutation_1_c A B C h)), (⟨(not_col_permutation_5_c B A C (not_col_permutation_4_c A B C h)), (⟨(not_col_permutation_5_c C B A (not_col_permutation_3_c A B C h)), (not_col_permutation_5_c C A B (not_col_permutation_2_c A B C h))⟩)⟩)⟩)⟩)⟩

theorem col_cong_3_cong_3_eq_c (A B C A' B' C₁ C₂ : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong_3 A B C A' B' C₁) (h₂ : Cong_3 A B C A' B' C₂) : C₁ = C₂ := by
  obtain ⟨hAB', hAC1, hBC1⟩ := h₁
  obtain ⟨_, hAC2, hBC2⟩ := h₂
  have hA'B' : A' ≠ B' := cong_diff_c A B A' B' hAB hAB'
  have hCol' : Col A' B' C₁ := l4_13_c A B C A' B' C₁ hCol ⟨hAB', hAC1, hBC1⟩
  exact l4_18_c A' B' C₁ C₂ hA'B' hCol'
    (cong_transitivity_c A' C₁ A C A' C₂ (cong_symmetry hAC1) hAC2)
    (cong_transitivity_c B' C₁ B C B' C₂ (cong_symmetry hBC1) hBC2)

theorem l4_2_c (A B C D A' B' C' D' : Tpoint)
    (h : IFSC A B C D A' B' C' D') : Cong B D B' D' := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  have o := point_equality_decidability A C
  rcases o with H10 | H10
  · subst H10
    have H15 := cong_symmetry H4
    have H16 := cong_identity A' C' A H15
    subst H16
    have H19 := between_identity A' B' H2
    subst H19
    have H21 := cong_identity B A A' H6
    subst H21
    exact H8
  · have H11 := point_construction_different A C
    obtain ⟨E, H12⟩ := H11
    obtain ⟨H13, H14⟩ := H12
    have sg := segment_construction A' C' C E
    obtain ⟨E', H15⟩ := sg
    obtain ⟨H16, H17⟩ := H15
    have H18 := five_segment_with_def (⟨H13, (⟨H16, (⟨H4, (⟨(cong_symmetry H17), (⟨H8, H9⟩)⟩)⟩)⟩)⟩) H10
    exact five_segment_with_def (⟨(between_symmetry (between_symmetry (between_symmetry (between_exchange3 H0 H13)))), (⟨(between_symmetry (between_symmetry (between_symmetry (between_exchange3 H2 H16)))), (⟨(cong_symmetry (cong_symmetry (cong_4321_c C' E' C E H17))), (⟨(cong_symmetry (cong_symmetry (cong_commutativity H6))), (⟨H18, H9⟩)⟩)⟩)⟩)⟩) (Ne.symm H14)

theorem l4_3_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A C A' C') (h₄ : Cong B C B' C') : Cong A B A' B' :=
  cong_commutativity (l4_2 (⟨h₁, (⟨h₂, (⟨h₃, (⟨h₄, (⟨(cong_trivial_identity A A'), (cong_symmetry (cong_symmetry (cong_commutativity h₃)))⟩)⟩)⟩)⟩)⟩))

theorem l4_3_1_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A B A' B') (h₄ : Cong A C A' C') : Cong B C B' C' :=
  cong_commutativity (l4_3 (between_symmetry h₁) (between_symmetry h₂) (cong_symmetry (cong_symmetry (cong_commutativity h₄))) (cong_symmetry (cong_symmetry (cong_commutativity h₃))))

theorem l4_5_c (A B C A' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong A C A' C') :
    ∃ B', Bet A' B' C' ∧ Cong_3 A B C A' B' C' := by
  have H1 := point_construction_different C' A'
  obtain ⟨x', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have sg := segment_construction x' A' A B
  obtain ⟨B', H5⟩ := sg
  obtain ⟨H6, H7⟩ := H5
  have sg0 := segment_construction x' B' B C
  obtain ⟨C'', H8⟩ := sg0
  obtain ⟨H9, H10⟩ := H8
  have H11 := between_symmetry (between_symmetry (between_exchange3 H6 H9))
  have H12 := construction_uniqueness (Ne.symm H4) (between_symmetry (between_symmetry (between_exchange4 H6 H9))) (l2_11 H11 hBet H7 H10) (between_symmetry H3) (cong_symmetry hCong)
  subst H12
  exact ⟨B', (⟨H11, (⟨(cong_symmetry H7), (⟨hCong, (cong_symmetry H10)⟩)⟩)⟩)⟩

theorem l4_6_c (A B C A' B' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A' B' C') : Bet A' B' C' := by
  obtain ⟨hAB, hAC, hBC⟩ := hCong
  obtain ⟨x, hBetx, hCong3x⟩ := l4_5_c A B C A' C' hBet hAC
  obtain ⟨hABx, hACx, hBCx⟩ := hCong3x
  have hCong3' : Cong_3 A' x C' A' B' C' := by
    refine ⟨?_, ?_, ?_⟩
    · exact cong_transitivity_c A' x A B A' B' (cong_symmetry_c A B A' x hABx) hAB
    · exact cong_reflexivity_c A' C'
    · exact cong_transitivity_c x C' B C B' C' (cong_symmetry_c B C x C' hBCx) hBC
  obtain ⟨hAxB', hAC', hxC'B'C'⟩ := hCong3'
  have hIFSC : IFSC A' x C' x A' x C' B' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hBetx
    · exact hBetx
    · exact hAC'
    · exact cong_reflexivity_c x C'
    · exact hAxB'
    · exact cong_symmetry_c C' B' C' x (cong_symmetry_c C' x C' B' (cong_commutativity_c x C' B' C' hxC'B'C'))
  have hCongxx : Cong x x x B' := l4_2_c A' x C' x A' x C' B' hIFSC
  have hxB' : x = B' := cong_identity x B' x (cong_symmetry_c x x x B' hCongxx)
  rw [← hxB']
  exact hBetx

theorem l4_16_c (A B C D A' B' C' D' : Tpoint)
    (h₁ : FSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨hCol, hC3, hAD, hBD⟩ := h₁
  obtain ⟨h1, h2, h3⟩ := hC3
  rcases hCol with hb | hb | hb
  · have hb' : Bet A' B' C' := l4_6_c A B C A' B' C' hb ⟨h1, h2, h3⟩
    exact five_segment_with_def_c A B C D A' B' C' D' ⟨hb, hb', h1, h3, hAD, hBD⟩ hAB
  · have hb' : Bet B' C' A' := l4_6_c B C A B' C' A' hb
      ⟨h3, cong_commutativity h1, cong_commutativity h2⟩
    exact l4_2_c B C A D B' C' A' D'
      ⟨hb, hb', cong_commutativity h1, cong_commutativity h2, hBD, hAD⟩
  · have hb' : Bet C' A' B' := l4_6_c C A B C' A' B' hb
      ⟨cong_commutativity h2, cong_commutativity h3, h1⟩
    exact five_segment_with_def_c B A C D B' A' C' D'
      ⟨between_symmetry hb, between_symmetry hb', cong_commutativity h1, h2, hBD, hAD⟩
      (Ne.symm hAB)

theorem l4_17_c (A B C P Q : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A P A Q) (h₂ : Cong B P B Q) : Cong C P C Q :=
  l4_16_c A B C P A B C Q
    ⟨hCol, ⟨cong_reflexivity A B, cong_reflexivity A C, cong_reflexivity B C⟩, h₁, h₂⟩ hAB

theorem cong3_bet_eq_c (A B C X : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A X C) : X = B := by
  obtain ⟨H1, H3, H4⟩ := hCong
  have H5 : IFSC A B C B A B C X := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hBet
    · exact hBet
    · exact H3
    · exact cong_reflexivity_c B C
    · exact H1
    · exact cong_symmetry_c C X C B (cong_symmetry_c C B C X (cong_symmetry_c C X C B (cong_4321_c B C X C H4)))
  have H6 : Cong B B B X := l4_2_c A B C B A B C X H5
  have H7 : Cong B X B B := cong_symmetry_c B B B X H6
  have H8 : B = X := cong_identity B X B H7
  exact H8.symm

#print axioms GeocoqTranslate.Tarski.Base.col_permutation_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_2_c
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_3_c
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_4_c
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_5_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_permutation_1_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_permutation_2_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_permutation_3_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_permutation_4_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_permutation_5_c
#print axioms GeocoqTranslate.Tarski.Base.Col_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Col_perm_c
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_2_c
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_3_c
#print axioms GeocoqTranslate.Tarski.Base.l4_13_c
#print axioms GeocoqTranslate.Tarski.Base.l4_14_c
#print axioms GeocoqTranslate.Tarski.Base.l4_18_c
#print axioms GeocoqTranslate.Tarski.Base.l4_19_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.NCol_cases_c
#print axioms GeocoqTranslate.Tarski.Base.NCol_perm_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong_3_cong_3_eq_c
#print axioms GeocoqTranslate.Tarski.Base.l4_2_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_1_c
#print axioms GeocoqTranslate.Tarski.Base.l4_5_c
#print axioms GeocoqTranslate.Tarski.Base.l4_6_c
#print axioms GeocoqTranslate.Tarski.Base.l4_16_c
#print axioms GeocoqTranslate.Tarski.Base.l4_17_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_bet_eq_c

end GeocoqTranslate.Tarski.Base
