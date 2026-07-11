import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

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
         Col B C A ∨ Col C A B ∨ Col C B A) : Col A B C := sorry

theorem Col_perm_c (A B C : Tpoint) (h : Col A B C) :
    Col A B C ∧ Col A C B ∧ Col B A C ∧
    Col B C A ∧ Col C A B ∧ Col C B A := sorry

theorem col_trivial_1_c (A B : Tpoint) : Col A A B :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_trivial B A))))

theorem col_trivial_2_c (A B : Tpoint) : Col A B B :=
  Or.inr (Or.inl (between_symmetry (between_symmetry (between_trivial2 B A))))

theorem col_trivial_3_c (A B : Tpoint) : Col A B A :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial B A)))))

theorem l4_13_c (A B C A' B' C' : Tpoint)
    (h₁ : Col A B C)
    (h₂ : Cong_3 A B C A' B' C') :
    Col A' B' C' := sorry

theorem l4_14_c (A B C A' B' : Tpoint)
    (h₁ : Col A B C) (h₂ : Cong A B A' B') :
    ∃ C', Cong_3 A B C A' B' C' := sorry

theorem l4_16_c (A B C D A' B' C' D' : Tpoint)
    (h₁ : FSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := sorry

theorem l4_17_c (A B C P Q : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A P A Q) (h₂ : Cong B P B Q) : Cong C P C Q := sorry

theorem l4_18_c (A B C C' : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' :=
  cong_identity C C' C (l4_17 hAB hCol (cong_symmetry h₁) (cong_symmetry h₂))

theorem l4_19_c (A B C C' : Tpoint)
    (hBet : Bet A C B)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' := sorry

theorem not_col_distincts_c (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A B C ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C := by
  exact ⟨h, (⟨((fun H0 => eq_ind_r (fun A0 => ~ Col A0 B C - > False) (fun H1 => H1 (col_trivial_1_c B C)) H0 h)), (⟨((fun H0 => eq_ind_r (fun B0 => ~ Col A B0 C - > False) (fun H1 => H1 (col_trivial_2_c A C)) H0 h)), ((fun H0 => eq_ind_r (fun A0 => ~ Col A0 B C - > False) (fun H1 => H1 (col_trivial_3_c C B)) H0 h))⟩)⟩)⟩

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
    (h₁ : Cong_3 A B C A' B' C₁) (h₂ : Cong_3 A B C A' B' C₂) : C₁ = C₂ := sorry

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
#print axioms GeocoqTranslate.Tarski.Base.l4_16_c
#print axioms GeocoqTranslate.Tarski.Base.l4_17_c
#print axioms GeocoqTranslate.Tarski.Base.l4_18_c
#print axioms GeocoqTranslate.Tarski.Base.l4_19_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.NCol_cases_c
#print axioms GeocoqTranslate.Tarski.Base.NCol_perm_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong_3_cong_3_eq_c
end GeocoqTranslate.Tarski.Base