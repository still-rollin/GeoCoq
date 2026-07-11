import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem bet_out_1_ax (A B C : Tpoint) (hBA : B ≠ A) (h : Bet C B A) : Out A B C :=
  bet_out hBA (between_symmetry h)

theorem out_diff1_ax (A B C : Tpoint) (h : Out A B C) : B ≠ A := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  exact H0

theorem out_diff2_ax (A B C : Tpoint) (h : Out A B C) : C ≠ A := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨H1, _⟩ := H0
  exact H1

theorem out_distinct_ax (A B C : Tpoint) (h : Out A B C) : B ≠ A ∧ C ≠ A :=
  ⟨(out_diff1 h), (out_diff2 h)⟩

theorem out_col_ax (A B C : Tpoint) (h : Out A B C) : Col A B C := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨_, H1⟩ := H0
  rcases H1 with H2 | H2
  · exact Or.inl H2
  · exact Or.inr (Or.inl (between_symmetry H2))

theorem l6_3_2_ax (A B P : Tpoint)
    (h : A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C) :
    Out P A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨C, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  exact ⟨H0, (⟨H2, (l5_2 H5 (between_symmetry H7) (between_symmetry H8))⟩)⟩

theorem out_trivial_ax (P A : Tpoint) (hAP : A ≠ P) : Out P A A :=
  ⟨hAP, (⟨hAP, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 A P)))))⟩)⟩

theorem bet_out_out_bet_ax (A B C A' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Out B A A') (h₃ : Out B C C') : Bet A' B C' := by
  obtain ⟨H2, H3⟩ := h₃
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := h₂
  obtain ⟨_, H7⟩ := H6
  rcases H7 with H8 | H8
  · rcases H4 with H9 | H9
    · have H10 := outer_transitivity_between2 (between_symmetry H8) h₁ H5
      exact outer_transitivity_between H10 H9 (Ne.symm H2)
    · have H10 := outer_transitivity_between2 (between_symmetry H8) h₁ H5
      exact between_inner_transitivity H10 H9
  · rcases H4 with H9 | H9
    · have H10 := between_exchange3 (between_symmetry H8) h₁
      exact outer_transitivity_between H10 H9 (Ne.symm H2)
    · have H10 := between_exchange3 (between_symmetry H8) h₁
      exact between_inner_transitivity H10 H9

theorem out2_bet_out_ax (A B C X P : Tpoint)
    (h₁ : Out B A C) (h₂ : Out B X P) (h₃ : Bet A X C) :
    Out B A P ∧ Out B C P := by
  obtain ⟨H2, H3⟩ := h₂
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := h₁
  obtain ⟨H8, H9⟩ := H7
  rcases H9 with H10 | H10
  · rcases H5 with H11 | H11
    · exact ⟨(⟨H6, (⟨H4, (Or.inl (between_exchange4 (between_inner_transitivity H10 h₃) H11))⟩)⟩), (⟨H8, (⟨H4, (l5_1 (Ne.symm H2) (between_exchange2 H10 h₃) H11)⟩)⟩)⟩
    · exact ⟨(⟨H6, (⟨H4, (l5_3 (between_inner_transitivity H10 h₃) H11)⟩)⟩), (⟨H8, (⟨H4, (Or.inr (between_exchange4 H11 (between_exchange2 H10 h₃)))⟩)⟩)⟩
  · rcases H5 with H11 | H11
    · exact ⟨(⟨H6, (⟨H4, (l5_1 (Ne.symm H2) (between_exchange2 H10 (between_symmetry h₃)) H11)⟩)⟩), (⟨H8, (⟨H4, (Or.inl (between_exchange4 (between_inner_transitivity H10 (between_symmetry h₃)) H11))⟩)⟩)⟩
    · exact ⟨(⟨H6, (⟨H4, (Or.inr (between_exchange4 H11 (between_exchange2 H10 (between_symmetry h₃))))⟩)⟩), (⟨H8, (⟨H4, (l5_3 (between_inner_transitivity H10 (between_symmetry h₃)) H11)⟩)⟩)⟩

theorem l6_13_2_ax (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Bet P A B) :
    Le P A P B :=
  ⟨A, (⟨h₂, (cong_reflexivity P A)⟩)⟩

theorem Out_cases_ax (A B C : Tpoint) (h : Out A B C ∨ Out A C B) : Out A B C := by
  rcases h with H0 | H0
  · exact H0
  · exact l6_6 H0

#print axioms GeocoqTranslate.Tarski.Base.bet_out_1_ax
#print axioms GeocoqTranslate.Tarski.Base.out_diff1_ax
#print axioms GeocoqTranslate.Tarski.Base.out_diff2_ax
#print axioms GeocoqTranslate.Tarski.Base.out_distinct_ax
#print axioms GeocoqTranslate.Tarski.Base.out_col_ax
#print axioms GeocoqTranslate.Tarski.Base.l6_3_2_ax
#print axioms GeocoqTranslate.Tarski.Base.out_trivial_ax
#print axioms GeocoqTranslate.Tarski.Base.bet_out_out_bet_ax
#print axioms GeocoqTranslate.Tarski.Base.out2_bet_out_ax
#print axioms GeocoqTranslate.Tarski.Base.l6_13_2_ax
#print axioms GeocoqTranslate.Tarski.Base.Out_cases_ax

end GeocoqTranslate.Tarski.Base