import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l5_2_ax (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet B C D ∨ Bet B D C := by
  have H2 := l5_1 hAB h₁ h₂
  rcases H2 with H3 | H3
  · exact Or.inl (between_symmetry (between_symmetry (between_exchange3 h₁ H3)))
  · exact Or.inr (between_symmetry (between_symmetry (between_exchange3 h₂ H3)))

theorem l5_3_ax (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet A C D) : Bet A B C ∨ Bet A C B := by
  have H1 := point_construction_different D A
  obtain ⟨P, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₁))
  have H6 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₂))
  exact l5_2 (Ne.symm H4) H5 H6

theorem le_bet_ax (A B C D : Tpoint) (h : Le C D A B) :
    ∃ X, Bet A X B ∧ Cong A X C D := by
  obtain ⟨Y, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  exact ⟨Y, (⟨H1, (cong_symmetry H2)⟩)⟩

theorem l5_5_1_ax (A B C D : Tpoint) (h : Le A B C D) :
    ∃ x, Bet A B x ∧ Cong A x C D := by
  obtain ⟨P, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  have sg := segment_construction A B P D
  obtain ⟨x, H3⟩ := sg
  obtain ⟨H4, H5⟩ := H3
  exact ⟨x, (⟨H4, (l2_11 H4 H1 H2 H5)⟩)⟩

theorem le_reflexivity_ax (A B : Tpoint) : Le A B A B :=
  ⟨B, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))), (cong_reflexivity A B)⟩)⟩

theorem between_cong_ax (A B C : Tpoint) (hBet : Bet A C B) (hCong : Cong A C A B) :
    C = B :=
  (let H1 := l4_6 (hBet) (⟨hCong, (⟨(cong_symmetry hCong), (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C B))))⟩)⟩); between_equality (between_symmetry H1) (between_symmetry hBet))

theorem cong3_symmetry_ax (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem le_trivial_ax (A C D : Tpoint) : Le A A C D :=
  ⟨C, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 C D))))), (cong_trivial_identity A C)⟩)⟩

theorem cong_le_ax (A B C D : Tpoint) (h : Cong A B C D) : Le A B C D :=
  ⟨D, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial C D))))), h⟩)⟩

theorem third_point_ax (A B P : Tpoint) (h : Col A B P) :
    Bet P A B ∨ Bet A P B ∨ Bet A B P := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inl (between_symmetry H1))
    · exact Or.inl H1

#print axioms GeocoqTranslate.Tarski.Base.l5_2_ax
#print axioms GeocoqTranslate.Tarski.Base.l5_3_ax
#print axioms GeocoqTranslate.Tarski.Base.le_bet_ax
#print axioms GeocoqTranslate.Tarski.Base.l5_5_1_ax
#print axioms GeocoqTranslate.Tarski.Base.le_reflexivity_ax
#print axioms GeocoqTranslate.Tarski.Base.between_cong_ax
#print axioms GeocoqTranslate.Tarski.Base.cong3_symmetry_ax
#print axioms GeocoqTranslate.Tarski.Base.le_trivial_ax
#print axioms GeocoqTranslate.Tarski.Base.cong__le_ax
#print axioms GeocoqTranslate.Tarski.Base.third_point_ax

end GeocoqTranslate.Tarski.Base
