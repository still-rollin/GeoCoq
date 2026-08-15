import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem bet_col_ax (A B C : Tpoint) (h : Bet A B C) : Col A B C :=
  Or.inl h

theorem between_symmetry_ax (A B C : Tpoint) (h : Bet A B C) : Bet C B A := by
  have H0 := between_trivial B C
  have H1 := inner_pasch A B C B C h H0
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity B x H3
  subst H5
  exact H4

theorem Bet_cases_ax (A B C : Tpoint) (h : Bet A B C ∨ Bet C B A) : Bet A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · exact between_symmetry H1

theorem Bet_perm_ax (A B C : Tpoint) (h : Bet A B C) : Bet A B C ∧ Bet C B A :=
  ⟨h, (between_symmetry h)⟩

theorem between_trivial2_ax (A B : Tpoint) : Bet A A B :=
  between_symmetry (between_trivial B A)

theorem between_equality_2_ax (A B C : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C B) : B = C :=
  between_equality (between_symmetry h₂) (between_symmetry h₁)

theorem between_exchange3_ax (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet B C D := by
  have H1 := inner_pasch D C A C B (between_symmetry h₂) (between_symmetry h₁)
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity C x H3
  subst H5
  exact H4

theorem bet_neq21_neq_ax (A B C : Tpoint) (h : Bet A B C) (hBA : B ≠ A) : A ≠ C :=
  bet_neq12_neq h (Ne.symm hBA)

theorem bet_neq32_neq_ax (A B C : Tpoint) (h : Bet A B C) (hCB : C ≠ B) : A ≠ C :=
  bet_neq23_neq h (Ne.symm hCB)

theorem outer_transitivity_between2_ax (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A C D := by
  have sg := segment_construction A C C D
  obtain ⟨x, H2⟩ := sg
  obtain ⟨H3, H4⟩ := H2
  have H5 := construction_uniqueness hBC (between_exchange3 h₁ H3) H4 h₂ (cong_reflexivity C D)
  subst H5
  exact H3

theorem between_exchange2_ax (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A C D := by
  have o := point_equality_decidability B C
  rcases o with H1 | H1
  · subst H1
    exact h₁
  · exact between_symmetry (between_symmetry (outer_transitivity_between2 (between_inner_transitivity h₁ h₂) h₂ H1))

theorem outer_transitivity_between_ax (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A B D :=
  between_symmetry (outer_transitivity_between2 (between_symmetry h₂) (between_symmetry h₁) (Ne.symm hBC))

theorem between_exchange4_ax (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet A B D :=
  between_symmetry (between_exchange2 (between_symmetry h₂) (between_symmetry h₁))

theorem l3_9_4_ax (A₁ A₂ A₃ A₄ : Tpoint) (h : Bet_4 A₁ A₂ A₃ A₄) :
    Bet_4 A₄ A₃ A₂ A₁ := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨(between_symmetry H2), (⟨(between_symmetry H0), (⟨(between_symmetry H5), (between_symmetry H4)⟩)⟩)⟩

theorem l3_17_ax (A B C A' B' P : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C) (h₃ : Bet A P A') :
    ∃ Q, Bet P Q C ∧ Bet B Q B' := by
  have H2 := inner_pasch C A A' B' P (between_symmetry h₂) h₃
  obtain ⟨x, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  have H6 := inner_pasch B' C A x B H4 (between_symmetry h₁)
  obtain ⟨y, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  exact ⟨y, (⟨(between_symmetry (between_symmetry (between_exchange2 H5 H8))), H9⟩)⟩

theorem another_point_ax (A : Tpoint) : ∃ B, A ≠ B := by
  have pcd := point_construction_different A A
  obtain ⟨B, H⟩ := pcd
  obtain ⟨_, H0⟩ := H
  exact ⟨B, H0⟩

#print axioms GeocoqTranslate.Tarski.Base.bet_col_ax
#print axioms GeocoqTranslate.Tarski.Base.between_symmetry_ax
#print axioms GeocoqTranslate.Tarski.Base.Bet_cases_ax
#print axioms GeocoqTranslate.Tarski.Base.Bet_perm_ax
#print axioms GeocoqTranslate.Tarski.Base.between_trivial2_ax
#print axioms GeocoqTranslate.Tarski.Base.between_equality_2_ax
#print axioms GeocoqTranslate.Tarski.Base.between_exchange3_ax
#print axioms GeocoqTranslate.Tarski.Base.bet_neq21_neq_ax
#print axioms GeocoqTranslate.Tarski.Base.bet_neq32_neq_ax
#print axioms GeocoqTranslate.Tarski.Base.outer_transitivity_between2_ax
#print axioms GeocoqTranslate.Tarski.Base.between_exchange2_ax
#print axioms GeocoqTranslate.Tarski.Base.outer_transitivity_between_ax
#print axioms GeocoqTranslate.Tarski.Base.between_exchange4_ax
#print axioms GeocoqTranslate.Tarski.Base.l3_9_4_ax
#print axioms GeocoqTranslate.Tarski.Base.l3_17_ax
#print axioms GeocoqTranslate.Tarski.Base.another_point_ax

end GeocoqTranslate.Tarski.Base
