import GeocoqTranslate.Tarski_dev.Ch02

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem bet_col_c (A B C : Tpoint) (h : Bet A B C) : Col A B C :=
  Or.inl h

theorem between_trivial_c (A B : Tpoint) : Bet A B B := by
  have sg := segment_construction A B B B
  obtain ⟨x, H⟩ := sg
  obtain ⟨H0, H1⟩ := H
  have H2 := cong_reverse_identity (cong_symmetry (cong_symmetry (cong_4321_c B x B B H1)))
  subst H2
  exact H0

theorem between_symmetry_c (A B C : Tpoint) (h : Bet A B C) : Bet C B A := by
  have H0 := between_trivial B C
  have H1 := inner_pasch A B C B C h H0
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity B x H3
  subst H5
  exact H4

theorem Bet_cases_c (A B C : Tpoint) (h : Bet A B C ∨ Bet C B A) : Bet A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · exact between_symmetry H1

theorem Bet_perm_c (A B C : Tpoint) (h : Bet A B C) : Bet A B C ∧ Bet C B A :=
  ⟨h, (between_symmetry h)⟩

theorem between_trivial2_c (A B : Tpoint) : Bet A A B :=
  between_symmetry (between_trivial B A)

theorem between_equality_c (A B C : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B A C) : A = B := by
  have H1 := inner_pasch A B C B A h₁ h₂
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity B x H3
  have H6 := between_identity A x H4
  exact Eq.trans H6 (Eq.symm H5)

theorem between_equality_2_c (A B C : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C B) : B = C :=
  between_equality (between_symmetry h₂) (between_symmetry h₁)

theorem between_exchange3_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet B C D := by
  have H1 := inner_pasch D C A C B (between_symmetry h₂) (between_symmetry h₁)
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity C x H3
  subst H5
  exact H4

theorem bet_neq12_neq_c (A B C : Tpoint) (h : Bet A B C) (hAB : A ≠ B) : A ≠ C := by
  intro Heq
  subst Heq
  exact hAB (between_identity A B h)

theorem bet_neq21_neq_c (A B C : Tpoint) (h : Bet A B C) (hBA : B ≠ A) : A ≠ C :=
  bet_neq12_neq h (Ne.symm hBA)

theorem bet_neq23_neq_c (A B C : Tpoint) (h : Bet A B C) (hBC : B ≠ C) : A ≠ C := by
  intro Heq
  subst Heq
  exact hBC (Eq.symm (between_identity A B h))

theorem bet_neq32_neq_c (A B C : Tpoint) (h : Bet A B C) (hCB : C ≠ B) : A ≠ C :=
  bet_neq23_neq h (Ne.symm hCB)

theorem not_bet_distincts_c (A B C : Tpoint) (h : ¬ Bet A B C) :
    A ≠ B ∧ B ≠ C := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h (between_trivial2_c _ _)
  · rintro rfl; exact h (between_trivial_c _ _)

theorem between_inner_transitivity_c (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A B C := by
  have H1 := inner_pasch A B D B C h₁ h₂
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_identity B x H3
  subst H5
  exact between_symmetry H4

theorem outer_transitivity_between2_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A C D := by
  have sg := segment_construction A C C D
  obtain ⟨x, H2⟩ := sg
  obtain ⟨H3, H4⟩ := H2
  have H5 := construction_uniqueness hBC (between_exchange3 h₁ H3) H4 h₂ (cong_reflexivity C D)
  subst H5
  exact H3

theorem between_exchange2_c (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A C D := by
  have o := point_equality_decidability B C
  rcases o with H1 | H1
  · subst H1
    exact h₁
  · exact between_symmetry (between_symmetry (outer_transitivity_between2 (between_inner_transitivity h₁ h₂) h₂ H1))

theorem outer_transitivity_between_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A B D :=
  between_symmetry (outer_transitivity_between2 (between_symmetry h₂) (between_symmetry h₁) (Ne.symm hBC))

theorem between_exchange4_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet A B D :=
  between_symmetry (between_exchange2 (between_symmetry h₂) (between_symmetry h₁))

theorem l3_9_4_c (A₁ A₂ A₃ A₄ : Tpoint) (h : Bet_4 A₁ A₂ A₃ A₄) :
    Bet_4 A₄ A₃ A₂ A₁ := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨(between_symmetry H2), (⟨(between_symmetry H0), (⟨(between_symmetry H5), (between_symmetry H4)⟩)⟩)⟩

theorem l3_17_c (A B C A' B' P : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C) (h₃ : Bet A P A') :
    ∃ Q, Bet P Q C ∧ Bet B Q B' := by
  have H2 := inner_pasch C A A' B' P (between_symmetry h₂) h₃
  obtain ⟨x, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  have H6 := inner_pasch B' C A x B H4 (between_symmetry h₁)
  obtain ⟨y, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  exact ⟨y, (⟨(between_symmetry (between_symmetry (between_exchange2 H5 H8))), H9⟩)⟩

theorem lower_dim_ex_c :
    ∃ A B C : Tpoint, ¬ (Bet A B C ∨ Bet B C A ∨ Bet C A B) :=
  ⟨PA, (⟨PB, (⟨PC, lower_dim⟩)⟩)⟩

theorem two_distinct_points_c : ∃ X Y : Tpoint, X ≠ Y := by
  obtain ⟨A, B, C, h⟩ := lower_dim_ex (Tpoint := Tpoint)
  refine ⟨A, B, ?_⟩
  intro hAB; subst hAB
  exact h (.inr (.inr (between_trivial C A)))

theorem point_construction_different_c (A B : Tpoint) :
    ∃ C, Bet A B C ∧ B ≠ C := by
  obtain ⟨x, y, hxy⟩ := two_distinct_points_c (Tpoint := Tpoint)
  obtain ⟨F, hbet, hcong⟩ := segment_construction A B x y
  refine ⟨F, hbet, ?_⟩
  intro e
  rw [← e] at hcong
  exact hxy (cong_reverse_identity_c B x y hcong)

theorem another_point_c (A : Tpoint) : ∃ B, A ≠ B := by
  have pcd := point_construction_different A A
  obtain ⟨B, H⟩ := pcd
  obtain ⟨_, H0⟩ := H
  exact ⟨B, H0⟩

theorem l2_11_b_c (Cong_stability : ∀ A B C D : Tpoint, ¬ ¬ Cong A B C D → Cong A B C D)
    (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A B A' B') (h₄ : Cong B C B' C') : Cong A C A' C' := by
  apply Cong_stability
  intro H3
  have hAB : A ≠ B := by
    intro e
    rw [e] at h₃
    have hA'B' := cong_reverse_identity_c B A' B' h₃
    apply H3
    rw [e, hA'B']
    exact h₄
  have h5 := five_segment A A' B B' C C' A A' h₃ h₄
    (cong_trivial_identity_c A A') (cong_commutativity h₃) h₁ h₂ hAB
  exact H3 (cong_commutativity h5)

theorem cong_dec_eq_dec_b_c (Cong_stability : ∀ A B C D : Tpoint, ¬ ¬ Cong A B C D → Cong A B C D)
    (A B : Tpoint) (h : ¬ A ≠ B) : A = B := by
  apply cong_identity A B A
  apply Cong_stability
  intro HNCong
  apply h
  intro HEq
  rw [HEq] at HNCong
  exact HNCong (cong_pseudo_reflexivity B B)

theorem bet_dec_eq_dec_b_c (Bet_stability : ∀ A B C : Tpoint, ¬ ¬ Bet A B C → Bet A B C)
    (A B : Tpoint) (h : ¬ A ≠ B) : A = B := by
  apply between_identity
  apply Bet_stability
  intro HNBet
  apply h
  intro HEq
  rw [HEq] at HNBet
  apply HNBet
  exact between_trivial_c B B

theorem BetSEq_c (A B C : Tpoint) :
    BetS A B C ↔ Bet A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  constructor
  · intro ⟨hbet, hab, hac, hbc⟩
    exact ⟨hbet, hab, hac, hbc⟩
  · intro ⟨hbet, hab, hac, hbc⟩
    exact ⟨hbet, hab, hac, hbc⟩

#print axioms GeocoqTranslate.Tarski.Base.bet_col_c
#print axioms GeocoqTranslate.Tarski.Base.between_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.between_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.Bet_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Bet_perm_c
#print axioms GeocoqTranslate.Tarski.Base.between_trivial2_c
#print axioms GeocoqTranslate.Tarski.Base.between_equality_c
#print axioms GeocoqTranslate.Tarski.Base.between_equality_2_c
#print axioms GeocoqTranslate.Tarski.Base.between_exchange3_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq12_neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq21_neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq23_neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq32_neq_c
#print axioms GeocoqTranslate.Tarski.Base.not_bet_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.between_inner_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.outer_transitivity_between2_c
#print axioms GeocoqTranslate.Tarski.Base.between_exchange2_c
#print axioms GeocoqTranslate.Tarski.Base.outer_transitivity_between_c
#print axioms GeocoqTranslate.Tarski.Base.between_exchange4_c
#print axioms GeocoqTranslate.Tarski.Base.l3_9_4_c
#print axioms GeocoqTranslate.Tarski.Base.l3_17_c
#print axioms GeocoqTranslate.Tarski.Base.lower_dim_ex_c
#print axioms GeocoqTranslate.Tarski.Base.two_distinct_points_c
#print axioms GeocoqTranslate.Tarski.Base.point_construction_different_c
#print axioms GeocoqTranslate.Tarski.Base.another_point_c
#print axioms GeocoqTranslate.Tarski.Base.l2_11_b_c
#print axioms GeocoqTranslate.Tarski.Base.cong_dec_eq_dec_b_c
#print axioms GeocoqTranslate.Tarski.Base.bet_dec_eq_dec_b_c
#print axioms GeocoqTranslate.Tarski.Base.BetSEq_c

end GeocoqTranslate.Tarski.Base
