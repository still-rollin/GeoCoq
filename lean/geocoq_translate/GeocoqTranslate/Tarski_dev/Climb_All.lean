import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem cong_reflexivity_c (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B (cong_pseudo_reflexivity B A) (cong_pseudo_reflexivity B A)

theorem cong_symmetry_c (A B C D : Tpoint) (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_reflexivity A B)

theorem cong_transitivity_c (A B C D E F : Tpoint)
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symmetry h1) h2

theorem cong_left_commutativity_c (A B C D : Tpoint)
    (h : Cong A B C D) : Cong B A C D :=
  cong_inner_transitivity A B B A C D (cong_symmetry (cong_pseudo_reflexivity B A)) h

theorem cong_right_commutativity_c (A B C D : Tpoint)
    (h : Cong A B C D) : Cong A B D C :=
  cong_symmetry ((let H0 := cong_symmetry h; cong_left_commutativity H0))

theorem cong_3421_c (A B C D : Tpoint) (h : Cong A B C D) : Cong C D B A :=
  cong_right_commutativity (cong_right_commutativity (cong_right_commutativity (cong_symmetry h)))

theorem cong_4312_c (A B C D : Tpoint) (h : Cong A B C D) : Cong D C A B :=
  cong_right_commutativity (cong_right_commutativity (cong_symmetry (cong_right_commutativity h)))

theorem cong_4321_c (A B C D : Tpoint) (h : Cong A B C D) : Cong D C B A :=
  cong_right_commutativity (cong_symmetry (cong_right_commutativity h))

theorem cong_trivial_identity_c (A B : Tpoint) : Cong A A B B := by
  obtain ⟨E, hBet, hCong⟩ := segment_construction B A B B
  have hAE : A = E := cong_identity A E B hCong
  rw [← hAE] at hCong
  exact hCong

theorem cong_reverse_identity_c (A C D : Tpoint) (h : Cong A A C D) : C = D :=
  (let H0 := cong_symmetry h; cong_identity C D A H0)

theorem cong_commutativity_c (A B C D : Tpoint) (h : Cong A B C D) : Cong B A D C :=
  cong_left_commutativity (cong_right_commutativity h)

theorem not_cong_2134_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A C D :=
  (fun H0 => h (cong_symmetry (cong_3421_c B A C D H0)))

theorem not_cong_1243_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong A B D C :=
  (fun H0 => h (cong_symmetry (cong_4312_c A B D C H0)))

theorem not_cong_2143_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A D C :=
  (fun H0 => h (cong_symmetry (cong_4321_c B A D C H0)))

theorem not_cong_3412_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D A B :=
  (fun H0 => h (cong_symmetry H0))

theorem not_cong_4312_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C A B :=
  (fun H0 => h (cong_symmetry (cong_left_commutativity H0)))

theorem not_cong_3421_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D B A :=
  (fun H0 => h (cong_symmetry (cong_right_commutativity H0)))

theorem not_cong_4321_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C B A :=
  (fun H0 => h (cong_symmetry (cong_commutativity H0)))

theorem five_segment_with_def_c (A B C D A' B' C' D' : Tpoint)
    (h : OFSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨H1, H2⟩ := h
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  exact five_segment A A' B B' C C' D D' H5 H7 H9 H10 H1 H3 hAB

theorem cong_diff_c (A B C D : Tpoint) (hAB : A ≠ B) (h : Cong A B C D) : C ≠ D := by
  intro hCD; apply hAB
  rw [hCD] at h
  exact cong_identity A B D h

theorem cong_diff_2_c (A B C D : Tpoint) (hBA : B ≠ A) (h : Cong A B C D) : C ≠ D := by
  intro hCD; apply hBA
  rw [hCD] at h
  exact (cong_identity A B D h).symm

theorem cong_diff_3_c (A B C D : Tpoint) (hCD : C ≠ D) (h : Cong A B C D) : A ≠ B := by
  intro hAB; apply hCD
  rw [hAB] at h
  exact cong_identity C D B (cong_symmetry h)

theorem cong_diff_4_c (A B C D : Tpoint) (hDC : D ≠ C) (h : Cong A B C D) : A ≠ B := by
  intro hAB; apply hDC
  rw [hAB] at h
  exact (cong_identity C D B (cong_symmetry h)).symm

theorem cong_3_sym_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem cong_3_swap_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 B A C B' A' C' := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry (cong_symmetry (cong_symmetry (cong_4321_c A B A' B' H0)))), (⟨H3, H2⟩)⟩

theorem cong_3_swap_2_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A C B A' C' B' := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨H2, (⟨H0, (cong_symmetry (cong_symmetry (cong_symmetry (cong_4321_c B C B' C' H3))))⟩)⟩

theorem cong3_transitivity_c (A0 B0 C0 A1 B1 C1 A2 B2 C2 : Tpoint)
    (h1 : Cong_3 A0 B0 C0 A1 B1 C1) (h2 : Cong_3 A1 B1 C1 A2 B2 C2) :
    Cong_3 A0 B0 C0 A2 B2 C2 := by
  obtain ⟨H1, H2⟩ := h2
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := h1
  obtain ⟨H7, H8⟩ := H6
  exact ⟨(cong_transitivity H5 H1), (⟨(cong_transitivity H7 H3), (cong_transitivity H8 H4)⟩)⟩

theorem eq_dec_points_c (A B : Tpoint) : A = B ∨ A ≠ B := point_equality_decidability A B

theorem distinct_c (P Q R : Tpoint) (hPQ : P ≠ Q) : R ≠ P ∨ R ≠ Q := by
  have o := point_equality_decidability R P
  rcases o with H0 | H0
  · subst H0
    exact Or.inr hPQ
  · exact Or.inl H0

theorem l2_11_c (A B C A' B' C' : Tpoint)
    (h1 : Bet A B C) (h2 : Bet A' B' C')
    (h3 : Cong A B A' B') (h4 : Cong B C B' C') : Cong A C A' C' := by
  have o := point_equality_decidability A B
  rcases o with H3 | H3
  · subst H3
    have H6 := cong_identity A' B' A (cong_symmetry h3)
    subst H6
    exact h4
  · exact cong_commutativity (five_segment A A' B B' C C' A A' h3 h4 (cong_trivial_identity A A') (cong_symmetry (cong_symmetry (cong_commutativity h3))) h1 h2 H3)

theorem bet_cong3_c (A B C A' B' : Tpoint)
    (h1 : Bet A B C) (h2 : Cong A B A' B') : ∃ C', Cong_3 A B C A' B' C' := by
  have H1 := segment_construction A' B' B C
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := l2_11 h1 H3 h2 (cong_symmetry H4)
  exact ⟨x, (⟨h2, (⟨H5, (cong_symmetry H4)⟩)⟩)⟩

theorem construction_uniqueness_c (Q A B C X Y : Tpoint)
    (hQA : Q ≠ A) (hBet1 : Bet Q A X) (hCong1 : Cong A X B C)
    (hBet2 : Bet Q A Y) (hCong2 : Cong A Y B C) : X = Y := by
  have hAXAY : Cong A X A Y := cong_transitivity_c A X B C A Y hCong1 (cong_symmetry hCong2)
  have hQXQY : Cong Q X Q Y := l2_11_c Q A X Q A Y hBet1 hBet2 (cong_reflexivity Q A) hAXAY
  have hofsc : OFSC Q A X Y Q A X X :=
    ⟨hBet1, hBet1, cong_reflexivity Q A, cong_reflexivity A X,
     cong_symmetry hQXQY, cong_symmetry hAXAY⟩
  exact cong_identity X Y X (five_segment_with_def_c Q A X Y Q A X X hofsc hQA)

theorem Cong_cases_c (A B C D : Tpoint)
    (h : Cong A B C D ∨ Cong A B D C ∨ Cong B A C D ∨ Cong B A D C ∨
         Cong C D A B ∨ Cong C D B A ∨ Cong D C A B ∨ Cong D C B A) :
    Cong A B C D := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact cong_symmetry (cong_symmetry (cong_right_commutativity H2))
    · rcases H2 with H3 | H3
      · exact cong_symmetry (cong_symmetry (cong_left_commutativity H3))
      · rcases H3 with H4 | H4
        · exact cong_symmetry (cong_symmetry (cong_commutativity H4))
        · rcases H4 with H5 | H5
          · exact cong_symmetry H5
          · rcases H5 with H6 | H6
            · exact cong_symmetry (cong_symmetry (cong_4312_c C D B A H6))
            · rcases H6 with H7 | H7
              · exact cong_symmetry (cong_symmetry (cong_3421_c D C A B H7))
              · exact cong_symmetry (cong_symmetry (cong_4321_c D C B A H7))

theorem Cong_perm_c (A B C D : Tpoint) (h : Cong A B C D) :
    Cong A B C D ∧ Cong A B D C ∧ Cong B A C D ∧ Cong B A D C ∧
    Cong C D A B ∧ Cong C D B A ∧ Cong D C A B ∧ Cong D C B A :=
  ⟨h, (⟨(cong_symmetry (cong_symmetry (cong_right_commutativity h))), (⟨(cong_symmetry (cong_symmetry (cong_left_commutativity h))), (⟨(cong_symmetry (cong_symmetry (cong_commutativity h))), (⟨(cong_symmetry h), (⟨(cong_symmetry (cong_symmetry (cong_3421_c A B C D h))), (⟨(cong_symmetry (cong_symmetry (cong_4312_c A B C D h))), (cong_symmetry (cong_symmetry (cong_4321_c A B C D h)))⟩)⟩)⟩)⟩)⟩)⟩)⟩

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

theorem bet_neq12__neq_c (A B C : Tpoint) (h : Bet A B C) (hAB : A ≠ B) : A ≠ C := by
  intro Heq
  subst Heq
  exact hAB (between_identity A B h)

theorem bet_neq21__neq_c (A B C : Tpoint) (h : Bet A B C) (hBA : B ≠ A) : A ≠ C :=
  bet_neq12__neq h (Ne.symm hBA)

theorem bet_neq23__neq_c (A B C : Tpoint) (h : Bet A B C) (hBC : B ≠ C) : A ≠ C := by
  intro Heq
  subst Heq
  exact hBC (Eq.symm (between_identity A B h))

theorem bet_neq32__neq_c (A B C : Tpoint) (h : Bet A B C) (hCB : C ≠ B) : A ≠ C :=
  bet_neq23__neq h (Ne.symm hCB)

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

theorem l5_1_c (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet A C D ∨ Bet A D C :=
  l5_1 hAB h₁ h₂

theorem l5_2_c (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet B C D ∨ Bet B D C := by
  have H2 := l5_1 hAB h₁ h₂
  rcases H2 with H3 | H3
  · exact Or.inl (between_symmetry (between_symmetry (between_exchange3 h₁ H3)))
  · exact Or.inr (between_symmetry (between_symmetry (between_exchange3 h₂ H3)))

theorem segment_construction_2_c (A Q B C : Tpoint) (hAQ : A ≠ Q) :
    ∃ X, (Bet Q A X ∨ Bet Q X A) ∧ Cong Q X B C := by
  obtain ⟨A', hbet1, hcong1⟩ := segment_construction A Q A Q
  obtain ⟨X, hbet2, hcong2⟩ := segment_construction A' Q B C
  have hA'Q : A' ≠ Q := by
    intro hEq
    rw [hEq] at hcong1
    exact hAQ (cong_identity A Q Q (cong_symmetry hcong1))
  exact ⟨X, l5_2 hA'Q (between_symmetry hbet1) hbet2, hcong2⟩

theorem l5_3_c (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet A C D) : Bet A B C ∨ Bet A C B := by
  have H1 := point_construction_different D A
  obtain ⟨P, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₁))
  have H6 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₂))
  exact l5_2 (Ne.symm H4) H5 H6

theorem bet3__bet_c (A B C D E : Tpoint)
    (h₁ : Bet A B E) (h₂ : Bet A D E) (h₃ : Bet B C D) : Bet A C E := by
  have o := l5_3 h₁ h₂
  rcases o with x | x
  · exact between_exchange4 (between_exchange2 x h₃) h₂
  · exact between_exchange4 (between_exchange2 x (between_symmetry h₃)) h₁

theorem le_bet_c (A B C D : Tpoint) (h : Le C D A B) :
    ∃ X, Bet A X B ∧ Cong A X C D := by
  obtain ⟨Y, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  exact ⟨Y, (⟨H1, (cong_symmetry H2)⟩)⟩

theorem l5_5_1_c (A B C D : Tpoint) (h : Le A B C D) :
    ∃ x, Bet A B x ∧ Cong A x C D := by
  obtain ⟨P, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  have sg := segment_construction A B P D
  obtain ⟨x, H3⟩ := sg
  obtain ⟨H4, H5⟩ := H3
  exact ⟨x, (⟨H4, (l2_11 H4 H1 H2 H5)⟩)⟩

theorem l5_5_2_c (A B C D : Tpoint)
    (h : ∃ x, Bet A B x ∧ Cong A x C D) : Le A B C D := by
  obtain ⟨P, H1, H2⟩ := h
  have H3 : ∃ B', Bet C B' D ∧ Cong_3 A B P C B' D := l4_5_c A B P C D H1 H2
  obtain ⟨y, H5, H6⟩ := H3
  unfold Le
  use y
  unfold Cong_3 at H6
  obtain ⟨H7, H8, H9⟩ := H6
  exact ⟨H5, H7⟩

theorem l5_6_c (A B C D A' B' C' D' : Tpoint)
    (h₁ : Le A B C D) (h₂ : Cong A B A' B') (h₃ : Cong C D C' D') :
    Le A' B' C' D' := by
  obtain ⟨y, H3, H4⟩ := h₁
  have H5 : ∃ z : Tpoint, Bet C' z D' ∧ Cong_3 C y D C' z D' := l4_5_c C y D C' D' H3 h₃
  obtain ⟨z, H7, H8⟩ := H5
  exists z
  constructor
  · exact H7
  · obtain ⟨H9, H10, H11⟩ := H8
    exact cong_transitivity_c A' B' A B C' z (cong_symmetry_c A B A' B' h₂) (cong_transitivity_c A B C y C' z H4 H9)

theorem le_reflexivity_c (A B : Tpoint) : Le A B A B :=
  ⟨B, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))), (cong_reflexivity A B)⟩)⟩

theorem le_transitivity_c (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Le C D E F) : Le A B E F := by
  obtain ⟨y, H2, H3⟩ := h₁
  obtain ⟨z, H5, H6⟩ := h₂
  obtain ⟨P, H9, H10⟩ := l4_5_c C y D E z H2 H6
  obtain ⟨H11, H12, H13⟩ := H10
  exact ⟨P, between_symmetry_c F P E (between_symmetry_c E P F (between_exchange4_c E P z F H9 H5)), cong_transitivity_c A B C y E P H3 H11⟩

theorem between_cong_c (A B C : Tpoint) (hBet : Bet A C B) (hCong : Cong A C A B) :
    C = B :=
  (let H1 := l4_6 (hBet) (⟨hCong, (⟨(cong_symmetry hCong), (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C B))))⟩)⟩); between_equality (between_symmetry H1) (between_symmetry hBet))

theorem cong3_symmetry_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem between_cong_2_c (A B D E : Tpoint)
    (h₁ : Bet A D B) (h₂ : Bet A E B) (h₃ : Cong A D A E) : D = E :=
  cong3_bet_eq_c A E B D (h₂) (⟨(cong_symmetry h₃), (⟨(cong_reflexivity A B), (l4_2 (⟨(between_symmetry h₂), (⟨(between_symmetry h₁), (⟨(cong_reflexivity B A), (⟨(cong_symmetry (cong_symmetry (cong_4321_c A D A E h₃))), (⟨(cong_reflexivity B B), (cong_reflexivity A B)⟩)⟩)⟩)⟩)⟩))⟩)⟩)

theorem between_cong_3_c (A B D E : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B D) (h₂ : Bet A B E) (h₃ : Cong B D B E) : D = E := by
  have T := l5_2 hAB h₁ h₂
  rcases T with H3 | H3
  · exact between_cong_c B E D H3 h₃
  · exact Eq.symm (between_cong_c B D E H3 (cong_symmetry h₃))

theorem le_anti_symmetry_c (A B C D : Tpoint)
    (h₁ : Le A B C D) (h₂ : Le C D A B) : Cong A B C D := by
  have H1 := l5_5_1_c C D A B h₂
  obtain ⟨Y, H2⟩ := h₁
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨T, H5⟩ := H1
  obtain ⟨H6, H7⟩ := H5
  have H8 := cong_symmetry (cong_symmetry (cong_symmetry (cong_transitivity H7 H4)))
  have H9 := between_symmetry (between_symmetry (between_exchange4 H3 H6))
  have H10 := between_cong_c C T Y H9 H8
  subst H10
  have H15 := between_equality (between_symmetry H6) (between_symmetry H3)
  subst H15
  exact H4

theorem cong_dec_c (A B C D : Tpoint) : Cong A B C D ∨ ¬ Cong A B C D := by
  rcases point_equality_decidability A B with hAB | hAB
  · subst B
    rcases point_equality_decidability C D with hCD | hCD
    · subst D
      exact Or.inl (cong_trivial_identity_c A C)
    · refine Or.inr ?_
      intro h
      exact hCD (cong_identity C D A (cong_symmetry_c A A C D h))
  · rcases point_equality_decidability C D with hCD | hCD
    · subst D
      refine Or.inr ?_
      intro h
      exact hAB (cong_identity A B C h)
    · obtain ⟨D', hbet, hcong⟩ := segment_construction_2_c B A C D (Ne.symm hAB)
      rcases point_equality_decidability B D' with hBD' | hBD'
      · subst hBD'
        exact Or.inl hcong
      · refine Or.inr ?_
        intro h
        have hADAB : Cong A D' A B :=
          cong_transitivity_c A D' C D A B hcong (cong_symmetry_c A B C D h)
        rcases hbet with hb | hb
        · exact hBD' (between_cong_c A D' B hb (cong_symmetry_c A D' A B hADAB))
        · exact hBD' (Eq.symm (between_cong_c A B D' hb hADAB))

theorem bet_dec_c (A B C : Tpoint) : Bet A B C ∨ ¬ Bet A B C := by
  obtain ⟨C', hbet, hcong⟩ := segment_construction A B B C
  rcases point_equality_decidability C C' with hCC' | hCC'
  · subst hCC'
    exact Or.inl hbet
  · rcases point_equality_decidability A B with hAB | hAB
    · subst hAB
      exact Or.inl (between_trivial2_c _ _)
    · refine Or.inr ?_
      intro hbetABC
      exact hCC' (between_cong_3_c A B C C' hAB hbetABC hbet (cong_symmetry_c B C' B C hcong))

theorem col_dec_c (A B C : Tpoint) : Col A B C ∨ ¬ Col A B C := by
  rcases bet_dec_c A B C with h | h
  · exact Or.inl (Or.inl h)
  rcases bet_dec_c B C A with h2 | h2
  · exact Or.inl (Or.inr (Or.inl h2))
  rcases bet_dec_c C A B with h3 | h3
  · exact Or.inl (Or.inr (Or.inr h3))
  · exact Or.inr (by rintro (x | x | x); exacts [h x, h2 x, h3 x])

theorem le_trivial_c (A C D : Tpoint) : Le A A C D :=
  ⟨C, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 C D))))), (cong_trivial_identity A C)⟩)⟩

theorem le_cases_c (A B C D : Tpoint) : Le A B C D ∨ Le C D A B := by
  have o := point_equality_decidability A B
  rcases o with H | H
  · subst H
    exact Or.inl (le_trivial_c A C D)
  · have H0 := segment_construction_2_c B A C D (Ne.symm H)
    obtain ⟨X, H1⟩ := H0
    obtain ⟨H2, H3⟩ := H1
    rcases H2 with H4 | H4
    · exact Or.inl (l5_5_2_c A B C D (⟨X, (⟨H4, H3⟩)⟩))
    · exact Or.inr (⟨X, (⟨H4, (cong_symmetry H3)⟩)⟩)

theorem le_zero_c (A B C : Tpoint) (h : Le A B C C) : A = B := by
  have H0 := le_trivial_c C A B
  have H1 := le_anti_symmetry_c A B C C h H0
  have H2 := cong_identity A B C H1
  subst H2
  exact rfl

theorem le_diff_c (A B C D : Tpoint) (hAB : A ≠ B) (h : Le A B C D) : C ≠ D := by
  intro Heq
  subst Heq
  exact hAB (le_zero_c A B C h)

theorem lt_diff_c (A B C D : Tpoint) (h : Lt A B C D) : C ≠ D := by
  intro Heq
  subst Heq
  obtain ⟨x, x0⟩ := h
  have H := le_zero_c A B C x
  subst H
  exact x0 (cong_trivial_identity A C)

theorem bet_cong_eq_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) (h₃ : Cong B C A D) : C = D ∧ A = B := by
  have hCD : C = D := by
    have hLe1 : Le A C A D := ⟨C, h₂, cong_reflexivity A C⟩
    have hLe2 : Le C B C A := ⟨B, between_symmetry h₁, cong_reflexivity C B⟩
    have hLe3 : Le A D A C := l5_6_c C B C A A D A C hLe2
      (cong_left_commutativity_c B C A D h₃) (cong_pseudo_reflexivity C A)
    exact between_cong_c A D C h₂ (le_anti_symmetry_c A C A D hLe1 hLe3)
  refine ⟨hCD, ?_⟩
  rw [← hCD] at h₃
  exact (between_cong_c C A B (between_symmetry h₁) (cong_commutativity h₃)).symm

theorem cong__le_c (A B C D : Tpoint) (h : Cong A B C D) : Le A B C D :=
  ⟨D, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial C D))))), h⟩)⟩

theorem cong__le3412_c (A B C D : Tpoint) (h : Cong A B C D) : Le C D A B :=
  cong__le_c C D A B (cong_symmetry h)

theorem le1221_c (A B : Tpoint) : Le A B B A :=
  cong__le_c A B B A (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity A B))))

theorem le_left_comm_c (A B C D : Tpoint) (h : Le A B C D) : Le B A C D :=
  le_transitivity_c B A A B C D (le1221_c B A) h

theorem le_right_comm_c (A B C D : Tpoint) (h : Le A B C D) : Le A B D C :=
  le_transitivity_c A B C D D C h (le1221_c C D)

theorem le_comm_c (A B C D : Tpoint) (h : Le A B C D) : Le B A D C :=
  le_left_comm_c A B D C (le_right_comm_c A B C D h)

theorem ge_left_comm_c (A B C D : Tpoint) (h : Ge A B C D) : Ge B A C D :=
  le_right_comm_c C D A B h

theorem ge_right_comm_c (A B C D : Tpoint) (h : Ge A B C D) : Ge A B D C :=
  le_left_comm_c C D A B h

theorem ge_comm_c (A B C D : Tpoint) (h : Ge A B C D) : Ge B A D C :=
  ge_left_comm_c A B D C (ge_right_comm_c A B C D h)

theorem lt_right_comm_c (A B C D : Tpoint) (h : Lt A B C D) : Lt A B D C := by
  obtain ⟨H0, H1⟩ := h
  exact ⟨(le_right_comm_c A B C D H0), ((fun H2 => H1 (cong_right_commutativity H2)))⟩

theorem lt_left_comm_c (A B C D : Tpoint) (h : Lt A B C D) : Lt B A C D := by
  obtain ⟨hLe, hNCong⟩ := h
  constructor
  · obtain ⟨P, hBet, hCong⟩ := hLe
    exact ⟨P, hBet, cong_left_commutativity_c A B C P hCong⟩
  · intro hCong
    exact hNCong (cong_left_commutativity_c B A C D hCong)

theorem lt_comm_c (A B C D : Tpoint) (h : Lt A B C D) : Lt B A D C :=
  lt_left_comm_c A B D C (lt_right_comm_c A B C D h)

theorem gt_left_comm_c (A B C D : Tpoint) (h : Gt A B C D) : Gt B A C D :=
  lt_right_comm_c C D A B h

theorem gt_right_comm_c (A B C D : Tpoint) (h : Gt A B C D) : Gt A B D C :=
  lt_left_comm_c C D A B h

theorem gt_comm_c (A B C D : Tpoint) (h : Gt A B C D) : Gt B A D C :=
  gt_left_comm_c A B D C (gt_right_comm_c A B C D h)

theorem cong2_lt__lt_c (A B C D A' B' C' D' : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Cong A B A' B') (h₃ : Cong C D C' D') :
    Lt A' B' C' D' := by
  obtain ⟨x, x0⟩ := h₁
  exact ⟨(l5_6_c A B C D A' B' C' D' x h₂ h₃), ((fun H => x0 (cong_transitivity h₂ (cong_transitivity H (cong_symmetry h₃)))))⟩

theorem fourth_point_c (A B C P : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCol : Col A B P) (hBet : Bet A B C) :
    Bet P A B ∨ Bet A P B ∨ Bet B P C ∨ Bet B C P := by
  rcases hCol with hCol1 | hCol2 | hCol3
  · have HH := l5_2_c A B C P hAB hBet hCol1
    rcases HH with hBCP | hBPC
    · right; right; right; exact hBCP
    · right; right; left; exact hBPC
  · right; left
    exact between_symmetry_c B P A hCol2
  · left
    exact hCol3

theorem third_point_c (A B P : Tpoint) (h : Col A B P) :
    Bet P A B ∨ Bet A P B ∨ Bet A B P := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inl (between_symmetry H1))
    · exact Or.inl H1

theorem l5_12_a_c (A B C : Tpoint) (h : Bet A B C) : Le A B A C ∧ Le B C A C :=
  ⟨(⟨B, (⟨h, (cong_reflexivity A B)⟩)⟩), (le_comm_c C B C A (⟨B, (⟨(between_symmetry h), (cong_reflexivity C B)⟩)⟩))⟩

theorem bet__le1213_c (A B C : Tpoint) (h : Bet A B C) : Le A B A C := by
  have a := l5_12_a_c A B C h
  obtain ⟨x, x0⟩ := a
  exact x

theorem bet__le2313_c (A B C : Tpoint) (h : Bet A B C) : Le B C A C := by
  have a := l5_12_a_c A B C h
  obtain ⟨x, x0⟩ := a
  exact x0

theorem bet__lt1213_c (A B C : Tpoint) (hBC : B ≠ C) (h : Bet A B C) :
    Lt A B A C :=
  ⟨(bet__le1213_c A B C h), ((fun H => hBC (between_cong_c A C B h H)))⟩

theorem bet__lt2313_c (A B C : Tpoint) (hAB : A ≠ B) (h : Bet A B C) :
    Lt B C A C :=
  lt_comm_c C B C A (bet__lt1213_c C B A (Ne.symm hAB) (between_symmetry h))

theorem l5_12_b_c (A B C : Tpoint)
    (hCol : Col A B C) (h₁ : Le A B A C) (h₂ : Le B C A C) : Bet A B C := by
  unfold Col at hCol
  rcases hCol with hBet | hBet | hBet
  · exact hBet
  · have H4 := l5_12_a_c B C A hBet
    obtain ⟨H5, H6⟩ := H4
    have H7 : Cong A B A C := le_anti_symmetry_c A B A C h₁ (le_comm_c C A B A H6)
    have H8 : C = B := between_cong_c A B C (between_symmetry_c B C A hBet) (cong_symmetry_c A B A C H7)
    rw [← H8]
    exact between_trivial_c A C
  · have H4 := l5_12_a_c B A C (between_symmetry_c C A B hBet)
    obtain ⟨H5, H6⟩ := H4
    have H7 : Cong B C A C := le_anti_symmetry_c B C A C h₂ H6
    have H8 : A = B := between_cong_c C B A hBet (cong_symmetry_c C B C A (cong_commutativity_c B C A C H7))
    rw [H8]
    exact between_symmetry_c C B B (between_trivial_c C B)

theorem bet_le_eq_c (A B C : Tpoint)
    (hBet : Bet A B C) (hLe : Le A C B C) : A = B :=
  (let H1 := l5_5_2_c C B C A (⟨A, (⟨(between_symmetry hBet), (cong_reflexivity C A)⟩)⟩); (let H2 := le_anti_symmetry_c A C B C hLe (le_comm_c C B C A H1); Eq.symm (between_cong_c C A B (between_symmetry hBet) (cong_commutativity (cong_symmetry H2)))))

theorem or_lt_cong_gt_c (A B C D : Tpoint) :
    Lt A B C D ∨ Gt A B C D ∨ Cong A B C D := by
  have HH := le_cases_c A B C D
  rcases HH with H | H
  · have o := cong_dec_c A B C D
    rcases o with H0 | H0
    · exact Or.inr (Or.inr H0)
    · exact Or.inl (⟨H, H0⟩)
  · have o := cong_dec_c A B C D
    rcases o with H0 | H0
    · exact Or.inr (Or.inr H0)
    · exact Or.inr (Or.inl ((⟨H, ((fun H1 => H0 (cong_symmetry H1)))⟩)))

theorem lt__le_c (A B C D : Tpoint) (h : Lt A B C D) : Le A B C D := by
  obtain ⟨x, x0⟩ := h
  exact x

theorem le1234_lt__lt_c (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Lt C D E F) : Lt A B E F := by
  obtain ⟨x, x0⟩ := h₂
  exact ⟨(le_transitivity_c A B C D E F h₁ x), ((fun H => x0 (le_anti_symmetry_c C D E F x (l5_6_c A B C D E F C D h₁ H (cong_reflexivity C D)))))⟩

theorem le3456_lt__lt_c (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Le C D E F) : Lt A B E F := by
  obtain ⟨x, x0⟩ := h₁
  exact ⟨(le_transitivity_c A B C D E F x h₂), ((fun H => x0 (le_anti_symmetry_c A B C D x (l5_6_c C D E F C D A B h₂ (cong_reflexivity C D) (cong_symmetry H)))))⟩

theorem lt_transitivity_c (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Lt C D E F) : Lt A B E F :=
  le1234_lt__lt_c A B C D E F (lt__le_c A B C D h₁) h₂

theorem not_and_lt_c (A B C D : Tpoint) : ¬ (Lt A B C D ∧ Lt C D A B) := by
  rintro ⟨⟨hle1, hnc⟩, ⟨hle2, _⟩⟩
  exact hnc (le_anti_symmetry_c A B C D hle1 hle2)

theorem nlt_c (A B : Tpoint) : ¬ Lt A B A B := fun h => not_and_lt_c A B A B ⟨h, h⟩

theorem le__nlt_c (A B C D : Tpoint) (h : Le A B C D) : ¬ Lt C D A B := by
  rintro ⟨hle2, hnc2⟩
  exact not_and_lt_c A B C D
    ⟨⟨h, fun hc => hnc2 (cong_symmetry_c A B C D hc)⟩, ⟨hle2, hnc2⟩⟩

theorem cong__nlt_c (A B C D : Tpoint) (h : Cong A B C D) : ¬ Lt A B C D :=
  le__nlt_c C D A B (⟨B, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))), (cong_symmetry h)⟩)⟩)

theorem nlt__le_c (A B C D : Tpoint) (h : ¬ Lt A B C D) : Le C D A B := by
  have o := le_cases_c A B C D
  rcases o with x | x
  · have o0 := cong_dec_c C D A B
    rcases o0 with x0 | x0
    · exact cong__le_c C D A B x0
    · exact ((h (⟨x, ((fun H1 => x0 (cong_symmetry H1)))⟩))).elim
  · exact x

theorem lt__nle_c (A B C D : Tpoint) (h : Lt A B C D) : ¬ Le C D A B :=
  fun hle => le__nlt_c C D A B hle h

theorem nle__lt_c (A B C D : Tpoint) (h : ¬ Le A B C D) : Lt C D A B := by
  have o := le_cases_c A B C D
  rcases o with x | x
  · exact ((h x)).elim
  · exact ⟨x, ((fun H0 => h (cong__le_c A B C D (cong_symmetry H0))))⟩

theorem lt1123_c (A B C : Tpoint) (hBC : B ≠ C) : Lt A A B C := by
  refine ⟨le_trivial_c A B C, ?_⟩
  intro hcong
  exact hBC (cong_identity B C A (cong_symmetry hcong))

theorem bet2_le2__le_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Le o a O A) (h₄ : Le o b O B) : Le a b A B := sorry

theorem Le_cases_c (A B C D : Tpoint)
    (h : Le A B C D ∨ Le B A C D ∨ Le A B D C ∨ Le B A D C) :
    Le A B C D := by
  rcases h with x | x
  · exact x
  · rcases x with x0 | x0
    · exact le_left_comm_c B A C D x0
    · rcases x0 with x1 | x1
      · exact le_right_comm_c A B D C x1
      · exact le_comm_c B A D C x1

theorem Lt_cases_c (A B C D : Tpoint)
    (h : Lt A B C D ∨ Lt B A C D ∨ Lt A B D C ∨ Lt B A D C) :
    Lt A B C D := by
  rcases h with x | x
  · exact x
  · rcases x with x0 | x0
    · exact lt_left_comm_c B A C D x0
    · rcases x0 with x1 | x1
      · exact lt_right_comm_c A B D C x1
      · exact lt_comm_c B A D C x1

theorem bet_out_c (A B C : Tpoint) (hBA : B ≠ A) (h : Bet A B C) : Out A B C := by
  refine ⟨hBA, ?_, Or.inl h⟩
  intro hCA
  rw [hCA] at h
  exact hBA (between_identity A B h).symm

theorem bet_out_1_c (A B C : Tpoint) (hBA : B ≠ A) (h : Bet C B A) : Out A B C :=
  bet_out hBA (between_symmetry h)

theorem out_dec_c (P A B : Tpoint) : Out P A B ∨ ¬ Out P A B := by
  rcases point_equality_decidability A P with hA | hA
  · exact Or.inr (fun h => h.1 hA)
  rcases point_equality_decidability B P with hB | hB
  · exact Or.inr (fun h => h.2.1 hB)
  rcases bet_dec_c P A B with hb1 | hb1
  · exact Or.inl ⟨hA, hB, Or.inl hb1⟩
  rcases bet_dec_c P B A with hb2 | hb2
  · exact Or.inl ⟨hA, hB, Or.inr hb2⟩
  · exact Or.inr (fun h => h.2.2.elim hb1 hb2)

theorem out_diff1_c (A B C : Tpoint) (h : Out A B C) : B ≠ A := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  exact H0

theorem out_diff2_c (A B C : Tpoint) (h : Out A B C) : C ≠ A := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨H1, _⟩ := H0
  exact H1

theorem out_distinct_c (A B C : Tpoint) (h : Out A B C) : B ≠ A ∧ C ≠ A :=
  ⟨(out_diff1 h), (out_diff2 h)⟩

theorem out_col_c (A B C : Tpoint) (h : Out A B C) : Col A B C := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨_, H1⟩ := H0
  rcases H1 with H2 | H2
  · exact Or.inl H2
  · exact Or.inr (Or.inl (between_symmetry H2))

theorem l6_2_c (A B C P : Tpoint)
    (hAP : A ≠ P) (hBP : B ≠ P) (hCP : C ≠ P) (h : Bet A P C) :
    Bet B P C ↔ Out P A B := by
  constructor
  · intro H3
    refine ⟨hAP, hBP, ?_⟩
    exact l5_2_c C P A B hCP (between_symmetry_c A P C h) (between_symmetry_c B P C H3)
  · intro H3
    obtain ⟨_, _, H6⟩ := H3
    cases H6 with
    | inl H7 =>
      exact between_symmetry_c C P B
        (between_symmetry_c B P C
          (outer_transitivity_between2_c B A P C
            (between_symmetry_c P A B H7) h hAP))
    | inr H7 =>
      exact between_symmetry_c C P B
        (between_symmetry_c B P C
          (between_exchange3_c A B P C (between_symmetry_c P B A H7) h))

theorem bet_out__bet_c (A B C P : Tpoint) (h₁ : Bet A P C) (h₂ : Out P A B) :
    Bet B P C := by
  obtain ⟨hAP, hBP, hOr⟩ := h₂
  rcases eq_dec_points_c C P with hCP | hCP
  · rw [hCP]
    exact between_trivial_c B P
  · exact (l6_2_c A B C P hAP hBP hCP h₁).mpr ⟨hAP, hBP, hOr⟩

theorem l6_3_1_c (A B P : Tpoint) (h : Out P A B) :
    A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C := by
  obtain ⟨hAP, hBP, hBet⟩ := h
  refine ⟨hAP, hBP, ?_⟩
  cases hBet with
  | inl H4 =>
    obtain ⟨C, H7, H8⟩ := point_construction_different_c A P
    exact ⟨C, H8.symm, H7, between_symmetry_c C P B (between_symmetry_c B P C (outer_transitivity_between2_c B A P C (between_symmetry_c P A B H4) H7 hAP))⟩
  | inr H4 =>
    obtain ⟨C, H7, H8⟩ := point_construction_different_c B P
    exact ⟨C, H8.symm, between_symmetry_c C P A (between_symmetry_c A P C (outer_transitivity_between2_c A B P C (between_symmetry_c P B A H4) H7 hBP)), H7⟩

theorem l6_3_2_c (A B P : Tpoint)
    (h : A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C) :
    Out P A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨C, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  exact ⟨H0, (⟨H2, (l5_2 H5 (between_symmetry H7) (between_symmetry H8))⟩)⟩

theorem l6_4_1_c (A B P : Tpoint) (h : Out P A B) : Col A P B ∧ ¬ Bet A P B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  rcases H3 with H4 | H4
  · exact ⟨(Or.inr (Or.inr (between_symmetry H4))), ((fun H5 => H0 (between_equality H5 H4)))⟩
  · exact ⟨(Or.inr (Or.inl H4)), ((fun H5 => H2 (between_equality (between_symmetry H5) H4)))⟩

theorem l6_4_2_c (A B P : Tpoint) (h : Col A P B ∧ ¬ Bet A P B) : Out P A B := by
  obtain ⟨H0, H1⟩ := h
  rcases H0 with H2 | H2
  · exact ((H1 H2)).elim
  · have o := point_equality_decidability A P
    rcases o with H3 | H3
    · subst H3
      rcases H2 with _ | _
      · exact ⟨((fun _ => H1 (between_trivial2 A B))), (⟨((fun _ => H1 (between_trivial2 A B))), (Or.inl (between_trivial2 A B))⟩)⟩
      · exact ⟨((fun _ => H1 (between_trivial2 A B))), (⟨((fun _ => H1 (between_trivial2 A B))), (Or.inl (between_trivial2 A B))⟩)⟩
    · have o0 := point_equality_decidability B P
      rcases o0 with H4 | H4
      · subst H4
        rcases H2 with H8 | H8
        · exact ⟨((fun H9 => (let H10 := H3 H9; (H10).elim))), (⟨((fun _ => H1 (between_trivial A B))), (Or.inr H8)⟩)⟩
        · exact ⟨((fun H9 => (let H10 := H3 H9; (H10).elim))), (⟨((fun _ => H1 (between_trivial A B))), (Or.inl H8)⟩)⟩
      · rcases H2 with H5 | H5
        · exact ⟨H3, (⟨H4, (Or.inr H5)⟩)⟩
        · exact ⟨H3, (⟨H4, (Or.inl (between_symmetry H5))⟩)⟩

theorem out_trivial_c (P A : Tpoint) (hAP : A ≠ P) : Out P A A :=
  ⟨hAP, (⟨hAP, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 A P)))))⟩)⟩

theorem l6_6_c (P A B : Tpoint) (h : Out P A B) : Out P B A := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  rcases H3 with H4 | H4
  · exact ⟨((fun H5 => (let H6 := H2 H5; (H6).elim))), (⟨((fun H5 => (let H6 := H0 H5; (H6).elim))), (Or.inr H4)⟩)⟩
  · exact ⟨((fun H5 => (let H6 := H2 H5; (H6).elim))), (⟨((fun H5 => (let H6 := H0 H5; (H6).elim))), (Or.inl H4)⟩)⟩

theorem l6_7_c (P A B C : Tpoint) (h₁ : Out P A B) (h₂ : Out P B C) : Out P A C := by
  obtain ⟨H5, H6_, H7⟩ := h₁
  obtain ⟨H1, H3, H4⟩ := h₂
  refine ⟨H5, H3, ?_⟩
  rcases H7 with H8 | H8
  · rcases H4 with H9 | H9
    · exact Or.inl (between_exchange4_c P A B C H8 H9)
    · exact l5_3_c P A C B H8 H9
  · rcases H4 with H9 | H9
    · exact l5_1_c P B A C (Ne.symm H1) H8 H9
    · exact Or.inr (between_symmetry_c A C P (between_symmetry_c P C A (between_exchange4_c P C B A H9 H8)))

theorem bet_out_out_bet_c (A B C A' C' : Tpoint)
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

theorem out2_bet_out_c (A B C X P : Tpoint)
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

theorem l6_11_uniqueness_c (A B C R X Y : Tpoint)
    (h₁ : Out A X R) (h₂ : Cong A X B C)
    (h₃ : Out A Y R) (h₄ : Cong A Y B C) : X = Y := by
  obtain ⟨hXA, hRA, horX⟩ := h₁
  obtain ⟨hYA, -, horY⟩ := h₃
  have hCgXY : Cong A X A Y :=
    cong_transitivity_c A X B C A Y h₂ (cong_symmetry_c A Y B C h₄)
  rcases horX with hX | hX
  · rcases horY with hY | hY
    · exact l4_19_c A R X Y hX hCgXY
        (l4_3_c R X A R Y A (between_symmetry_c A X R hX) (between_symmetry_c A Y R hY)
          (cong_reflexivity R A) (cong_commutativity_c A X A Y hCgXY))
    · exact between_cong_c A Y X (between_exchange4_c A X R Y hX hY) hCgXY
  · rcases horY with hY | hY
    · exact (between_cong_c A X Y (between_exchange4_c A Y R X hY hX)
        (cong_symmetry_c A X A Y hCgXY)).symm
    · rcases l5_1_c A R X Y (Ne.symm hRA) hX hY with hb | hb
      · exact between_cong_c A Y X hb hCgXY
      · exact (between_cong_c A X Y hb (cong_symmetry_c A X A Y hCgXY)).symm

theorem l6_11_existence_c (A B C R : Tpoint) (hRA : R ≠ A) (hBC : B ≠ C) :
    ∃ X, Out A X R ∧ Cong A X B C := by
  obtain ⟨X, hbet, hcong⟩ := segment_construction_2_c R A B C hRA
  have hXA : X ≠ A := by
    intro e
    rw [e] at hcong
    exact hBC (cong_reverse_identity_c A B C hcong)
  exact ⟨X, ⟨hXA, hRA, Or.symm hbet⟩, hcong⟩

theorem segment_construction_3_c (A B X Y : Tpoint) (hAB : A ≠ B) (hXY : X ≠ Y) :
    ∃ C, Out A B C ∧ Cong A C X Y := by
  obtain ⟨C0, hout, hcong⟩ := l6_11_existence_c A X Y B (Ne.symm hAB) hXY
  exact ⟨C0, l6_6_c A C0 B hout, hcong⟩

theorem l6_13_1_c (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Le P A P B) :
    Bet P A B := by
  obtain ⟨hAP, hBP, hor⟩ := h₁
  rcases hor with hb | hb
  · exact hb
  · obtain ⟨Y, hBetY, hCgY⟩ := h₂
    have hYP : Y ≠ P := by
      intro hyp
      rw [hyp] at hCgY
      have : P = A := cong_reverse_identity_c P P A (cong_symmetry_c P A P P hCgY)
      exact hAP this.symm
    have hOutY : Out P Y B := ⟨hYP, hBP, Or.inl hBetY⟩
    have hOutA : Out P A B := ⟨hAP, hBP, Or.inr hb⟩
    have hYA : Y = A := l6_11_uniqueness_c P P A B Y A hOutY
      (cong_symmetry_c P A P Y hCgY) hOutA (cong_reflexivity P A)
    rw [hYA] at hBetY
    exact hBetY

theorem l6_13_2_c (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Bet P A B) :
    Le P A P B :=
  ⟨A, (⟨h₂, (cong_reflexivity P A)⟩)⟩

theorem l6_16_1_c (P Q S X : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col S P Q) (h₂ : Col X P Q) : Col X P S := by
  have H3 : (Bet P S X ∨ Bet P X S) → Col X P S := fun d =>
    d.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (between_symmetry h)))
  rcases h₁ with hS | hS | hS <;> rcases h₂ with hX | hX | hX
  · exact H3 (l5_2 (Ne.symm hPQ) (between_symmetry hS) (between_symmetry hX))
  · exact Or.inl (between_symmetry (outer_transitivity_between_c S P Q X hS hX hPQ))
  · exact Or.inl (between_exchange3_c Q X P S hX (between_symmetry hS))
  · exact Or.inl (outer_transitivity_between_c X P Q S hX hS hPQ)
  · exact H3 (l5_1 hPQ hS hX)
  · exact Or.inr (Or.inr (between_symmetry (between_exchange4_c P X Q S (between_symmetry hX) hS)))
  · exact Or.inl (between_inner_transitivity_c X P S Q hX (between_symmetry hS))
  · exact H3 (Or.inl (between_exchange4_c P S Q X (between_symmetry hS) hX))
  · exact H3 (l5_3_c P S X Q (between_symmetry hS) (between_symmetry hX))

theorem col_transitivity_1_c (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col P A B := by
  rcases point_equality_decidability A P with e | hAP
  · rw [e]
    exact col_trivial_1_c P B
  · exact col_permutation_1_c B P A
      (l6_16_1_c P Q A B hPQ (col_permutation_2_c P Q A h₁) (col_permutation_2_c P Q B h₂))

theorem col_transitivity_2_c (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col Q A B :=
  col_transitivity_1_c Q P A B (Ne.symm hPQ) (col_permutation_5_c Q A P (col_permutation_1_c P Q A h₁)) (col_permutation_5_c Q B P (col_permutation_1_c P Q B h₂))

theorem l6_21_c (A B C D P Q : Tpoint)
    (hNCol : ¬ Col A B C) (hCD : C ≠ D)
    (h₁ : Col A B P) (h₂ : Col A B Q)
    (h₃ : Col C D P) (h₄ : Col C D Q) : P = Q := by
  rcases eq_dec_points_c P Q with hPQ | hPQ
  · exact hPQ
  · exfalso
    have hAB : A ≠ B := (not_col_distincts_c A B C hNCol).2.1
    have hCPQ : Col C P Q := col_transitivity_1_c C D P Q hCD h₃ h₄
    have hAPQ : Col A P Q := col_transitivity_1_c A B P Q hAB h₁ h₂
    rcases eq_dec_points_c Q A with hQA | hQA
    · have hPA : P ≠ A := fun h => hPQ (h.trans hQA.symm)
      rw [hQA] at hCPQ
      exact hNCol (col_transitivity_1_c A P B C (Ne.symm hPA)
        (col_permutation_5_c A B P h₁) (col_permutation_3_c C P A hCPQ))
    · have s1 : Col Q A C := col_transitivity_1_c Q P A C (Ne.symm hPQ)
        (col_permutation_3_c A P Q hAPQ) (col_permutation_3_c C P Q hCPQ)
      exact hNCol (col_transitivity_1_c A Q B C (Ne.symm hQA)
        (col_permutation_5_c A B Q h₂) (col_permutation_4_c Q A C s1))

theorem col2__eq_c (A B X Y : Tpoint)
    (h₁ : Col A X Y) (h₂ : Col B X Y) (h₃ : ¬ Col A X B) : X = Y := by
  apply l6_21_c A X B X X Y h₃
  · intro hBX
    rw [hBX] at h₂ h₃
    exact h₃ (col_trivial_2_c A X)
  · exact col_trivial_2_c A X
  · exact h₁
  · exact col_trivial_2_c B X
  · exact h₂

theorem not_col_exists_c (A B : Tpoint) (hAB : A ≠ B) : ∃ C, ¬ Col A B C := by
  obtain ⟨U, V, W, hL⟩ := lower_dim_ex_c (Tpoint := Tpoint)
  have hNC : ¬ Col U V W := hL
  rcases col_dec_c A B U with h1 | h1
  · rcases col_dec_c A B V with h2 | h2
    · rcases col_dec_c A B W with h3 | h3
      · exfalso
        rcases eq_dec_points_c A U with hAU | hAU
        · have hUVW : Col A V W := col_transitivity_1_c A B V W hAB h2 h3
          rw [hAU] at hUVW
          exact hNC hUVW
        · have c1 : Col A U V := col_transitivity_1_c A B U V hAB h1 h2
          have c2 : Col A U W := col_transitivity_1_c A B U W hAB h1 h3
          exact hNC (col_transitivity_1_c U A V W (Ne.symm hAU)
            (col_permutation_4_c A U V c1) (col_permutation_4_c A U W c2))
      · exact ⟨W, h3⟩
    · exact ⟨V, h2⟩
  · exact ⟨U, h1⟩

theorem col3_c (X Y A B C : Tpoint) (hXY : X ≠ Y)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col X Y C) : Col A B C := by
  have H3 := col_transitivity_1_c X Y A B hXY h₁ h₂
  have o := point_equality_decidability C X
  rcases o with H4 | H4
  · subst H4
    exact col_permutation_1_c C A B H3
  · exact col_permutation_1_c C A B (col_transitivity_1_c C X A B H4 (col_permutation_2_c X A C (col_transitivity_1_c X Y A C hXY h₁ h₃)) (col_permutation_2_c X B C (col_transitivity_1_c X Y B C hXY h₂ h₃)))

theorem colx_c (A B C X Y : Tpoint) (hAB : A ≠ B)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col A B C) : Col X Y C := by
  rcases point_equality_decidability X Y with e | hXY
  · rw [e]
    exact col_trivial_1_c Y C
  · have hXAB : Col X A B := col_transitivity_1_c X Y A B hXY h₁ h₂
    have hYAB : Col Y A B := col_permutation_4_c A Y B
      (l6_16_1_c Y X B A (Ne.symm hXY)
        (col_permutation_2_c Y X B (col_permutation_4_c X Y B h₂))
        (col_permutation_2_c Y X A (col_permutation_4_c X Y A h₁)))
    exact col3_c A B X Y C hAB (col_permutation_1_c X A B hXAB)
      (col_permutation_1_c Y A B hYAB) h₃

theorem out2__bet_c (A B C : Tpoint) (h₁ : Out A B C) (h₂ : Out C A B) : Bet A B C := by
  have Hout3 := l6_4_1_c A B C h₂
  obtain ⟨x, x0⟩ := Hout3
  obtain ⟨x1, x2⟩ := h₁
  obtain ⟨x3, x4⟩ := x2
  rcases x4 with x5 | x5
  · exact x5
  · exact ((x0 x5)).elim

theorem bet2_le2__le1346_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le B C B' C') : Le A C A' C' := sorry

theorem bet2_le2__le2356_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le A' C' A C) : Le B' C' B C := sorry

theorem bet2_le2__le1245_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le B C B' C') (h₄ : Le A' C' A C) : Le A' B' A B :=
  le_comm_c B' A' B A (bet2_le2__le2356_c C B A C' B' A' (between_symmetry h₁) (between_symmetry h₂) (le_comm_c B C B' C' h₃) (le_comm_c A' C' A C h₄))

theorem cong_preserves_bet_c (B A' A0 E D' D0 : Tpoint)
    (h₁ : Bet B A' A0) (h₂ : Cong B A' E D') (h₃ : Cong B A0 E D0)
    (h₄ : Out E D' D0) : Bet E D' D0 := by
  obtain ⟨H3, H4⟩ := h₄
  obtain ⟨_, H5⟩ := H4
  rcases H5 with H6 | H6
  · exact H6
  · have H7 := l5_5_2_c E D0 E D' (⟨D', (⟨H6, (cong_reflexivity E D')⟩)⟩)
    have H8 := l5_6_c B A' B A0 E D' E D0 (l5_5_2_c B A' B A0 (⟨A0, (⟨h₁, (cong_reflexivity B A0)⟩)⟩)) h₂ h₃
    have H9 := le_anti_symmetry_c E D' E D0 H8 H7
    have H10 := between_cong_c E D' D0 H6 (cong_symmetry H9)
    subst H10
    exact H6

theorem out_cong_cong_c (B A A0 E D D0 : Tpoint)
    (h₁ : Out B A A0) (h₂ : Out E D D0)
    (h₃ : Cong B A E D) (h₄ : Cong B A0 E D0) : Cong A A0 D D0 := by
  obtain ⟨_, H3⟩ := h₁
  obtain ⟨_, H4⟩ := H3
  rcases H4 with H5 | H5
  · have H6 := cong_preserves_bet_c B A A0 E D D0 H5 h₃ h₄ h₂
    exact cong_commutativity (l4_3 (between_symmetry H5) (between_symmetry H6) (cong_symmetry (cong_symmetry (cong_commutativity h₄))) (cong_symmetry (cong_symmetry (cong_commutativity h₃))))
  · have H6 := cong_preserves_bet_c B A0 A E D0 D H5 h₄ h₃ (l6_6 h₂)
    exact l4_3 (between_symmetry H5) (between_symmetry H6) (cong_symmetry (cong_symmetry (cong_commutativity h₃))) (cong_symmetry (cong_symmetry (cong_commutativity h₄)))

theorem not_out_bet_c (A B C : Tpoint) (h₁ : Col A B C) (h₂ : ¬ Out B A C) :
    Bet A B C := by
  rcases eq_dec_points_c A B with hAB | hAB
  · rw [hAB]
    exact between_trivial2_c B C
  · rcases eq_dec_points_c B C with hBC | hBC
    · rw [hBC]
      exact between_trivial_c A C
    · rcases h₁ with h | h | h
      · exact h
      · exact absurd ⟨hAB, Ne.symm hBC, Or.inr h⟩ h₂
      · exact absurd ⟨hAB, Ne.symm hBC, Or.inl (between_symmetry_c C A B h)⟩ h₂

theorem or_bet_out_c (A B C : Tpoint) : Bet A B C ∨ Out B A C ∨ ¬ Col A B C := by
  have o := col_dec_c A B C
  rcases o with x | x
  · have o0 := out_dec_c B A C
    rcases o0 with x0 | x0
    · exact Or.inr (Or.inl x0)
    · exact Or.inl (not_out_bet_c A B C x x0)
  · exact Or.inr (Or.inr x)

theorem not_bet_out_c (A B C : Tpoint) (h₁ : Col A B C) (h₂ : ¬ Bet A B C) :
    Out B A C := by
  have o := or_bet_out_c A B C
  rcases o with x | x
  · exact ((h₂ x)).elim
  · rcases x with x0 | x0
    · exact x0
    · exact ((x0 h₁)).elim

theorem not_bet_and_out_c (A B C : Tpoint) : ¬ (Bet A B C ∧ Out B A C) := by
  intro H
  obtain ⟨H0, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  rcases H5 with H6 | H6
  · have H7 := between_equality H0 H6
    exact ((H2 H7)).elim
  · have H7 := between_equality (between_symmetry H0) H6
    exact ((H4 H7)).elim

theorem out_to_bet_c (A B C A' B' C' : Tpoint)
    (h₁ : Col A' B' C')
    (h₂ : Out B A C ↔ Out B' A' C')
    (h₃ : Bet A B C) : Bet A' B' C' := by
  rcases out_dec_c B A C with H2 | H2
  · -- Out B A C case
    obtain ⟨H3, H5, H6⟩ := H2
    rcases H6 with H7 | H7
    · -- Bet B A C
      have H8 : A = B := between_equality_c A B C h₃ H7
      exact False.elim (H3 H8)
    · -- Bet B C A
      have H8 : Bet A C B := between_symmetry_c B C A H7
      have H9 : C = B := between_equality_c C B A (between_symmetry_c A B C h₃) (between_symmetry_c A C B H8)
      exact False.elim (H5 H9)
  · -- ¬ Out B A C case
    obtain ⟨_, H3⟩ := h₂
    have H4 : ¬ Out B' A' C' := fun H4 => H2 (H3 H4)
    exact not_out_bet_c A' B' C' h₁ H4

theorem col_out2_col_c (A B C AA CC : Tpoint)
    (h₁ : Col A B C) (h₂ : Out B A AA) (h₃ : Out B C CC) : Col AA B CC := by
  rcases h₁ with hBet1 | hBet2 | hBet3
  · -- Case: Bet A B C
    have H3 : Bet AA B CC := bet_out_out_bet_c A B C AA CC hBet1 h₂ h₃
    left
    exact H3
  · -- Case: Bet B C A
    have hCneB : C ≠ B := h₃.1
    have hBetBCA : Bet B C A := hBet2
    have H4 : Out B AA CC :=
      l6_7_c B AA A CC (l6_6_c B A AA h₂)
        (l6_6_c B CC A
          (l6_7_c B CC C A (l6_6_c B C CC h₃)
            (bet_out_c B C A hCneB hBetBCA)))
    exact col_permutation_4_c B AA CC (out_col_c B AA CC H4)
  · -- Case: Bet C A B
    have hAneB : A ≠ B := h₂.1
    have hBetBAC : Bet B A C := between_symmetry_c C A B hBet3
    have H4 : Out B AA CC :=
      l6_6_c B CC AA
        (l6_7_c B CC C AA (l6_6_c B C CC h₃)
          (l6_6_c B AA C
            (l6_7_c B AA A C (l6_6_c B A AA h₂)
              (bet_out_c B A C hAneB hBetBAC))))
    exact col_permutation_4_c B AA CC (out_col_c B AA CC H4)

theorem bet2_out_out_c (A B C B' C' : Tpoint)
    (hBA : B ≠ A) (hB'A : B' ≠ A) (h₁ : Out A C C')
    (h₂ : Bet A B C) (h₃ : Bet A B' C') : Out A B B' := by
  rcases eq_dec_points_c B' C' with rfl | hB'C'
  · -- Case B' = C'
    obtain ⟨hCA, hB'A', hBet⟩ := h₁
    refine ⟨hBA, hB'A, ?_⟩
    rcases hBet with hBetACB' | hBetAB'C
    · left
      exact between_exchange4_c A B C B' h₂ hBetACB'
    · exact l5_3_c A B B' C h₂ hBetAB'C
  · -- Case B' ≠ C'
    obtain ⟨hCA, hC'A, hBet⟩ := h₁
    refine ⟨hBA, hB'A, ?_⟩
    rcases hBet with hBetACC' | hBetAC'C
    · have hABC' : Bet A B C' := between_exchange4_c A B C C' h₂ hBetACC'
      exact l5_3_c A B B' C' hABC' h₃
    · have hB'C'C : Bet B' C' C := between_exchange3_c A B' C' C h₃ hBetAC'C
      have hAB'C : Bet A B' C := outer_transitivity_between_c A B' C' C h₃ hB'C'C hB'C'
      exact l5_3_c A B B' C h₂ hAB'C

theorem bet2__out_c (A B C B' : Tpoint)
    (hAB : A ≠ B) (hAB' : A ≠ B')
    (h₁ : Bet A B C) (h₂ : Bet A B' C) : Out A B B' :=
  bet2_out_out_c A B C B' C (Ne.symm hAB) (Ne.symm hAB') ((let H3 := bet_neq12__neq h₁ hAB; out_trivial (Ne.symm H3))) h₁ h₂

theorem out_bet_out_1_c (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P A B := by
  rcases eq_dec_points_c B P with rfl | hBP
  · exfalso
    exact not_bet_and_out_c A B C ⟨h₂, h₁⟩
  · obtain ⟨hAP, hCP, hBet⟩ := h₁
    refine ⟨hAP, hBP, ?_⟩
    rcases hBet with hPAC | hPCA
    · left
      exact between_inner_transitivity_c P A B C hPAC h₂
    · right
      exact between_exchange2_c P C B A hPCA (between_symmetry_c A B C h₂)

theorem out_bet_out_2_c (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P B C :=
  l6_6 (out_bet_out_1_c C B A P (l6_6 h₁) (between_symmetry h₂))

theorem out_bet__out_c (A B P Q : Tpoint) (h₁ : Bet P Q A) (h₂ : Out Q A B) :
    Out P A B := by
  obtain ⟨hAQ, hBQ, hd⟩ := h₂
  have hAP : A ≠ P := by
    intro e; rw [e] at h₁; exact hAQ (e.trans (between_identity P Q h₁))
  rcases hd with hb | hb
  · exact bet_out_c P A B hAP (outer_transitivity_between2_c P Q A B h₁ hb (Ne.symm hAQ))
  · have hPBA : Bet P B A := between_exchange2_c P Q B A h₁ hb
    have hBP : B ≠ P := by
      intro e; rw [e] at hb hBQ; exact hBQ (between_equality_c P Q A h₁ hb)
    exact l6_6_c P B A (bet_out_c P B A hBP hPBA)

theorem segment_reverse_c (A B C : Tpoint) (h : Bet A B C) :
    ∃ B', Bet A B' C ∧ Cong C B' A B := by
  rcases eq_dec_points_c A B with rfl | hAB
  · exact ⟨C, between_symmetry_c C C A (between_symmetry_c A C C (between_trivial_c A C)), 
          le_anti_symmetry_c C C A A (le_trivial_c C A A) (le_trivial_c A C C)⟩
  · have hCA : C ≠ A := fun hCA => by
      rw [hCA] at h
      exact hAB (between_identity A B h)
    rcases segment_construction_3_c C A A B hCA hAB with ⟨B', hOut, hCong⟩
    exact ⟨B', between_symmetry_c C B' A (cong_preserves_bet_c A B C C B' A h 
              (cong_symmetry_c C B' A B hCong)
              (cong_symmetry_c C A A C (cong_symmetry_c A C C A (cong_right_commutativity_c A C A C (cong_reflexivity_c A C))))
              (l6_6_c C A B' hOut)), hCong⟩

theorem diff_col_ex_c (A B : Tpoint) : ∃ C, A ≠ C ∧ B ≠ C ∧ Col A B C := by
  obtain ⟨C, hBet, hBC⟩ := point_construction_different_c A B
  refine ⟨C, ?_, hBC, bet_col_c A B C hBet⟩
  intro hAC
  rcases eq_dec_points_c A B with hAB | hAB
  · subst hAB
    subst hAC
    exact hBC rfl
  · subst hAC
    have : A = B := between_identity A B hBet
    exact hAB this

theorem diff_bet_ex3_c (A B C : Tpoint) (h : Bet A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := sorry

theorem diff_col_ex3_c (A B C : Tpoint) (h : Col A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := by
  have cas1 := diff_bet_ex3_c A B C
  have cas2 := diff_bet_ex3_c B C A
  have cas3 := diff_bet_ex3_c C A B
  rcases h with H0 | H0
  · exact diff_bet_ex3_c A B C H0
  · rcases H0 with H1 | H1
    · have HH := H1
      have o := point_equality_decidability B C
      rcases o with H2 | H2
      · subst H2
        have H3 := diff_col_ex_c A B
        obtain ⟨D, H4⟩ := H3
        obtain ⟨H5, H6⟩ := H4
        obtain ⟨H7, H8⟩ := H6
        exact ⟨D, (⟨H5, (⟨H7, (⟨H7, H8⟩)⟩)⟩)⟩
      · have HH0 := cas2 HH
        obtain ⟨D, H3⟩ := HH0
        obtain ⟨H4, H5⟩ := H3
        obtain ⟨H6, H7⟩ := H5
        obtain ⟨H8, H9⟩ := H7
        exact ⟨D, (⟨H8, (⟨H4, (⟨H6, (col_permutation_2_c B D A (col_transitivity_1_c B C D A H2 H9 (Or.inl H1)))⟩)⟩)⟩)⟩
    · have o := point_equality_decidability A C
      rcases o with H2 | H2
      · subst H2
        have H3 := diff_col_ex_c A B
        obtain ⟨D, H4⟩ := H3
        obtain ⟨H5, H6⟩ := H4
        obtain ⟨H7, H8⟩ := H6
        exact ⟨D, (⟨H5, (⟨H7, (⟨H5, H8⟩)⟩)⟩)⟩
      · have HH := H1
        have HH0 := cas3 HH
        obtain ⟨D, H3⟩ := HH0
        obtain ⟨H4, H5⟩ := H3
        obtain ⟨H6, H7⟩ := H5
        obtain ⟨H8, H9⟩ := H7
        exact ⟨D, (⟨H6, (⟨H8, (⟨H4, (col_permutation_5_c A D B (col_transitivity_1_c A C D B H2 (col_permutation_4_c C A D H9) (Or.inr (Or.inr (between_symmetry H1)))))⟩)⟩)⟩)⟩

theorem Out_cases_c (A B C : Tpoint) (h : Out A B C ∨ Out A C B) : Out A B C := by
  rcases h with H0 | H0
  · exact H0
  · exact l6_6 H0

theorem midpoint_dec_c (I A B : Tpoint) : Midpoint I A B ∨ ¬ Midpoint I A B := by
  rcases bet_dec_c A I B with hb | hb
  · rcases cong_dec_c A I I B with hc | hc
    · exact Or.inl ⟨hb, hc⟩
    · exact Or.inr (fun h => hc h.2)
  · exact Or.inr (fun h => hb h.1)

theorem is_midpoint_id_c (A B : Tpoint) (h : Midpoint A A B) : A = B := by
  obtain ⟨H0, H1⟩ := h
  have H2 := cong_symmetry H1
  have H3 := cong_identity A B A H2
  subst H3
  exact rfl

theorem is_midpoint_id_2_c (A B : Tpoint) (h : Midpoint A B A) : A = B := by
  obtain ⟨_, H0⟩ := h
  have H1 := cong_identity B A A H0
  exact Eq.symm H1

theorem l7_2_c (M A B : Tpoint) (h : Midpoint M A B) : Midpoint M B A := by
  obtain ⟨H0, H1⟩ := h
  exact ⟨(between_symmetry H0), (cong_symmetry (cong_symmetry (cong_symmetry (cong_commutativity H1))))⟩

theorem l7_3_c (M A : Tpoint) (h : Midpoint M A A) : M = A := by
  obtain ⟨H0, H1⟩ := h
  have H2 := between_identity A M H0
  subst H2
  exact rfl

theorem l7_3_2_c (A : Tpoint) : Midpoint A A A :=
  ⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 A A))))), (cong_reflexivity A A)⟩

theorem symmetric_point_construction_c (P A : Tpoint) : ∃ P', Midpoint A P P' := by
  have sg := segment_construction P A P A
  obtain ⟨E, H⟩ := sg
  obtain ⟨H0, H1⟩ := H
  exact ⟨E, (⟨H0, (cong_symmetry H1)⟩)⟩

theorem symmetric_point_uniqueness_c (A P P₁ P₂ : Tpoint)
    (h₁ : Midpoint P A P₁) (h₂ : Midpoint P A P₂) : P₁ = P₂ := by
  obtain ⟨H1, H2⟩ := h₂
  obtain ⟨H3, H4⟩ := h₁
  rcases (point_equality_decidability A P) with H5 | H5
  · subst H5
    have H8 := cong_symmetry H4
    have H9 := cong_identity A P₁ A H8
    subst H9
    have H10 := cong_symmetry H2
    have H11 := cong_identity A P₂ A H10
    subst H11
    exact rfl
  · exact construction_uniqueness H5 H3 (cong_symmetry H4) H1 (cong_symmetry H2)

theorem l7_9_c (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A Q X) :
    P = Q := by
  obtain ⟨H1, H2⟩ := h₂
  obtain ⟨H3, H4⟩ := h₁
  have o := point_equality_decidability A X
  rcases o with H5 | H5
  · subst H5
    have H8 := cong_identity P A A H4
    subst H8
    have H10 := cong_identity Q P P H2
    subst H10
    exact rfl
  · exact construction_uniqueness (Ne.symm H5) (between_symmetry H3) (cong_symmetry (cong_symmetry (cong_commutativity H4))) (between_symmetry H1) (cong_symmetry (cong_symmetry (cong_commutativity H2)))

theorem l7_9_bis_c (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A X Q) :
    P = Q := by
  obtain ⟨hBetPAX, hCongPAAX⟩ := h₁
  obtain ⟨hBetXAQ, hCongXAAQ⟩ := h₂
  apply l7_9_c P Q A X
  · exact ⟨hBetPAX, hCongPAAX⟩
  · exact ⟨between_symmetry_c X A Q hBetXAQ, cong_symmetry_c A X Q A (cong_symmetry_c Q A A X (cong_4321_c X A A Q hCongXAAQ))⟩

theorem l7_13_c (A P Q P' Q' : Tpoint)
    (h₁ : Midpoint A P' P) (h₂ : Midpoint A Q' Q) : Cong P Q P' Q' := by
  obtain ⟨hB1, hC1⟩ := h₁
  obtain ⟨hB2, hC2⟩ := h₂
  rcases eq_dec_points_c P A with hPA | hPA
  · rw [hPA] at hC1
    have hP'A : P' = A := cong_identity P' A A hC1
    rw [hPA, hP'A]
    exact cong_right_commutativity_c A Q Q' A (cong_symmetry_c Q' A A Q hC2)
  · obtain ⟨X, hBetP'PX, hCongPXQA⟩ := segment_construction P' P Q A
    obtain ⟨X', hBetXP'X', hCongP'X'QA⟩ := segment_construction X P' Q A
    obtain ⟨Y, hBetQ'QY, hCongQYPA⟩ := segment_construction Q' Q P A
    obtain ⟨Y', hBetYQ'Y', hCongQ'Y'PA⟩ := segment_construction Y Q' P A
    have hBetQ'AY : Bet Q' A Y := between_exchange4_c Q' A Q Y hB2 hBetQ'QY
    have hBetYAQ' : Bet Y A Q' := between_symmetry_c Q' A Y hBetQ'AY
    have hBetP'AX : Bet P' A X := between_exchange4_c P' A P X hB1 hBetP'PX
    have hBetAPX : Bet A P X := between_exchange3_c P' A P X hB1 hBetP'PX
    have hBetAQY : Bet A Q Y := between_exchange3_c Q' A Q Y hB2 hBetQ'QY
    have hBetYQA : Bet Y Q A := between_symmetry_c A Q Y hBetAQY
    have hBetAQ'Y' : Bet A Q' Y' := between_exchange3_c Y A Q' Y' hBetYAQ' hBetYQ'Y'
    have hBetXAP' : Bet X A P' := between_symmetry_c P' A X hBetP'AX
    have hBetAP'X' : Bet A P' X' := between_exchange3_c X A P' X' hBetXAP' hBetXP'X'
    have hBetX'P'A : Bet X' P' A := between_symmetry_c A P' X' hBetAP'X'
    have hBetXAX' : Bet X A X' := between_exchange4_c X A P' X' hBetXAP' hBetXP'X'
    have hBetYAY' : Bet Y A Y' := between_exchange4_c Y A Q' Y' hBetYAQ' hBetYQ'Y'
    have hCongAPYQ : Cong A P Y Q :=
      cong_commutativity_c P A Q Y (cong_symmetry_c Q Y P A hCongQYPA)
    have hCongAXYA : Cong A X Y A :=
      l2_11_c A P X Y Q A hBetAPX hBetYQA hCongAPYQ hCongPXQA
    have hCongAQ'AQ : Cong A Q' A Q := cong_left_commutativity_c Q' A A Q hC2
    have hCongAQX'P' : Cong A Q X' P' :=
      cong_commutativity_c Q A P' X' (cong_symmetry_c P' X' Q A hCongP'X'QA)
    have hCongPAP'A : Cong P A P' A :=
      cong_left_commutativity_c A P P' A (cong_symmetry_c P' A A P hC1)
    have hCongQ'Y'P'A : Cong Q' Y' P' A :=
      cong_transitivity_c Q' Y' P A P' A hCongQ'Y'PA hCongPAP'A
    have hCongAY'X'A : Cong A Y' X' A :=
      l2_11_c A Q' Y' X' P' A hBetAQ'Y' hBetX'P'A
        (cong_transitivity_c A Q' A Q X' P' hCongAQ'AQ hCongAQX'P') hCongQ'Y'P'A
    have hCongAQAQ' : Cong A Q A Q' :=
      cong_right_commutativity_c A Q Q' A (cong_symmetry_c Q' A A Q hC2)
    have hCongQYQ'Y' : Cong Q Y Q' Y' :=
      cong_transitivity_c Q Y P A Q' Y' hCongQYPA (cong_symmetry_c Q' Y' P A hCongQ'Y'PA)
    have hCongAYAY' : Cong A Y A Y' :=
      l2_11_c A Q Y A Q' Y' hBetAQY hBetAQ'Y' hCongAQAQ' hCongQYQ'Y'
    have hCongXAY'A : Cong X A Y' A :=
      cong_transitivity_c X A A Y Y' A
        (cong_commutativity_c A X Y A hCongAXYA)
        (cong_right_commutativity_c A Y A Y' hCongAYAY')
    have hCongAX'AY' : Cong A X' A Y' :=
      cong_right_commutativity_c A X' Y' A
        (cong_commutativity_c X' A A Y' (cong_symmetry_c A Y' X' A hCongAY'X'A))
    have hCongAX'AY : Cong A X' A Y :=
      cong_transitivity_c A X' A Y' A Y hCongAX'AY' (cong_symmetry_c A Y A Y' hCongAYAY')
    have hCongXX'Y'Y : Cong X X' Y' Y :=
      l2_11_c X A X' Y' A Y hBetXAX' (between_symmetry_c Y A Y' hBetYAY')
        hCongXAY'A hCongAX'AY
    have hAX : A ≠ X := bet_neq12__neq_c A P X hBetAPX (Ne.symm hPA)
    have hFSC : FSC X A X' Y' Y' A Y X :=
      ⟨bet_col_c X A X' hBetXAX', ⟨hCongXAY'A, hCongXX'Y'Y, hCongAX'AY⟩,
       cong_pseudo_reflexivity X Y',
       cong_symmetry_c A X A Y' (cong_commutativity_c X A Y' A hCongXAY'A)⟩
    have hCongX'Y'YX : Cong X' Y' Y X := l4_16_c X A X' Y' Y' A Y X hFSC (Ne.symm hAX)
    have hCongAXAX' : Cong A X A X' :=
      cong_transitivity_c A X A Y A X'
        (cong_right_commutativity_c A X Y A hCongAXYA)
        (cong_symmetry_c A X' A Y hCongAX'AY)
    have hIFSC1 : IFSC Y Q A X Y' Q' A X' :=
      ⟨hBetYQA, between_symmetry_c A Q' Y' hBetAQ'Y',
       cong_commutativity_c A Y A Y' hCongAYAY',
       cong_left_commutativity_c A Q Q' A (cong_symmetry_c Q' A A Q hC2),
       cong_right_commutativity_c Y X X' Y' (cong_symmetry_c X' Y' Y X hCongX'Y'YX),
       hCongAXAX'⟩
    have hCongQXQ'X' : Cong Q X Q' X' := l4_2_c Y Q A X Y' Q' A X' hIFSC1
    have hIFSC2 : IFSC X P A Q X' P' A Q' :=
      ⟨between_symmetry_c A P X hBetAPX, hBetX'P'A,
       cong_commutativity_c A X A X' hCongAXAX',
       hCongPAP'A,
       cong_commutativity_c Q X Q' X' hCongQXQ'X',
       hCongAQAQ'⟩
    exact l4_2_c X P A Q X' P' A Q' hIFSC2

theorem l7_15_c (P Q R P' Q' R' A : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint A Q Q') (h₃ : Midpoint A R R')
    (h₄ : Bet P Q R) : Bet P' Q' R' :=
  l4_6 h₄ (⟨(l7_13_c A P Q P' Q' (l7_2_c A P P' h₁) (l7_2_c A Q Q' h₂)), (⟨(l7_13_c A P R P' R' (l7_2_c A P P' h₁) (l7_2_c A R R' h₃)), (l7_13_c A Q R Q' R' (l7_2_c A Q Q' h₂) (l7_2_c A R R' h₃))⟩)⟩)

theorem l7_16_c (P Q R S P' Q' R' S' A : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint A Q Q')
    (h₃ : Midpoint A R R') (h₄ : Midpoint A S S')
    (h₅ : Cong P Q R S) : Cong P' Q' R' S' :=
  (let H4 := l7_13_c A P Q P' Q' (l7_2_c A P P' h₁) (l7_2_c A Q Q' h₂); (let H5 := l7_13_c A R S R' S' (l7_2_c A R R' h₃) (l7_2_c A S S' h₄); cong_transitivity (cong_symmetry H4) (cong_transitivity h₅ H5)))

theorem symmetry_preserves_midpoint_c (A B C D E F Z : Tpoint)
    (h₁ : Midpoint Z A D) (h₂ : Midpoint Z B E)
    (h₃ : Midpoint Z C F) (h₄ : Midpoint B A C) : Midpoint E D F := by
  obtain ⟨H3, H4⟩ := h₄
  exact ⟨(l7_15_c A B C D E F Z h₁ h₂ h₃ H3), (l7_16_c A B B C D E E F Z h₁ h₂ h₂ h₃ H4)⟩

theorem Mid_cases_c (A B C : Tpoint) (h : Midpoint A B C ∨ Midpoint A C B) :
    Midpoint A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · exact l7_2_c A C B H1

theorem Mid_perm_c (A B C : Tpoint) (h : Midpoint A B C) :
    Midpoint A B C ∧ Midpoint A C B := by
  obtain ⟨H0, H1⟩ := h
  exact ⟨(⟨H0, H1⟩), (⟨(between_symmetry H0), (cong_symmetry (cong_symmetry (cong_4321_c B A A C H1)))⟩)⟩

theorem l7_17_c (P P' A B : Tpoint) (h₁ : Midpoint A P P') (h₂ : Midpoint B P P') :
    A = B := by
  obtain ⟨X, hMid⟩ := symmetric_point_construction_c B A
  obtain ⟨hBet2, hCong2⟩ := h₂
  have hCongPBP'B : Cong P B P' B := cong_right_commutativity_c P B B P' hCong2
  have hMidRev : Midpoint A X B := l7_2_c A B X hMid
  have hCongP'BPX : Cong P' B P X := l7_13_c A P' B P X h₁ hMidRev
  have hMid1Rev : Midpoint A P' P := l7_2_c A P P' h₁
  have hCongPBP'X : Cong P B P' X := l7_13_c A P B P' X hMid1Rev hMidRev
  have hCongPBPX : Cong P B P X := cong_transitivity_c P B P' B P X hCongPBP'B hCongP'BPX
  have hCongPXP'X : Cong P X P' X :=
    cong_transitivity_c P X P B P' X (cong_symmetry_c P B P X hCongPBPX) hCongPBP'X
  have hCongP'BP'X : Cong P' B P' X := cong_transitivity_c P' B P X P' X hCongP'BPX hCongPXP'X
  have hBX : B = X := l4_19_c P P' B X hBet2 hCongPBPX hCongP'BP'X
  rw [← hBX] at hMid
  exact l7_3_c A B hMid

theorem l7_17_bis_c (P P' A B : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint B P' P) : A = B :=
  l7_17_c P P' A B h₁ (l7_2_c B P' P h₂)

theorem l7_20_c (M A B : Tpoint) (hCol : Col A M B) (hCong : Cong M A M B) :
    A = B ∨ Midpoint M A B := by
  rcases hCol with H1 | H1
  · exact Or.inr (⟨H1, (cong_symmetry (cong_symmetry (cong_left_commutativity hCong)))⟩)
  · rcases H1 with H2 | H2
    · have H3 := l4_3 (between_symmetry H2) (between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 B M))))) (cong_symmetry (cong_symmetry (cong_commutativity hCong))) (cong_reflexivity B M)
      have H4 := cong_identity A B B H3
      subst H4
      exact Or.inl rfl
    · have H3 := l4_3 H2 (between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 A M))))) (cong_symmetry (cong_symmetry (cong_4321_c M A M B hCong))) (cong_reflexivity A M)
      have H4 := cong_identity B A A H3
      subst H4
      exact Or.inl rfl

theorem l7_20_bis_c (M A B : Tpoint) (hAB : A ≠ B)
    (hCol : Col A M B) (hCong : Cong M A M B) : Midpoint M A B := by
  have o := l7_20_c M A B hCol hCong
  rcases o with H2 | H2
  · have H3 := hAB H2
    exact (H3).elim
  · exact H2

theorem cong_col_mid_c (A B C : Tpoint) (hAC : A ≠ C)
    (hCol : Col A B C) (hCong : Cong A B B C) : Midpoint B A C := by
  have H2 := l7_20_c B A C hCol (cong_symmetry (cong_symmetry (cong_left_commutativity hCong)))
  rcases H2 with H3 | H3
  · have H4 := hAC H3
    exact (H4).elim
  · exact H3

theorem l7_21_c (A B C D P : Tpoint)
    (hNCol : ¬ Col A B C) (hBD : B ≠ D)
    (h₁ : Cong A B C D) (h₂ : Cong B C D A)
    (h₃ : Col A P C) (h₄ : Col B P D) :
    Midpoint P A C ∧ Midpoint P B D := by
  obtain ⟨_, _, _, hAC⟩ := not_col_distincts_c A B C hNCol
  obtain ⟨x, hC3⟩ := l4_14_c B D P D B (col_permutation_5_c B P D h₄)
    (cong_pseudo_reflexivity B D)
  have hDBx : Col D B x := l4_13_c B D P D B x (col_permutation_5_c B P D h₄) hC3
  obtain ⟨hBDDB, hBPDx, hDPBx⟩ := hC3
  have hFSC1 : FSC B D P A D B x C :=
    ⟨col_permutation_5_c B P D h₄, ⟨hBDDB, hBPDx, hDPBx⟩,
     cong_commutativity_c A B C D h₁,
     cong_symmetry_c B C D A h₂⟩
  have hFSC2 : FSC B D P C D B x A :=
    ⟨col_permutation_5_c B P D h₄, ⟨hBDDB, hBPDx, hDPBx⟩,
     h₂,
     cong_commutativity_c C D A B (cong_symmetry_c A B C D h₁)⟩
  have hPAxC : Cong P A x C := l4_16_c B D P A D B x C hFSC1 hBD
  have hPCxA : Cong P C x A := l4_16_c B D P C D B x A hFSC2 hBD
  have hCxA : Col C x A := l4_13_c A P C C x A h₃
    ⟨cong_commutativity_c P A x C hPAxC, cong_pseudo_reflexivity A C, hPCxA⟩
  have hPx : P = x := l6_21_c A C B D P x
    (fun hc => hNCol (col_permutation_5_c A C B hc)) hBD
    (col_permutation_5_c A P C h₃)
    (col_permutation_2_c C x A hCxA)
    (col_permutation_5_c B P D h₄)
    (col_permutation_4_c D B x hDBx)
  rw [← hPx] at hPAxC hBPDx
  refine ⟨?_, ?_⟩
  · rcases l7_20_c P A C h₃ hPAxC with hACeq | hM
    · exact absurd hACeq hAC
    · exact hM
  · rcases l7_20_c P B D h₄ (cong_commutativity_c B P D P hBPDx) with hBDeq | hM
    · exact absurd hBDeq hBD
    · exact hM

theorem l7_22_aux_c (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂)
    (h₇ : Le C A₁ C A₂) : Bet M₁ C M₂ := by
  rcases eq_dec_points_c A₂ C with hA2C | hA2C
  · rw [hA2C] at h₇ h₄ h₆
    have hCA1 : C = A₁ := le_zero_c C A₁ C h₇
    rw [← hCA1] at h₃ h₅
    have hCB1 : C = B₁ := cong_reverse_identity_c C C B₁ h₃
    have hCB2 : C = B₂ := cong_reverse_identity_c C C B₂ h₄
    rw [← hCB1] at h₅
    rw [← hCB2] at h₆
    have hM1C : M₁ = C := l7_3_c M₁ C h₅
    have hM2C : M₂ = C := l7_3_c M₂ C h₆
    rw [hM1C, hM2C]
    exact between_trivial_c C C
  · obtain ⟨X, hMX⟩ := symmetric_point_construction_c A₂ C
    obtain ⟨Y, hMY⟩ := symmetric_point_construction_c B₂ C
    obtain ⟨Z, hMZ⟩ := symmetric_point_construction_c M₂ C
    obtain ⟨hBetM2, hCgM2⟩ := h₆
    have hBetXZY : Bet X Z Y := l7_15_c A₂ M₂ B₂ X Z Y C hMX hMZ hMY hBetM2
    have hCgXZZY : Cong X Z Z Y := l7_16_c A₂ M₂ M₂ B₂ X Z Z Y C hMX hMZ hMZ hMY hCgM2
    obtain ⟨hBetA2CX, hCgA2X⟩ := hMX
    obtain ⟨hBetB2CY, hCgB2Y⟩ := hMY
    obtain ⟨hBetM2CZ, hCgM2Z⟩ := hMZ
    have hCgCA2CX : Cong C A₂ C X := cong_left_commutativity_c A₂ C C X hCgA2X
    have hCgCB2CY : Cong C B₂ C Y := cong_left_commutativity_c B₂ C C Y hCgB2Y
    have hCgCXCY : Cong C X C Y :=
      cong_transitivity_c C X C B₂ C Y
        (cong_transitivity_c C X C A₂ C B₂ (cong_symmetry_c C A₂ C X hCgCA2CX) h₄)
        hCgCB2CY
    have hLeX : Le C A₁ C X := l5_6_c C A₁ C A₂ C A₁ C X h₇ (cong_reflexivity C A₁) hCgCA2CX
    have hBetCA1X : Bet C A₁ X := by
      rcases eq_dec_points_c A₁ C with hA1C | hA1C
      · rw [hA1C]
        exact between_trivial2_c C X
      · have hXC : X ≠ C := by
          intro hxc
          rw [hxc] at hLeX
          exact hA1C (le_zero_c C A₁ C hLeX).symm
        exact l6_13_1_c C A₁ X
          ⟨hA1C, hXC, l5_2_c A₂ C A₁ X hA2C (between_symmetry_c A₁ C A₂ h₁) hBetA2CX⟩
          hLeX
    have hLeY : Le C B₁ C Y := l5_6_c C A₁ C X C B₁ C Y hLeX h₃ hCgCXCY
    have hBetCB1Y : Bet C B₁ Y := by
      rcases eq_dec_points_c B₁ C with hB1C | hB1C
      · rw [hB1C]
        exact between_trivial2_c C Y
      · have hYC : Y ≠ C := by
          intro hyc
          rw [hyc] at hLeY
          exact hB1C (le_zero_c C B₁ C hLeY).symm
        have hB2C : B₂ ≠ C := by
          intro hb2c
          rw [hb2c] at h₄
          exact hA2C (cong_identity C A₂ C h₄).symm
        exact l6_13_1_c C B₁ Y
          ⟨hB1C, hYC, l5_2_c B₂ C B₁ Y hB2C (between_symmetry_c B₁ C B₂ h₂) hBetB2CY⟩
          hLeY
    obtain ⟨Q, hQ1, hQ2⟩ := l3_17_c X A₁ C Y B₁ Z
      (between_symmetry_c C A₁ X hBetCA1X)
      (between_symmetry_c C B₁ Y hBetCB1Y)
      hBetXZY
    have hIFSC : IFSC X A₁ C Z Y B₁ C Z :=
      ⟨between_symmetry_c C A₁ X hBetCA1X, between_symmetry_c C B₁ Y hBetCB1Y,
       cong_commutativity_c C X C Y hCgCXCY,
       cong_commutativity_c C A₁ C B₁ h₃,
       cong_right_commutativity_c X Z Z Y hCgXZZY,
       cong_reflexivity C Z⟩
    have hCgA1Z : Cong A₁ Z B₁ Z := l4_2_c X A₁ C Z Y B₁ C Z hIFSC
    have hCgQ : Cong Q A₁ Q B₁ := by
      rcases eq_dec_points_c C Z with hCZ | hCZ
      · rw [← hCZ] at hQ1
        have hCQ : C = Q := between_identity C Q hQ1
        rw [← hCQ]
        exact h₃
      · exact l4_17_c C Z Q A₁ B₁ hCZ
          (col_permutation_2_c Z Q C (bet_col_c Z Q C hQ1))
          h₃ (cong_commutativity_c A₁ Z B₁ Z hCgA1Z)
    have hQM1 : Q = M₁ := l7_17_c A₁ B₁ Q M₁
      ⟨hQ2, cong_left_commutativity_c Q A₁ Q B₁ hCgQ⟩ h₅
    rw [hQM1] at hQ1
    exact between_exchange3_c Z M₁ C M₂ hQ1 (between_symmetry_c M₂ C Z hBetM2CZ)

theorem l7_22_c (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂) : Bet M₁ C M₂ := by
  have H5 := le_cases_c C A₁ C A₂
  rcases H5 with H6 | H6
  · exact l7_22_aux_c A₁ A₂ B₁ B₂ C M₁ M₂ h₁ h₂ h₃ h₄ h₅ h₆ H6
  · exact between_symmetry (l7_22_aux_c A₂ A₁ B₂ B₁ C M₂ M₁ (between_symmetry h₁) (between_symmetry h₂) h₄ h₃ h₆ h₅ H6)

theorem bet_col1_c (A B C D : Tpoint) (h₁ : Bet A B D) (h₂ : Bet A C D) :
    Col A B C := by
  have H1 := l5_3 h₁ h₂
  rcases H1 with H2 | H2
  · exact Or.inl H2
  · exact Or.inr (Or.inl (between_symmetry H2))

theorem l7_25_c (A B C : Tpoint) (h : Cong C A C B) : ∃ X, Midpoint X A B := by
  rcases col_dec_c A B C with hCol | hNCol
  · rcases l7_20_c C A B (col_permutation_5_c A B C hCol) h with hab | hM
    · rw [hab]
      exact ⟨B, l7_3_2_c B⟩
    · exact ⟨C, hM⟩
  · obtain ⟨-, hAB, hBC, hAC⟩ := not_col_distincts_c A B C hNCol
    obtain ⟨P, hBetCAP, hAP⟩ := point_construction_different_c C A
    obtain ⟨Q, hBetCBQ, hCgBQ⟩ := segment_construction C B A P
    obtain ⟨R, hARQ, hBRP⟩ := inner_pasch P Q C A B
      (between_symmetry_c C A P hBetCAP) (between_symmetry_c C B Q hBetCBQ)
    obtain ⟨X, hAXB, hRXC⟩ := inner_pasch C B P A R hBetCAP hBRP
    have hBQ : B ≠ Q := by
      intro hbq
      rw [← hbq] at hCgBQ
      exact hAP (cong_reverse_identity_c B A P hCgBQ)
    have hBP : B ≠ P := by
      intro hbp
      rw [← hbp] at hBetCAP
      exact hNCol (col_permutation_1_c C A B (bet_col_c C A B hBetCAP))
    have hOFSC : OFSC C A P B C B Q A :=
      ⟨hBetCAP, hBetCBQ, h, cong_symmetry_c B Q A P hCgBQ,
       cong_symmetry_c C A C B h, cong_pseudo_reflexivity A B⟩
    have hCgPBQA : Cong P B Q A :=
      five_segment_with_def_c C A P B C B Q A hOFSC (Ne.symm hAC)
    obtain ⟨R', hAR'Q, hC3⟩ := l4_5_c B R P A Q hBRP
      (cong_commutativity_c P B Q A hCgPBQA)
    obtain ⟨-, hCgBPAQ, hCgRPR'Q⟩ := hC3
    have hIFSC1 : IFSC B R P A A R' Q B :=
      ⟨hBRP, hAR'Q, hCgBPAQ, hCgRPR'Q, cong_pseudo_reflexivity B A,
       cong_commutativity_c A P B Q (cong_symmetry_c B Q A P hCgBQ)⟩
    have hCgRAR'B : Cong R A R' B := l4_2_c B R P A A R' Q B hIFSC1
    have hIFSC2 : IFSC B R P Q A R' Q P :=
      ⟨hBRP, hAR'Q, hCgBPAQ, hCgRPR'Q, hCgBQ, cong_pseudo_reflexivity P Q⟩
    have hCgRQR'P : Cong R Q R' P := l4_2_c B R P Q A R' Q P hIFSC2
    have hC3' : Cong_3 A R Q B R' P :=
      ⟨cong_commutativity_c R A R' B hCgRAR'B,
       cong_commutativity_c Q A P B (cong_symmetry_c P B Q A hCgPBQA),
       hCgRQR'P⟩
    have hColBR'P : Col B R' P := l4_13_c A R Q B R' P (bet_col_c A R Q hARQ) hC3'
    have hColCBQ : Col C B Q := bet_col_c C B Q hBetCBQ
    have hRR' : R = R' := l6_21_c A Q B P R R'
      (fun hAQB => hNCol (col_permutation_4_c B A C
        (col_transitivity_1_c B Q A C hBQ
          (col_permutation_3_c A Q B hAQB)
          (col_permutation_1_c C B Q hColCBQ))))
      hBP
      (col_permutation_5_c A R Q (bet_col_c A R Q hARQ))
      (col_permutation_5_c A R' Q (bet_col_c A R' Q hAR'Q))
      (col_permutation_5_c B R P (bet_col_c B R P hBRP))
      (col_permutation_5_c B R' P hColBR'P)
    rw [← hRR'] at hCgRAR'B
    refine ⟨X, hAXB, ?_⟩
    rcases eq_dec_points_c R C with hRC | hRC
    · rw [hRC] at hRXC
      have hCX : C = X := between_identity C X hRXC
      rw [← hCX]
      exact cong_left_commutativity_c C A C B h
    · exact cong_left_commutativity_c X A X B
        (l4_17_c R C X A B hRC
          (col_permutation_5_c R X C (bet_col_c R X C hRXC))
          hCgRAR'B h)

theorem midpoint_distinct_1_c (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    I ≠ A ∧ I ≠ B := by
  constructor
  · intro hIA
    rw [hIA] at h
    obtain ⟨hBet, hCong⟩ := h
    have hCong' : Cong A A A B := hCong
    have hCong'' : Cong A B A A := cong_symmetry_c A A A B hCong'
    have hEq : A = B := cong_identity A B A hCong''
    exact hAB hEq
  · intro hIB
    rw [hIB] at h
    obtain ⟨hBet, hCong⟩ := h
    have hEq : A = B := cong_identity A B B hCong
    exact hAB hEq

theorem midpoint_distinct_2_c (I A B : Tpoint) (hIA : I ≠ A) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ B := by
  have H1 : A ≠ B := fun H1 =>
    let ⟨H2, H3⟩ := h
    let H4 : Bet A I A := H1 ▸ H2
    let H5 : A = I := between_identity A I H4
    hIA (H5 ▸ rfl)
  refine ⟨H1, ?_⟩
  have H2 := midpoint_distinct_1_c I A B H1 h
  exact H2.2

theorem midpoint_distinct_3_c (I A B : Tpoint) (hIB : I ≠ B) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ A := by
  have H1 : A ≠ B := fun H1 =>
    let ⟨H2, H3⟩ := h
    let H5 : Bet A I A := H1 ▸ H2
    let H6 : A = I := between_identity A I H5
    hIB (H1 ▸ H6.symm)
  refine ⟨H1, ?_⟩
  have H2 := midpoint_distinct_1_c I A B H1 h
  exact H2.1

theorem midpoint_def_c (A B C : Tpoint) (h₁ : Bet A B C) (h₂ : Cong A B B C) :
    Midpoint B A C :=
  ⟨h₁, h₂⟩

theorem midpoint_bet_c (A B C : Tpoint) (h : Midpoint B A C) : Bet A B C := by
  obtain ⟨H0, _⟩ := h
  exact H0

theorem midpoint_col_c (A M B : Tpoint) (h : Midpoint M A B) : Col M A B :=
  Or.inr (Or.inr (midpoint_bet_c B M A (l7_2_c M A B h)))

theorem midpoint_cong_c (A B C : Tpoint) (h : Midpoint B A C) : Cong A B B C := by
  obtain ⟨_, H0⟩ := h
  exact H0

theorem midpoint_out_c (A B C : Tpoint) (hAC : A ≠ C) (h : Midpoint B A C) :
    Out A B C := by
  obtain ⟨hBA, _hBC⟩ := midpoint_distinct_1_c B A C hAC h
  refine ⟨?_, ?_, ?_⟩
  · exact hBA
  · exact Ne.symm hAC
  · exact Or.inl (midpoint_bet_c A B C h)

theorem midpoint_out_1_c (A B C : Tpoint) (hAC : A ≠ C) (h : Midpoint B A C) :
    Out C A B :=
  l6_6 (midpoint_out_c C B A (Ne.symm hAC) (l7_2_c B A C h))

theorem midpoint_not_midpoint_c (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    ¬ Midpoint B A I := by
  have hIB : I ≠ B := (midpoint_distinct_1_c I A B hAB h).2
  have hBet1 : Bet A I B := midpoint_bet_c A I B h
  intro h3
  have hBet2 : Bet A B I := midpoint_bet_c A B I h3
  have hIeqB : I = B := by
    have h5 : Bet B I A := between_symmetry_c A I B hBet1
    have h6 : Bet I B A := between_symmetry_c A B I hBet2
    exact between_equality_c I B A h6 h5
  exact hIB hIeqB

theorem swap_diff_c (A B : Tpoint) (h : A ≠ B) : B ≠ A :=
  (fun H0 => h (Eq.symm H0))

theorem cong_cong_half_1_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong A M A' M' := by
  obtain ⟨hBetAMB, hCongAMMB⟩ := h₁
  obtain ⟨hBetA'M'B', hCongA'M'M'B'⟩ := h₂
  obtain ⟨M'', hM''Bet, hCong3⟩ := l4_5_c A M B A' B' hBetAMB h₃
  obtain ⟨hCongAMA'M'', hCongABA'B', hCongMBM''B'⟩ := hCong3
  have hMidM'' : Midpoint M'' A' B' := by
    refine ⟨hM''Bet, ?_⟩
    apply cong_transitivity_c A' M'' A M M'' B'
    · exact cong_symmetry_c A M A' M'' hCongAMA'M''
    · exact cong_transitivity_c A M M B M'' B' hCongAMMB hCongMBM''B'
  have hEq : M' = M'' := by
    apply l7_17_c A' B' M' M''
    · exact ⟨hBetA'M'B', hCongA'M'M'B'⟩
    · exact hMidM''
  rw [hEq]
  exact hCongAMA'M''

theorem cong_cong_half_2_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong B M B' M' :=
  cong_cong_half_1_c B M A B' M' A' (l7_2_c M A B h₁) (l7_2_c M' A' B' h₂) (cong_symmetry (cong_symmetry (cong_commutativity h₃)))

theorem cong_mid2__cong_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A M A' M') : Cong A B A' B' := by
  obtain ⟨x, x0⟩ := h₁
  obtain ⟨x1, x2⟩ := h₂
  exact l2_11 x x1 h₃ (cong_transitivity (cong_transitivity (cong_symmetry x0) h₃) x2)

theorem mid__lt_c (A M B : Tpoint) (hAB : A ≠ B) (h : Midpoint M A B) :
    Lt A M A B := by
  have a := midpoint_distinct_1_c M A B hAB h
  obtain ⟨x, x0⟩ := a
  obtain ⟨x1, x2⟩ := h
  exact ⟨(⟨M, (⟨x1, (cong_reflexivity A M)⟩)⟩), ((fun H1 => x0 (between_cong_c A B M x1 H1)))⟩

theorem le_mid2__le13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A M A' M') : Le A B A' B' := by
  obtain ⟨x, x0⟩ := h₁
  obtain ⟨x1, x2⟩ := h₂
  exact bet2_le2__le1346_c A M B A' M' B' x x1 h₃ (l5_6_c A M A' M' M B M' B' h₃ x0 x2)

theorem le_mid2__le12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A B A' B') : Le A M A' M' := by
  rcases (le_cases_c A M A' M') with H | H
  · exact H
  · have H0 := le_mid2__le13_c A' M' B' A M B h₂ h₁ H
    exact cong__le_c A M A' M' (cong_cong_half_1_c A M B A' M' B' h₁ h₂ (le_anti_symmetry_c A B A' B' h₃ H0))

theorem lt_mid2__lt13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A M A' M') : Lt A B A' B' := by
  obtain ⟨x, x0⟩ := h₃
  exact ⟨(le_mid2__le13_c A M B A' M' B' h₁ h₂ x), ((fun H0 => x0 (cong_cong_half_1_c A M B A' M' B' h₁ h₂ H0)))⟩

theorem lt_mid2__lt12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A B A' B') : Lt A M A' M' := by
  obtain ⟨x, x0⟩ := h₃
  exact ⟨(le_mid2__le12_c A M B A' M' B' h₁ h₂ x), ((fun H0 => x0 (cong_mid2__cong_c A M B A' M' B' h₁ h₂ H0)))⟩

theorem midpoint_preserves_out_c (A B C A' B' C' M : Tpoint)
    (h₀ : Out A B C)
    (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') :
    Out A' B' C' := by
  obtain ⟨hBA, hCA, hBet⟩ := h₀
  refine ⟨?_, ?_, ?_⟩
  · intro hB'A'
    rw [hB'A'] at h₂
    have hAB : A = B := symmetric_point_uniqueness_c A' M A B (l7_2_c M A A' h₁) (l7_2_c M B A' h₂)
    exact hBA hAB.symm
  · intro hC'A'
    rw [hC'A'] at h₃
    have hAC : A = C := symmetric_point_uniqueness_c A' M A C (l7_2_c M A A' h₁) (l7_2_c M C A' h₃)
    exact hCA hAC.symm
  · cases hBet with
    | inl hBet => exact Or.inl (l7_15_c A B C A' B' C' M h₁ h₂ h₃ hBet)
    | inr hBet => exact Or.inr (l7_15_c A C B A' C' B' M h₁ h₃ h₂ hBet)

theorem col_cong_bet_c (A B C D : Tpoint)
    (hCol : Col A B D) (hCong : Cong A B C D) (hBet : Bet A C B) :
    Bet C A D ∨ Bet C B D := sorry

theorem col_cong2_bet1_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet C B D := by
  have o := point_equality_decidability A C
  rcases o with H3 | H3
  · subst H3
    have H6 := cong_symmetry h₂
    have H7 := cong_identity B D A H6
    subst H7
    exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))
  · have HH := col_cong_bet_c A B C D hCol h₁ hBet
    rcases HH with H4 | H4
    · have H5 := bet_cong_eq_c B C A D (between_symmetry hBet) (between_symmetry (between_symmetry (outer_transitivity_between2 (between_symmetry hBet) H4 (Ne.symm H3)))) (cong_symmetry (cong_symmetry (cong_left_commutativity h₂)))
      obtain ⟨H6, H7⟩ := H5
      subst H6
      subst H7
      exact between_symmetry hBet
    · exact H4

theorem col_cong2_bet2_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet C A D := by
  have o := point_equality_decidability B C
  rcases o with H3 | H3
  · subst H3
    have H6 := cong_identity A D B h₂
    subst H6
    exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial B A))))
  · have HH := col_cong_bet_c A B C D hCol h₁ hBet
    rcases HH with H4 | H4
    · exact H4
    · have H5 := bet_cong_eq_c D B C A (between_symmetry H4) (between_symmetry (between_symmetry (between_symmetry (outer_transitivity_between hBet H4 (Ne.symm H3))))) (cong_symmetry (cong_symmetry (cong_3421_c A D B C h₂)))
      obtain ⟨H6, H7⟩ := H5
      subst H7
      subst H6
      exact hBet

theorem col_cong2_bet3_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A B C)
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet B C D := sorry

theorem col_cong2_bet4_c (A B C D : Tpoint)
    (hCol : Col A B C) (hBet : Bet A B D)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet B D C := sorry

theorem col_bet2_cong1_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C B D) : Cong A C D B :=
  l4_3 hBet (between_symmetry h₂) (cong_symmetry (cong_symmetry (cong_right_commutativity h₁))) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C B))))

theorem col_bet2_cong2_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C A D) : Cong D A B C :=
  l4_3 (between_symmetry h₂) (between_symmetry hBet) (cong_symmetry (cong_symmetry (cong_4321_c A B C D h₁))) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity A C))))

theorem bet2_lt2__lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Lt o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

theorem bet2_lt_le__lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Cong o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

theorem per_dec_c (A B C : Tpoint) : Per A B C ∨ ¬ Per A B C := by
  unfold Per
  obtain ⟨C', HC'⟩ := symmetric_point_construction_c C B
  cases cong_dec_c A C A C' with
  | inl h =>
    left
    exact ⟨C', HC', h⟩
  | inr h =>
    right
    intro H0
    obtain ⟨x, H3, H4⟩ := H0
    have H5 : C' = x := symmetric_point_uniqueness_c C B C' x HC' H3
    rw [H5] at h
    exact h H4

theorem l8_2_c (A B C : Tpoint) (h : Per A B C) : Per C B A := by
  obtain ⟨C', H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  have H3 := symmetric_point_construction_c A B
  obtain ⟨A', H4⟩ := H3
  exact ⟨A', (⟨H4, (cong_transitivity (cong_commutativity H2) (l7_13_c B C' A C A' H1 (l7_2_c B A A' H4)))⟩)⟩

theorem Per_cases_c (A B C : Tpoint) (h : Per A B C ∨ Per C B A) : Per A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · exact l8_2_c C B A H1

theorem Per_perm_c (A B C : Tpoint) (h : Per A B C) : Per A B C ∧ Per C B A :=
  ⟨h, (l8_2_c A B C h)⟩

theorem l8_3_c (A B C A' : Tpoint)
    (h₁ : Per A B C) (hAB : A ≠ B) (hCol : Col B A A') : Per A' B C := by
  unfold Per at *
  obtain ⟨C', hMid, hCong⟩ := h₁
  use C'
  constructor
  · exact hMid
  · unfold Midpoint at hMid
    obtain ⟨hBet, hCongMid⟩ := hMid
    exact l4_17_c A B A' C C' hAB
      (col_permutation_5_c A A' B (col_permutation_1_c B A A' hCol))
      hCong
      (cong_symmetry_c B C' B C (cong_symmetry_c B C B C' (cong_left_commutativity_c C B B C' hCongMid)))

theorem l8_4_c (A B C C' : Tpoint) (h₁ : Per A B C) (h₂ : Midpoint B C C') :
    Per A B C' := by
  unfold Per at h₁ ⊢
  obtain ⟨B', hB'_mid, hB'_cong⟩ := h₁
  use C
  refine ⟨?_, ?_⟩
  · exact l7_2_c B C C' h₂
  · have H4 : B' = C' := symmetric_point_uniqueness_c C B B' C' hB'_mid h₂
    rw [← H4]
    exact cong_symmetry_c A C A B' hB'_cong

theorem l8_5_c (A B : Tpoint) : Per A B B :=
  ⟨B, (⟨(l7_3_2_c B), (cong_reflexivity A B)⟩)⟩

theorem l8_6_c (A B C A' : Tpoint)
    (h₁ : Per A B C) (h₂ : Per A' B C) (h₃ : Bet A C A') : B = C := by
  obtain ⟨C', H2⟩ := h₁
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨C'', H5⟩ := h₂
  obtain ⟨H6, H7⟩ := H5
  have H8 := symmetric_point_uniqueness_c C B C' C'' H3 H6
  subst H8
  have H11 := l4_19_c A A' C C' h₃ H4 H7
  subst H11
  exact l7_3_c B C H3

theorem l8_7_c (A B C : Tpoint) (h₁ : Per A B C) (h₂ : Per A C B) : B = C := by
  obtain ⟨C', hMidB, hCong1⟩ := h₁
  obtain ⟨A', hMidCA⟩ := symmetric_point_construction_c A C
  rcases eq_dec_points_c B C with hBC | hBC
  · exact hBC
  · obtain ⟨hBetCBC', hCgCB⟩ := hMidB
    obtain ⟨hBetACA', hCgAC⟩ := hMidCA
    have hPerC'CA : Per C' C A :=
      l8_3_c B C A C' (l8_2_c A C B h₂) hBC (bet_col_c C B C' hBetCBC')
    obtain ⟨Z, hMz, hCz⟩ := hPerC'CA
    have hZA' : Z = A' := symmetric_point_uniqueness_c A C Z A' hMz ⟨hBetACA', hCgAC⟩
    rw [hZA'] at hCz
    have hCong2 : Cong A C' A' C' := cong_commutativity_c C' A C' A' hCz
    have s1 : Cong A' C A C :=
      cong_left_commutativity_c C A' A C (cong_symmetry_c A C C A' hCgAC)
    have hCong3 : Cong A' C A' C' :=
      cong_transitivity_c A' C A C' A' C'
        (cong_transitivity_c A' C A C A C' s1 hCong1) hCong2
    exact l8_6_c A' B C A ⟨C', ⟨hBetCBC', hCgCB⟩, hCong3⟩
      ⟨C', ⟨hBetCBC', hCgCB⟩, hCong1⟩
      (between_symmetry_c A C A' hBetACA')

theorem l8_8_c (A B : Tpoint) (h : Per A B A) : A = B :=
  l8_7_c A A B (l8_2_c B A A (l8_5_c B A)) h

theorem per_distinct_c (A B C : Tpoint) (h : Per A B C) (hAB : A ≠ B) : A ≠ C := by
  intro H1
  subst H1
  exact hAB (l8_8_c A B h)

theorem per_distinct_1_c (A B C : Tpoint) (h : Per A B C) (hBC : B ≠ C) :
    A ≠ C := by
  intro H1
  subst H1
  exact hBC (Eq.symm (l8_8_c A B h))

theorem l8_9_c (A B C : Tpoint) (h₁ : Per A B C) (hCol : Col A B C) :
    A = B ∨ C = B := by
  rcases (point_equality_decidability A B) with H1 | H1
  · exact Or.inl H1
  · exact Or.inr (l8_7_c C C B (l8_2_c B C C (l8_5_c B C)) (l8_3_c A B C C h₁ H1 (col_permutation_5_c B C A (col_permutation_1_c A B C hCol))))

theorem l8_10_c (A B C A' B' C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Cong_3 A B C A' B' C') : Per A' B' C' := by
  obtain ⟨D, hMidD, hCongD⟩ := h₁
  obtain ⟨hc1, hc2, hc3⟩ := h₂
  obtain ⟨D', hBetD', hCongD'⟩ := segment_construction C' B' B' C'
  obtain ⟨hBet1, hCong1⟩ := hMidD
  refine ⟨D', ⟨hBetD', cong_left_commutativity_c B' C' B' D' (cong_symmetry_c B' D' B' C' hCongD')⟩, ?_⟩
  rcases eq_dec_points_c C B with hCB | hCB
  · rw [hCB] at hc3
    have hB'C' : B' = C' := cong_reverse_identity_c B B' C' hc3
    rw [← hB'C'] at hCongD'
    have hB'D' : B' = D' := cong_identity B' D' B' hCongD'
    rw [← hB'C', ← hB'D']
    exact cong_reflexivity A' B'
  · have hOFSC : OFSC C B D A C' B' D' A' :=
      ⟨hBet1, hBetD',
       cong_commutativity_c B C B' C' hc3,
       cong_transitivity_c B D C' B' B' D'
         (cong_transitivity_c B D C B C' B'
           (cong_symmetry_c C B B D hCong1)
           (cong_commutativity_c B C B' C' hc3))
         (cong_left_commutativity_c B' C' B' D' (cong_symmetry_c B' D' B' C' hCongD')),
       cong_commutativity_c A C A' C' hc2,
       cong_commutativity_c A B A' B' hc1⟩
    have hDA : Cong D A D' A' := five_segment_with_def_c C B D A C' B' D' A' hOFSC hCB
    exact cong_transitivity_c A' C' A D A' D'
      (cong_transitivity_c A' C' A C A D (cong_symmetry_c A C A' C' hc2) hCongD)
      (cong_commutativity_c D A D' A' hDA)

theorem col_col_per_per_c (A X C U V : Tpoint)
    (hAX : A ≠ X) (hCX : C ≠ X)
    (h₁ : Col U A X) (h₂ : Col V C X) (h₃ : Per A X C) : Per U X V :=
  (let H4 := l8_3_c A X C U h₃ hAX (col_permutation_5_c X U A (col_permutation_2_c U A X h₁)); (let H5 := l8_2_c U X C H4; l8_2_c V X U (l8_3_c C X U V H5 hCX (col_permutation_5_c X V C (col_permutation_2_c V C X h₂)))))

theorem perp_in_dec_c (X A B C D : Tpoint) :
    Perp_at X A B C D ∨ ¬ Perp_at X A B C D := by
  rcases eq_dec_points_c A B with hAB | hAB
  · refine Or.inr (fun hp => ?_)
    obtain ⟨h1, -⟩ := hp
    exact h1 hAB
  · rcases eq_dec_points_c C D with hCD | hCD
    · refine Or.inr (fun hp => ?_)
      obtain ⟨-, h2, -⟩ := hp
      exact h2 hCD
    · rcases col_dec_c X A B with hXAB | hXAB
      · rcases col_dec_c X C D with hXCD | hXCD
        · rcases eq_dec_points_c B X with hBX | hBX
          · have hAX : A ≠ X := fun h => hAB (h.trans hBX.symm)
            rcases eq_dec_points_c D X with hDX | hDX
            · have hCX : C ≠ X := fun h => hCD (h.trans hDX.symm)
              rcases per_dec_c A X C with hPer | hPer
              · refine Or.inl ⟨hAB, hCD, hXAB, hXCD, fun U V hU hV => ?_⟩
                rw [hBX] at hU
                rw [hDX] at hV
                exact col_col_per_per_c A X C U V hAX hCX hU hV hPer
              · refine Or.inr (fun hp => ?_)
                obtain ⟨-, -, -, -, hUV⟩ := hp
                exact hPer (hUV A C (col_trivial_1_c A B) (col_trivial_1_c C D))
            · rcases per_dec_c A X D with hPer | hPer
              · refine Or.inl ⟨hAB, hCD, hXAB, hXCD, fun U V hU hV => ?_⟩
                rw [hBX] at hU
                have hVDX : Col V D X := col3_c C D V D X hCD
                  (col_permutation_1_c V C D hV) (col_trivial_2_c C D)
                  (col_permutation_1_c X C D hXCD)
                exact col_col_per_per_c A X D U V hAX hDX hU hVDX hPer
              · refine Or.inr (fun hp => ?_)
                obtain ⟨-, -, -, -, hUV⟩ := hp
                exact hPer (hUV A D (col_trivial_1_c A B) (col_trivial_3_c D C))
          · have hUBX : ∀ U, Col U A B → Col U B X := fun U hU =>
              col3_c A B U B X hAB (col_permutation_1_c U A B hU)
                (col_trivial_2_c A B) (col_permutation_1_c X A B hXAB)
            rcases eq_dec_points_c D X with hDX | hDX
            · have hCX : C ≠ X := fun h => hCD (h.trans hDX.symm)
              rcases per_dec_c B X C with hPer | hPer
              · refine Or.inl ⟨hAB, hCD, hXAB, hXCD, fun U V hU hV => ?_⟩
                rw [hDX] at hV
                exact col_col_per_per_c B X C U V hBX hCX (hUBX U hU) hV hPer
              · refine Or.inr (fun hp => ?_)
                obtain ⟨-, -, -, -, hUV⟩ := hp
                exact hPer (hUV B C (col_trivial_3_c B A) (col_trivial_1_c C D))
            · rcases per_dec_c B X D with hPer | hPer
              · refine Or.inl ⟨hAB, hCD, hXAB, hXCD, fun U V hU hV => ?_⟩
                have hVDX : Col V D X := col3_c C D V D X hCD
                  (col_permutation_1_c V C D hV) (col_trivial_2_c C D)
                  (col_permutation_1_c X C D hXCD)
                exact col_col_per_per_c B X D U V hBX hDX (hUBX U hU) hVDX hPer
              · refine Or.inr (fun hp => ?_)
                obtain ⟨-, -, -, -, hUV⟩ := hp
                exact hPer (hUV B D (col_trivial_3_c B A) (col_trivial_3_c D C))
        · refine Or.inr (fun hp => ?_)
          obtain ⟨-, -, -, h4, -⟩ := hp
          exact hXCD h4
      · refine Or.inr (fun hp => ?_)
        obtain ⟨-, -, h3, -⟩ := hp
        exact hXAB h3

theorem perp_distinct_c (A B C D : Tpoint) (h : Perp A B C D) :
    A ≠ B ∧ C ≠ D := by
  obtain ⟨X, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, _⟩ := H5
  exact ⟨((fun H6 => (let H7 := H1 H6; (H7).elim))), ((fun H6 => (let H7 := H3 H6; (H7).elim)))⟩

theorem l8_12_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X C D A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  exact ⟨H2, (⟨H0, (⟨H6, (⟨H4, (fun U V H8 H9 => l8_2_c V X U (H7 V U H9 H8))⟩)⟩)⟩)⟩

theorem per_col_c (A B C D : Tpoint)
    (hBC : B ≠ C) (h₁ : Per A B C) (hCol : Col B C D) : Per A B D := by
  obtain ⟨C', hMidC, hCongC⟩ := h₁
  obtain ⟨hBetCBC', hCgCB⟩ := hMidC
  obtain ⟨D', hBetDBD', hCgBD'⟩ := segment_construction D B D B
  have hCgDB : Cong D B B D' := cong_symmetry_c B D' D B hCgBD'
  have hCgBC : Cong B C B C' := cong_left_commutativity_c C B B C' hCgCB
  have hCgBD : Cong B D B D' := cong_left_commutativity_c D B B D' hCgDB
  have hCgCA : Cong C A C' A := cong_commutativity_c A C A C' hCongC
  refine ⟨D', ⟨hBetDBD', hCgDB⟩, ?_⟩
  rcases hCol with hB | hB | hB
  · have hBet' : Bet B C' D' :=
      l7_15_c B C D B C' D' B (l7_3_2_c B) ⟨hBetCBC', hCgCB⟩ ⟨hBetDBD', hCgDB⟩ hB
    have hCgCD : Cong C D C' D' := l4_3_1_c B C D B C' D' hB hBet' hCgBC hCgBD
    exact cong_commutativity_c D A D' A
      (five_segment_with_def_c B C D A B C' D' A
        ⟨hB, hBet', hCgBC, hCgCD, cong_reflexivity B A, hCgCA⟩ hBC)
  · have hBet' : Bet C' D' B :=
      l7_15_c C D B C' D' B B ⟨hBetCBC', hCgCB⟩ ⟨hBetDBD', hCgDB⟩ (l7_3_2_c B) hB
    have hCgDC : Cong D C D' C' :=
      l4_3_1_c B D C B D' C' (between_symmetry_c C D B hB)
        (between_symmetry_c C' D' B hBet') hCgBD hCgBC
    exact cong_commutativity_c D A D' A
      (l4_2_c B D C A B D' C' A
        ⟨between_symmetry_c C D B hB, between_symmetry_c C' D' B hBet',
         hCgBC, hCgDC, cong_reflexivity B A, hCgCA⟩)
  · have hBet' : Bet D' B C' :=
      l7_15_c D B C D' B C' B ⟨hBetDBD', hCgDB⟩ (l7_3_2_c B) ⟨hBetCBC', hCgCB⟩ hB
    have hCgCBc : Cong C B C' B := cong_commutativity_c B C B C' hCgBC
    have hCgCD : Cong C D C' D' :=
      l2_11_c C B D C' B D' (between_symmetry_c D B C hB)
        (between_symmetry_c D' B C' hBet') hCgCBc hCgBD
    exact cong_commutativity_c D A D' A
      (five_segment_with_def_c C B D A C' B D' A
        ⟨between_symmetry_c D B C hB, between_symmetry_c D' B C' hBet',
         hCgCBc, hCgBD, hCgCA, cong_reflexivity B A⟩ (Ne.symm hBC))

theorem l8_13_2_c (A B C D X : Tpoint)
    (hAB : A ≠ B) (hCD : C ≠ D) (hCol1 : Col X A B) (hCol2 : Col X C D)
    (h : ∃ U V : Tpoint, Col U A B ∧ Col V C D ∧ U ≠ X ∧ V ≠ X ∧ Per U X V) :
    Perp_at X A B C D := by
  obtain ⟨U, H4⟩ := h
  obtain ⟨V, H5⟩ := H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := H11
  exact ⟨hAB, (⟨hCD, (⟨hCol1, (⟨hCol2, (fun U0 V0 H14 H15 => (let H16 := l8_2_c U0 X V (l8_3_c U X V U0 H13 H10 (col3_c A B X U U0 hAB (col_permutation_5_c A X B (col_permutation_4_c X A B hCol1)) (col_permutation_5_c A U B (col_permutation_4_c U A B H6)) (col_permutation_5_c A U0 B (col_permutation_4_c U0 A B H14)))); per_col_c U0 X V V0 (Ne.symm H12) (l8_2_c V X U0 H16) (col3_c C D X V V0 hCD (col_permutation_5_c C X D (col_permutation_4_c X C D hCol2)) (col_permutation_5_c C V D (col_permutation_4_c V C D H8)) (col_permutation_5_c C V0 D (col_permutation_4_c V0 C D H15)))))⟩)⟩)⟩)⟩

theorem l8_14_1_c (A B : Tpoint) : ¬ Perp A B A B := by
  intro H
  obtain ⟨X, H0⟩ := H
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  have H6 := H5 A A (col_trivial_1_c A B) (col_trivial_1_c A B)
  have H7 := l8_7_c A A X (l8_2_c X A A (l8_5_c X A)) H6
  have H8 := H5 B B (col_trivial_3_c B A) (col_trivial_3_c B A)
  have H9 := l8_7_c B B X (l8_2_c X B B (l8_5_c X B)) H8
  exact H2 (Eq.trans H7 (Eq.symm H9))

theorem l8_14_2_1a_c (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    Perp A B C D :=
  ⟨X, h⟩

theorem perp_in_distinct_c (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    A ≠ B ∧ C ≠ D :=
  (let H0 := l8_14_2_1a_c X A B C D h; perp_distinct_c A B C D H0)

theorem l8_14_2_1b_c (X A B C D Y : Tpoint)
    (h₁ : Perp_at X A B C D) (h₂ : Col Y A B) (h₃ : Col Y C D) : X = Y := by
  obtain ⟨_, H2⟩ := h₁
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  have H6 := H5 Y Y h₂ h₃
  exact Eq.symm (l8_8_c Y X H6)

theorem l8_14_2_1b_bis_c (A B C D X : Tpoint)
    (h₁ : Perp A B C D) (h₂ : Col X A B) (h₃ : Col X C D) :
    Perp_at X A B C D := by
  obtain ⟨Y, H2⟩ := h₁
  have H3 := (let H3 := l8_14_2_1b_c Y A B C D X H2 h₂ h₃; H3)
  subst H3
  exact H2

theorem l8_14_2_2_c (X A B C D : Tpoint)
    (h₁ : Perp A B C D)
    (h₂ : ∀ Y, Col Y A B → Col Y C D → X = Y) : Perp_at X A B C D := by
  apply l8_14_2_1b_bis_c
  · exact h₁
  · obtain ⟨Y, hY⟩ := h₁
    obtain ⟨_, _, hColYAB, hColYCD, _⟩ := hY
    have hEq : X = Y := h₂ Y hColYAB hColYCD
    rw [hEq]
    exact hColYAB
  · obtain ⟨Y, hY⟩ := h₁
    obtain ⟨_, _, hColYAB, hColYCD, _⟩ := hY
    have hEq : X = Y := h₂ Y hColYAB hColYCD
    rw [hEq]
    exact hColYCD

theorem l8_14_3_c (A B C D X Y : Tpoint)
    (h₁ : Perp_at X A B C D) (h₂ : Perp_at Y A B C D) : X = Y := by
  apply l8_14_2_1b_c X A B C D Y h₁
  · obtain ⟨_, _, hColY, _, _⟩ := h₂
    exact hColY
  · have h₃ := l8_12_c A B C D Y h₂
    obtain ⟨_, _, hColY', _, _⟩ := h₃
    exact hColY'

theorem l8_15_1_c (A B C X : Tpoint) (hCol : Col A B X) (h : Perp A B C X) :
    Perp_at X A B C X :=
  l8_14_2_1b_bis_c A B C X X h (col_permutation_5_c X B A (col_permutation_3_c A B X hCol)) (col_trivial_3_c X C)

theorem l8_15_2_c (A B C X : Tpoint) (hCol : Col A B X) (h : Perp_at X A B C X) :
    Perp A B C X :=
  l8_14_2_1a_c X A B C X h

theorem perp_in_per_c (A B C : Tpoint) (h : Perp_at B A B B C) : Per A B C := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  exact H3 A C (col_trivial_1_c A B) (col_trivial_3_c C B)

theorem perp_sym_c (A B C D : Tpoint) (h : Perp A B C D) : Perp C D A B := by
  obtain ⟨X, H0⟩ := h
  exact ⟨X, (l8_12_c A B C D X H0)⟩

theorem perp_col0_c (A B C D X Y : Tpoint)
    (h₁ : Perp A B C D) (hXY : X ≠ Y) (hX : Col A B X) (hY : Col A B Y) :
    Perp C D X Y := by
  obtain ⟨X0, hAB, hCD, hX0AB, hX0CD, hPerp⟩ := h₁
  refine ⟨X0, hCD, hXY, hX0CD, ?_, ?_⟩
  · exact col3_c A B X0 X Y hAB (col_permutation_5_c A X0 B (col_permutation_4_c X0 A B hX0AB)) hX hY
  · intro U V hUCD hVXY
    apply l8_2_c
    apply hPerp
    · have H14 : Col A X Y := col3_c A B A X Y hAB (col_trivial_3_c A B) hX hY
      have H15 : Col B X Y := col3_c A B B X Y hAB (col_trivial_2_c A B) hX hY
      exact col3_c X Y V A B hXY (col_permutation_5_c X V Y (col_permutation_4_c V X Y hVXY)) (col_permutation_5_c X A Y (col_permutation_4_c A X Y H14)) (col_permutation_5_c X B Y (col_permutation_4_c B X Y H15))
    · exact hUCD

theorem per_perp_in_c (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp_at B A B B C :=
  ⟨hAB, (⟨hBC, (⟨(col_trivial_3_c B A), (⟨(col_trivial_1_c B C), (fun U V H2 H3 => per_col_c U B C V hBC (l8_2_c C B U (per_col_c C B A U ((fun H4 => hAB (Eq.symm H4))) (l8_2_c A B C h) (col_permutation_5_c B U A (col_permutation_2_c U A B H2)))) (col_permutation_5_c B V C (col_permutation_4_c V B C H3)))⟩)⟩)⟩)⟩

theorem per_perp_c (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp A B B C :=
  (let H2 := per_perp_in_c A B C hAB hBC h; l8_14_2_1a_c B A B B C H2)

theorem perp_left_comm_c (A B C D : Tpoint) (h : Perp A B C D) :
    Perp B A C D := by
  unfold Perp at *
  obtain ⟨X, H0⟩ := h
  exists X
  unfold Perp_at at *
  obtain ⟨H1, H3, H5, H7, H8⟩ := H0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => H1 h.symm
  · exact H3
  · exact col_permutation_5_c X A B H5
  · exact H7
  · intro U V H9 H10
    exact H8 U V (col_permutation_5_c U B A H9) H10

theorem perp_right_comm_c (A B C D : Tpoint) (h : Perp A B C D) :
    Perp A B D C := by
  unfold Perp at *
  obtain ⟨X, H0⟩ := h
  exists X
  unfold Perp_at at *
  obtain ⟨H1, H3, H5, H7, H8⟩ := H0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact H1
  · intro heq
    exact H3 heq.symm
  · exact H5
  · exact col_permutation_5_c X C D H7
  · intro U V H9 H10
    exact H8 U V H9 (col_permutation_5_c V D C H10)

theorem perp_comm_c (A B C D : Tpoint) (h : Perp A B C D) : Perp B A D C :=
  perp_left_comm_c A B D C (perp_right_comm_c A B C D h)

theorem perp_in_sym_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X C D A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  exact ⟨H2, (⟨H0, (⟨H6, (⟨H4, (fun U V H8 H9 => l8_2_c V X U (H7 V U H9 H8))⟩)⟩)⟩)⟩

theorem perp_in_left_comm_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X B A C D := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  exact ⟨((fun H8 => H0 (Eq.symm H8))), (⟨((fun H8 => (let H9 := H2 H8; (H9).elim))), (⟨(col_permutation_5_c X A B H4), (⟨H6, (fun U V H8 H9 => H7 U V (col_permutation_5_c U B A H8) H9)⟩)⟩)⟩)⟩

theorem perp_in_right_comm_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X A B D C :=
  perp_in_sym_c D C A B X (perp_in_left_comm_c C D A B X (perp_in_sym_c A B C D X h))

theorem perp_in_comm_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X B A D C :=
  perp_in_left_comm_c A B D C X (perp_in_right_comm_c A B C D X h)

theorem Perp_cases_c (A B C D : Tpoint)
    (h : Perp A B C D ∨ Perp B A C D ∨ Perp A B D C ∨ Perp B A D C ∨
         Perp C D A B ∨ Perp C D B A ∨ Perp D C A B ∨ Perp D C B A) :
    Perp A B C D := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_comm_c B A D C (perp_right_comm_c B A C D H2)))
    · rcases H2 with H3 | H3
      · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_comm_c B A D C (perp_left_comm_c A B D C H3)))
      · rcases H3 with H4 | H4
        · exact perp_comm_c B A D C H4
        · rcases H4 with H5 | H5
          · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_sym_c C D A B H5))
          · rcases H5 with H6 | H6
            · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_left_comm_c B A C D (perp_sym_c C D B A H6)))
            · rcases H6 with H7 | H7
              · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_right_comm_c A B D C (perp_sym_c D C A B H7)))
              · exact perp_comm_c B A D C (perp_comm_c A B C D (perp_comm_c B A D C (perp_sym_c D C B A H7)))

theorem Perp_perm_c (A B C D : Tpoint) (h : Perp A B C D) :
    Perp A B C D ∧ Perp B A C D ∧ Perp A B D C ∧ Perp B A D C ∧
    Perp C D A B ∧ Perp C D B A ∧ Perp D C A B ∧ Perp D C B A :=
  ⟨h, (⟨(perp_comm_c A B D C (perp_comm_c B A C D (perp_comm_c A B D C (perp_right_comm_c A B C D h)))), (⟨(perp_comm_c B A C D (perp_comm_c A B D C (perp_comm_c B A C D (perp_left_comm_c A B C D h)))), (⟨(perp_comm_c A B C D h), (⟨(perp_comm_c D C B A (perp_comm_c C D A B (perp_sym_c A B C D h))), (⟨(perp_comm_c D C A B (perp_comm_c C D B A (perp_right_comm_c C D A B (perp_sym_c A B C D h)))), (⟨(perp_comm_c C D B A (perp_comm_c D C A B (perp_left_comm_c C D A B (perp_sym_c A B C D h)))), (perp_comm_c C D A B (perp_comm_c D C B A (perp_comm_c C D A B (perp_sym_c A B C D h))))⟩)⟩)⟩)⟩)⟩)⟩)⟩

theorem Perp_in_cases_c (X A B C D : Tpoint)
    (h : Perp_at X A B C D ∨ Perp_at X B A C D ∨ Perp_at X A B D C ∨
         Perp_at X B A D C ∨ Perp_at X C D A B ∨ Perp_at X C D B A ∨
         Perp_at X D C A B ∨ Perp_at X D C B A) : Perp_at X A B C D := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_comm_c B A D C X (perp_in_right_comm_c B A C D X H2)))
    · rcases H2 with H3 | H3
      · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_comm_c B A D C X (perp_in_left_comm_c A B D C X H3)))
      · rcases H3 with H4 | H4
        · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_comm_c B A D C X H4))
        · rcases H4 with H5 | H5
          · exact perp_in_sym_c C D A B X H5
          · rcases H5 with H6 | H6
            · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_sym_c C D A B X (perp_in_right_comm_c C D B A X H6)))
            · rcases H6 with H7 | H7
              · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_sym_c C D A B X (perp_in_left_comm_c D C A B X H7)))
              · exact perp_in_sym_c C D A B X (perp_in_sym_c A B C D X (perp_in_sym_c C D A B X (perp_in_comm_c D C B A X H7)))

theorem Perp_in_perm_c (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X A B C D ∧ Perp_at X B A C D ∧ Perp_at X A B D C ∧
    Perp_at X B A D C ∧ Perp_at X C D A B ∧ Perp_at X C D B A ∧
    Perp_at X D C A B ∧ Perp_at X D C B A :=
  ⟨h, (⟨(perp_in_sym_c C D B A X (perp_in_sym_c B A C D X (perp_in_comm_c A B D C X (perp_in_right_comm_c A B C D X h)))), (⟨(perp_in_sym_c D C A B X (perp_in_sym_c A B D C X (perp_in_comm_c B A C D X (perp_in_left_comm_c A B C D X h)))), (⟨(perp_in_sym_c D C B A X (perp_in_sym_c B A D C X (perp_in_comm_c A B C D X h))), (⟨(perp_in_sym_c A B C D X h), (⟨(perp_in_sym_c B A C D X (perp_in_comm_c A B D C X (perp_in_right_comm_c A B C D X h))), (⟨(perp_in_sym_c A B D C X (perp_in_right_comm_c A B C D X h)), (perp_in_sym_c B A D C X (perp_in_comm_c A B C D X h))⟩)⟩)⟩)⟩)⟩)⟩)⟩

theorem perp_in_col_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Col A B X ∧ Col C D X := by
  obtain ⟨_, H1⟩ := h
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, _⟩ := H4
  exact ⟨(col_permutation_5_c A X B (col_permutation_5_c A B X (col_permutation_5_c A X B (col_permutation_4_c X A B H3)))), (col_permutation_5_c C X D (col_permutation_5_c C D X (col_permutation_5_c C X D (col_permutation_4_c X C D H5))))⟩

theorem perp_perp_in_c (A B C : Tpoint) (h : Perp A B C A) : Perp_at A A B C A := by
  obtain ⟨X, hAB, hCA, hColXAB, hColXCA, hPer⟩ := h
  exact l8_15_1_c A B C A (col_trivial_3_c A B) ⟨X, hAB, hCA, hColXAB, hColXCA, hPer⟩

theorem perp_per_1_c (A B C : Tpoint) (h : Perp A B C A) : Per B A C := by
  have H0 := perp_perp_in_c A B C h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  exact H4 B C (col_trivial_3_c B A) (col_trivial_1_c C A)

theorem perp_per_2_c (A B C : Tpoint) (h : Perp A B A C) : Per B A C :=
  (let H0 := perp_right_comm_c A B A C h; perp_per_1_c A B C H0)

theorem perp_col_c (A B C D E : Tpoint)
    (hAE : A ≠ E) (h₁ : Perp A B C D) (h₂ : Col A B E) : Perp A E C D :=
  perp_sym_c C D A E (perp_col0_c A B C D A E h₁ hAE (col_trivial_3_c A B) h₂)

theorem perp_col2_c (A B C D X Y : Tpoint)
    (h₁ : Perp A B X Y) (hCD : C ≠ D) (hC : Col A B C) (hD : Col A B D) :
    Perp C D X Y := by
  obtain ⟨hAB, hXY⟩ := perp_distinct_c A B X Y h₁
  rcases eq_dec_points_c A C with hAC | hAC
  · rw [hAC] at h₁ hD
    exact perp_col_c C B X Y D hCD h₁ hD
  · have hACXY : Perp A C X Y := perp_col_c A B X Y C hAC h₁ hC
    have hCAD : Col C A D :=
      col_permutation_4_c A C D (col_transitivity_1_c A B C D hAB hC hD)
    exact perp_col_c C A X Y D hCD (perp_left_comm_c A C X Y hACXY) hCAD

theorem perp_col4_c (A B C D P Q R S : Tpoint)
    (hPQ : P ≠ Q) (hRS : R ≠ S)
    (h₁ : Col A B P) (h₂ : Col A B Q) (h₃ : Col C D R) (h₄ : Col C D S)
    (h : Perp A B C D) : Perp P Q R S :=
  perp_col2_c A B P Q R S (perp_sym_c R S A B (perp_col2_c C D R S A B (perp_sym_c A B C D h) hRS h₃ h₄)) hPQ h₁ h₂

theorem perp_not_eq_1_c (A B C D : Tpoint) (h : Perp A B C D) : A ≠ B := by
  obtain ⟨X, H0⟩ := h
  intro H1
  obtain ⟨H2, H3⟩ := H0
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, _⟩ := H5
  have H6 := H2 H1
  exact (H6).elim

theorem perp_not_eq_2_c (A B C D : Tpoint) (h : Perp A B C D) : C ≠ D :=
  (let H0 := perp_sym_c A B C D h; perp_not_eq_1_c C D A B H0)

theorem diff_per_diff_c (A B P R : Tpoint)
    (hAB : A ≠ B) (h₁ : Cong A P B R) (h₂ : Per B A P) (h₃ : Per A B R) :
    P ≠ R := by
  intro h
  rw [← h] at h₃
  exact hAB (l8_7_c P A B (l8_2_c B A P h₂) (l8_2_c A B P h₃))

theorem per_not_colp_c (A B P R : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBR : B ≠ R)
    (h₁ : Per B A P) (h₂ : Per A B R) : ¬ Col P A R :=
  (fun H4 => (let H5 := perp_comm_c B A A P (per_perp_c B A P (Ne.symm hAB) hAP h₁); (let H6 := per_perp_c A B R hAB hBR h₂; (let H7 := per_col_c B A P R hAP h₁ (col_permutation_5_c A R P (col_permutation_1_c P A R H4)); (let H8 := l8_2_c A B R h₂; (let H9 := l8_2_c B A R H7; (let H10 := l8_7_c R A B H9 H8; ((hAB H10)).elim)))))))

theorem per_not_col_c (A B C : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) : ¬ Col A B C := by
  intro hCol
  obtain ⟨C', hMid, hCong⟩ := h
  obtain ⟨hBetC, hCongC⟩ := hMid
  have hCAC' : Col C A C' :=
    col_transitivity_1_c C B A C' (Ne.symm hBC)
      (col_permutation_3_c A B C hCol) (bet_col_c C B C' hBetC)
  rcases l7_20_c A C C' hCAC' hCong with hCC' | hMidA
  · rw [← hCC'] at hBetC hCongC
    exact hBC (l7_3_c B C ⟨hBetC, hCongC⟩)
  · exact hAB (l7_17_c C C' A B hMidA ⟨hBetC, hCongC⟩)

theorem perp_not_col2_c (A B C D : Tpoint) (h : Perp A B C D) :
    ¬ Col A B C ∨ ¬ Col A B D := by
  have o := col_dec_c A B C
  rcases o with H0 | H0
  · exact Or.inr ((let H1 := l8_14_2_1b_bis_c A B C D C h (col_permutation_5_c C B A (col_permutation_3_c A B C H0)) (col_trivial_1_c C D); (fun H2 => (let H3 := l8_14_2_1b_bis_c A B C D D h (col_permutation_5_c D B A (col_permutation_3_c A B D H2)) (col_trivial_3_c D C); (let H4 := l8_14_3_c A B C D C D H1 H3; (let H5 := perp_not_eq_2_c A B C D h; ((H5 H4)).elim))))))
  · exact Or.inl H0

theorem perp_not_col_c (A B P : Tpoint) (h : Perp A B P A) : ¬ Col A B P := by
  intro hCol
  have hPerp_at : Perp_at A A B P A := perp_perp_in_c A B P h
  have hPer_PAB : Per P A B := perp_in_per_c P A B (perp_in_sym_c A B P A A hPerp_at)
  have hPerp_at' : Perp_at A B A P A := perp_in_left_comm_c A B P A A hPerp_at
  obtain ⟨hAB, hPA⟩ := perp_distinct_c A B P A h
  have hPer_BAP : Per B A P := perp_in_per_c B A P (perp_in_right_comm_c B A P A A hPerp_at')
  have hNotCol : ¬ Col B A P := per_not_col_c B A P hAB.symm hPA.symm hPer_BAP
  exact hNotCol (col_permutation_4_c A B P hCol)

theorem perp_in_col_perp_in_c (A B C D E P : Tpoint)
    (hCE : C ≠ E) (hCol : Col C D E) (h : Perp_at P A B C D) :
    Perp_at P A B C E := by
  obtain ⟨hAB, hCD, hPAB, hPCD, hUV⟩ := h
  refine ⟨hAB, hCE, hPAB, ?_, ?_⟩
  · exact col_permutation_4_c C P E
      (col_transitivity_1_c C D P E hCD (col_permutation_1_c P C D hPCD) hCol)
  · intro U V hU hV
    exact hUV U V hU
      (col_permutation_4_c C V D
        (col_transitivity_1_c C E V D hCE (col_permutation_1_c V C E hV)
          (col_permutation_5_c C D E hCol)))

theorem perp_col2_bis_c (A B C D P Q : Tpoint)
    (h₁ : Perp A B C D) (h₂ : Col C D P) (h₃ : Col C D Q) (hPQ : P ≠ Q) :
    Perp A B P Q :=
  perp_sym_c P Q A B (perp_col2_c C D P Q A B (perp_comm_c D C B A (perp_comm_c C D A B (perp_sym_c A B C D h₁))) hPQ h₂ h₃)

theorem perp_in_perp_bis_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp X B C D ∨ Perp A X C D := by
  obtain ⟨hAB, hCD, hXAB, hXCD, hUV⟩ := h
  rcases eq_dec_points_c X A with hXA | hXA
  · rw [hXA] at hXAB hXCD hUV
    refine Or.inl ?_
    rw [hXA]
    exact ⟨A, hAB, hCD, hXAB, hXCD, hUV⟩
  · refine Or.inr ⟨X, Ne.symm hXA, hCD, col_trivial_3_c X A, hXCD, ?_⟩
    intro U V hU hV
    exact hUV U V
      (col_permutation_4_c A U B
        (col_transitivity_1_c A X U B (Ne.symm hXA)
          (col_permutation_1_c U A X hU)
          (col_permutation_4_c X A B hXAB)))
      hV

theorem col_per_perp_c (A B C D : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hDB : D ≠ B) (hDC : D ≠ C)
    (hCol : Col B C D) (h : Per A B C) : Perp C D A B := by
  have H4 := per_perp_in_c A B C hAB hBC h
  have H5 := perp_in_perp_bis_c A B B C B H4
  rcases H5 with H6 | H6
  · have H7 := perp_distinct_c B B B C H6
    obtain ⟨H8, _⟩ := H7
    exact ((H8 rfl)).elim
  · exact perp_col_c C B A B D (Ne.symm hDC) (perp_sym_c A B C B (perp_right_comm_c A B B C H6)) (col_permutation_4_c B C D hCol)

theorem per_cong_mid_c (A B C H : Tpoint)
    (hBC : B ≠ C) (h₁ : Bet A B C) (h₂ : Cong A H C H) (h₃ : Per H B C) :
    Midpoint B A C := sorry

theorem per_double_cong_c (A B C C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint B C C') : Cong A C A C' := by
  obtain ⟨C'', H1⟩ := h₁
  obtain ⟨H2, H3⟩ := H1
  have H4 := l7_9_c C' C'' B C (l7_2_c B C C' h₂) (l7_2_c B C C'' H2)
  subst H4
  exact H3

theorem cong_perp_or_mid_c (A B M X : Tpoint)
    (hAB : A ≠ B) (hM : Midpoint M A B) (h : Cong A X B X) :
    X = M ∨ ¬ Col A B X ∧ Perp_at M X M A B := by
  rcases col_dec_c A B X with hCol | hNCol
  · left
    have H3 : A = B ∨ Midpoint X A B :=
      l7_20_c X A B (col_permutation_5_c A B X hCol)
        (cong_symmetry_c X B X A (cong_symmetry_c X A X B (cong_commutativity_c A X B X h)))
    rcases H3 with hEq | hMid
    · exact False.elim (hAB hEq)
    · exact l7_17_c A B X M hMid hM
  · right
    refine ⟨hNCol, ?_⟩
    have H3 : Col M A B := by
      obtain ⟨hBet, hCong⟩ := hM
      exact col_permutation_4_c A M B (bet_col_c A M B hBet)
    obtain ⟨_, _, _, hAX⟩ := not_col_distincts_c A B X hNCol
    obtain ⟨hMA, hMB⟩ := midpoint_distinct_1_c M A B hAB hM
    have H12 : Per X M A := ⟨B, hM, cong_symmetry_c X B X A (cong_symmetry_c X A X B (cong_commutativity_c A X B X h))⟩
    have hXM : X ≠ M := by
      intro hEq
      rw [hEq] at hNCol
      exact hNCol (col_permutation_5_c A M B (col_permutation_4_c M A B H3))
    have H13 : Perp_at M X M M A := per_perp_in_c X M A hXM hMA H12
    have H14 : Perp_at M X M A M := perp_in_right_comm_c X M M A M H13
    exact perp_in_col_perp_in_c X M A M B M hAB (col_permutation_5_c A B M (col_permutation_1_c M A B H3)) H14

theorem col_per2_cases_c (A B C D B' : Tpoint)
    (hBC : B ≠ C) (hB'C : B' ≠ C) (hCD : C ≠ D)
    (hCol : Col B C D) (h₁ : Per A B C) (h₂ : Per A B' C) :
    B = B' ∨ ¬ Col B' C D := sorry

theorem l8_16_1_c (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (h : Perp A B C X) :
    ¬ Col A B C ∧ Per C X U := by
  rcases eq_dec_points_c U X with hUX | hUX
  · rw [hUX]
    refine ⟨?_, l8_5_c C X⟩
    rcases perp_not_col2_c A B C X h with hnc | hnc
    · exact hnc
    · exact absurd hX hnc
  · obtain ⟨hAB, -⟩ := perp_distinct_c A B C X h
    refine ⟨?_, ?_⟩
    · intro h4
      have hXU : X = U := l8_14_2_1b_c X A B C X U (l8_15_1_c A B C X hX h)
        (col_permutation_2_c A B U hU)
        (col3_c A B U C X hAB hU h4 hX)
      exact hUX hXU.symm
    · obtain ⟨-, -, -, -, hUV⟩ := l8_14_2_1b_bis_c C X X U X
        (perp_col0_c A B C X X U h (Ne.symm hUX) hX hU)
        (col_trivial_3_c X C) (col_trivial_1_c X U)
      exact hUV C U (col_trivial_1_c C X) (col_trivial_3_c U X)

theorem l8_16_2_c (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (hUX : U ≠ X)
    (hNCol : ¬ Col A B C) (h : Per C X U) : Perp A B C X := by
  have H4 : C ≠ X := fun hCX => by
    subst hCX
    exact hNCol hX
  unfold Perp
  use X
  apply l8_13_2_c
  · exact (not_col_distincts_c A B C hNCol).2.1
  · exact H4
  · exact col_permutation_5_c X B A (col_permutation_3_c A B X hX)
  · exact col_trivial_3_c X C
  · use U, C
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact col_permutation_5_c U B A (col_permutation_3_c A B U hU)
    · exact col_trivial_1_c C X
    · exact hUX
    · exact H4
    · exact l8_2_c C X U h

theorem l8_18_uniqueness_c (A B C X Y : Tpoint)
    (hNCol : ¬ Col A B C)
    (h₁ : Col A B X) (h₂ : Perp A B C X)
    (h₃ : Col A B Y) (h₄ : Perp A B C Y) : X = Y := by
  obtain ⟨-, -, -, -, hUVX⟩ := l8_15_1_c A B C X h₁ h₂
  obtain ⟨-, -, -, -, hUVY⟩ := l8_15_1_c A B C Y h₃ h₄
  exact l8_7_c C X Y
    (l8_2_c Y X C (hUVX Y C (col_permutation_2_c A B Y h₃) (col_trivial_1_c C X)))
    (l8_2_c X Y C (hUVY X C (col_permutation_2_c A B X h₁) (col_trivial_1_c C Y)))

theorem midpoint_distinct_c (A B X C C' : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (h : Midpoint X C C') :
    C ≠ C' := by
  intro e
  obtain ⟨hBet, _⟩ := h
  rw [← e] at hBet
  have hCX := between_identity C X hBet
  apply hNCol
  rw [hCX]
  exact hCol

theorem l8_20_1_c (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C) : Per B A P := by
  obtain ⟨B', hMB'⟩ := symmetric_point_construction_c B A
  obtain ⟨D', hMD'⟩ := symmetric_point_construction_c D A
  obtain ⟨P', hMP'⟩ := symmetric_point_construction_c P A
  rcases eq_dec_points_c A B with hab | hab
  · rw [← hab]
    exact l8_2_c P A A (l8_5_c P A)
  · have hPerB'BC : Per B' B C :=
      l8_3_c A B C B' h₁ hab (bet_col_c B A B' (midpoint_bet_c B A B' hMB'))
    have hPerBB'C' : Per B B' C' :=
      l8_10_c B' B C B B' C' hPerB'BC
        ⟨cong_pseudo_reflexivity B' B,
         l7_13_c A B' C B C' hMB' h₃,
         l7_13_c A B C B' C' (l7_2_c A B B' hMB') h₃⟩
    have hMB'D'C' : Midpoint B' D' C' :=
      symmetry_preserves_midpoint_c D B C D' B' C' A hMD' hMB' (l7_2_c A C' C h₃) h₄
    have hMP'CD' : Midpoint P' C D' :=
      symmetry_preserves_midpoint_c C' P D C P' D' A h₃ hMP' hMD' h₂
    obtain ⟨D₁, hMD₁, hCg₁⟩ := hPerBB'C'
    have hD'D₁ : D' = D₁ :=
      symmetric_point_uniqueness_c C' B' D' D₁ (l7_2_c B' D' C' hMB'D'C') hMD₁
    rw [← hD'D₁] at hCg₁
    have hCgPDP'D' : Cong P D P' D' :=
      l7_13_c A P D P' D' (l7_2_c A P P' hMP') (l7_2_c A D D' hMD')
    have hCgC'DCD' : Cong C' D C D' :=
      l7_13_c A C' D C D' (l7_2_c A C' C h₃) (l7_2_c A D D' hMD')
    obtain ⟨hBetCP'D', hCgCP'P'D'⟩ := hMP'CD'
    have hCgPDP'C : Cong P D P' C :=
      cong_transitivity_c P D P' D' P' C hCgPDP'D'
        (cong_right_commutativity_c P' D' C P' (cong_symmetry_c C P' P' D' hCgCP'P'D'))
    obtain ⟨hBetDBC, hCgDBBC⟩ := h₄
    have hIFSC : IFSC C' P D B D' P' C B :=
      ⟨midpoint_bet_c C' P D h₂,
       midpoint_bet_c D' P' C (l7_2_c P' C D' ⟨hBetCP'D', hCgCP'P'D'⟩),
       cong_right_commutativity_c C' D C D' hCgC'DCD',
       hCgPDP'C,
       cong_commutativity_c B C' B D' hCg₁,
       cong_right_commutativity_c D B B C hCgDBBC⟩
    have hCgPBP'B : Cong P B P' B := l4_2_c C' P D B D' P' C B hIFSC
    exact ⟨P', hMP', cong_commutativity_c P B P' B hCgPBP'B⟩

theorem l8_20_2_c (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C)
    (hBC : B ≠ C) : A ≠ P := by
  intro H4
  subst H4
  have H6 := symmetric_point_uniqueness_c C' A C D h₃ h₂
  subst H6
  have H9 := l7_3_c B C h₄
  subst H9
  exact ((hBC rfl)).elim

theorem perp_col1_c (A B C D X : Tpoint)
    (hCX : C ≠ X) (h₁ : Perp A B C D) (h₂ : Col C D X) : Perp A B C X := by
  obtain ⟨hAB, hCD⟩ := perp_distinct_c A B C D h₁
  obtain ⟨P, hPerp⟩ := h₁
  obtain ⟨h4, h5, h7, h9, h10⟩ := hPerp
  refine ⟨P, ?_⟩
  refine ⟨h4, ?_, ?_, ?_, ?_⟩
  · exact hCX
  · exact h7
  · exact col_permutation_2_c C X P (col_transitivity_2_c D C X P (fun h => hCD h.symm) (col_permutation_4_c C D X h₂) (col_permutation_3_c P C D h9))
  · intro U V hU hV
    exact h10 U V hU (col_permutation_2_c C D V (col_transitivity_1_c C X D V hCX (col_permutation_5_c C D X h₂) (col_permutation_1_c V C X hV)))

theorem l8_18_existence_c (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ X, Col A B X ∧ Perp A B C X := by
  obtain ⟨-, hAB, -, -⟩ := not_col_distincts_c A B C hNCol
  obtain ⟨Y, hBetBAY, hCgAY⟩ := segment_construction B A A C
  obtain ⟨P, hMP⟩ := l7_25_c C Y A (cong_symmetry_c A Y A C hCgAY)
  have hPerAPY : Per A P Y := ⟨C, l7_2_c P C Y hMP, hCgAY⟩
  obtain ⟨Z, hBetAYZ, hCgYZ⟩ := segment_construction A Y Y P
  obtain ⟨Q, hBetPYQ, hCgYQ⟩ := segment_construction P Y Y A
  obtain ⟨Q', hBetQZQ', hCgZQ'⟩ := segment_construction Q Z Q Z
  have hMZQ : Midpoint Z Q Q' := ⟨hBetQZQ', cong_symmetry_c Z Q' Q Z hCgZQ'⟩
  obtain ⟨C', hBetQ'YC', hCgYC'⟩ := segment_construction Q' Y Y C
  obtain ⟨X, hMX⟩ := l7_25_c C C' Y (cong_symmetry_c Y C' Y C hCgYC')
  have hAY : A ≠ Y := by
    intro hay
    rw [← hay] at hCgAY
    have hAC' : A = C := cong_reverse_identity_c A A C hCgAY
    exact hNCol (by rw [← hAC']; exact col_trivial_3_c A B)
  have hCgAYQY : Cong A Y Q Y :=
    cong_right_commutativity_c A Y Y Q
      (cong_left_commutativity_c Y A Y Q (cong_symmetry_c Y Q Y A hCgYQ))
  have hOFSC : OFSC A Y Z Q Q Y P A :=
    ⟨hBetAYZ, between_symmetry_c P Y Q hBetPYQ, hCgAYQY, hCgYZ,
     cong_pseudo_reflexivity A Q, hCgYQ⟩
  have hCgZQPA : Cong Z Q P A := five_segment_with_def_c A Y Z Q Q Y P A hOFSC hAY
  have hC3 : Cong_3 A P Y Q Z Y :=
    ⟨cong_commutativity_c P A Z Q (cong_symmetry_c Z Q P A hCgZQPA),
     hCgAYQY,
     cong_commutativity_c Y P Y Z (cong_symmetry_c Y Z Y P hCgYZ)⟩
  have hPerYZQ : Per Y Z Q := l8_2_c Q Z Y (l8_10_c A P Y Q Z Y hPerAPY hC3)
  have hPY : P ≠ Y := by
    intro hpy
    rw [hpy] at hMP
    obtain ⟨-, hc⟩ := hMP
    have hCY' : C = Y := cong_identity C Y Y hc
    rw [← hCY'] at hBetBAY
    exact hNCol (col_permutation_4_c B A C (bet_col_c B A C hBetBAY))
  obtain ⟨Q'', hMZQ'', hCgYQQ''⟩ := hPerYZQ
  have hQ'Q'' : Q' = Q'' := symmetric_point_uniqueness_c Q Z Q' Q'' hMZQ hMZQ''
  rw [← hQ'Q''] at hCgYQQ''
  have hBetQYC : Bet Q Y C := outer_transitivity_between_c Q Y P C
    (between_symmetry_c P Y Q hBetPYQ)
    (between_symmetry_c C P Y (midpoint_bet_c C P Y hMP)) (Ne.symm hPY)
  have hy : Bet Z Y X := l7_22_c Q C Q' C' Y Z X hBetQYC hBetQ'YC'
    hCgYQQ'' (cong_symmetry_c Y C' Y C hCgYC') hMZQ hMX
  have hQY : Q ≠ Y := by
    intro hqy
    rw [hqy] at hCgYQ
    exact hAY (cong_reverse_identity_c Y Y A hCgYQ).symm
  have hPerYXC : Per Y X C := ⟨C', hMX, cong_symmetry_c Y C' Y C hCgYC'⟩
  have hColABY : Col A B Y :=
    col_permutation_5_c A Y B (col_permutation_1_c B A Y (bet_col_c B A Y hBetBAY))
  have hColABZ : Col A B Z :=
    col_transitivity_1_c A Y B Z hAY
      (col_permutation_5_c A B Y hColABY) (bet_col_c A Y Z hBetAYZ)
  have hYZ : Y ≠ Z := by
    intro hyz
    rw [← hyz] at hCgYZ
    exact hPY (cong_reverse_identity_c Y Y P hCgYZ).symm
  have gYZA : Col Y Z A := col3_c A B Y Z A hAB hColABY hColABZ (col_trivial_3_c A B)
  have gYZB : Col Y Z B := col3_c A B Y Z B hAB hColABY hColABZ (col_trivial_2_c A B)
  have hColABX : Col A B X :=
    col_permutation_1_c X A B
      (col3_c Y Z X A B hYZ
        (col_permutation_4_c Z Y X (bet_col_c Z Y X hy)) gYZA gYZB)
  have hCY : C ≠ Y := by
    intro hcy
    rw [← hcy] at hBetBAY
    exact hNCol (col_permutation_4_c B A C (bet_col_c B A C hBetBAY))
  have hYC : Y ≠ C := Ne.symm hCY
  have hQQ' : Q ≠ Q' := by
    intro hqq
    rw [← hqq] at hMZQ
    have hZQ : Z = Q := l7_3_c Z Q hMZQ
    have hColABQ : Col A B Q := by rw [← hZQ]; exact hColABZ
    exact hNCol (col3_c Q Y A B C hQY
      (col3_c A B Q Y A hAB hColABQ hColABY (col_trivial_3_c A B))
      (col3_c A B Q Y B hAB hColABQ hColABY (col_trivial_2_c A B))
      (bet_col_c Q Y C hBetQYC))
  obtain ⟨hBetCXC', hCgCXXC'⟩ := hMX
  have hColQQ'Z : Col Q Q' Z := col_permutation_5_c Q Z Q' (bet_col_c Q Z Q' hBetQZQ')
  have hZYC_of : Col Y C Q → Col Y C Q' → Col Y Z C := fun d1 d2 =>
    col3_c Q Q' Y Z C hQQ'
      (col3_c Y C Q Q' Y hYC d1 d2 (col_trivial_3_c Y C))
      hColQQ'Z
      (col3_c Y C Q Q' C hYC d1 d2 (col_trivial_2_c Y C))
  have hEnd : Col Y Z C → False := fun hyzc =>
    hNCol (col3_c Y Z A B C hYZ gYZA gYZB hyzc)
  have hColYCQ : Col Y C Q := col_permutation_1_c Q Y C (bet_col_c Q Y C hBetQYC)
  have hCC' : C ≠ C' := by
    intro hcc
    rw [← hcc] at hBetQ'YC'
    exact hEnd (hZYC_of hColYCQ (col_permutation_1_c Q' Y C (bet_col_c Q' Y C hBetQ'YC')))
  have hCX : C ≠ X := by
    intro hcx
    rw [← hcx] at hCgCXXC'
    exact hCC' (cong_reverse_identity_c C C C' hCgCXXC')
  have hXY : X ≠ Y := by
    intro hxy
    rw [hxy] at hBetCXC'
    have hC'Y : C' ≠ Y := by
      intro hc'y
      rw [hc'y] at hCgYC'
      exact hYC (cong_reverse_identity_c Y Y C hCgYC')
    have d2 : Col Y C Q' := col_permutation_5_c Y Q' C
      (col_transitivity_1_c Y C' Q' C (Ne.symm hC'Y)
        (col_permutation_1_c Q' Y C' (bet_col_c Q' Y C' hBetQ'YC'))
        (col_permutation_1_c C Y C' (bet_col_c C Y C' hBetCXC')))
    exact hEnd (hZYC_of hColYCQ d2)
  obtain ⟨-, -, -, -, hUV⟩ := l8_13_2_c Y Z C X X hYZ hCX
    (col_permutation_3_c Z Y X (bet_col_c Z Y X hy))
    (col_trivial_3_c X C)
    ⟨Y, C, col_trivial_1_c Y Z, col_trivial_1_c C X, Ne.symm hXY, hCX, hPerYXC⟩
  exact ⟨X, hColABX,
    ⟨X, hAB, hCX, col_permutation_2_c A B X hColABX, col_trivial_3_c X C,
     fun U V hU hV => hUV U V
       (col_permutation_2_c Y Z U
         (col3_c A B Y Z U hAB hColABY hColABZ (col_permutation_1_c U A B hU)))
       hV⟩⟩

theorem l8_21_aux_c (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := by
  obtain ⟨-, hAB, -, -⟩ := not_col_distincts_c A B C hNCol
  obtain ⟨X, hColABX, hPerpABCX⟩ := l8_18_existence_c A B C hNCol
  obtain ⟨-, -, -, -, hUV⟩ := l8_15_1_c A B C X hColABX hPerpABCX
  have hPerAXC : Per A X C := hUV A C (col_trivial_1_c A B) (col_trivial_1_c C X)
  obtain ⟨C', hMXCC', hCgACAC'⟩ := hPerAXC
  obtain ⟨C'', hMC''⟩ := symmetric_point_construction_c C A
  obtain ⟨hBetCAC'', hCgCAAC''⟩ := hMC''
  have hCgAC'AC'' : Cong A C' A C'' :=
    cong_transitivity_c A C' A C A C'' (cong_symmetry_c A C A C' hCgACAC')
      (cong_left_commutativity_c C A A C'' hCgCAAC'')
  obtain ⟨P, hMP⟩ := l7_25_c C' C'' A hCgAC'AC''
  have hXC : X ≠ C := by
    intro h
    rw [h] at hColABX
    exact hNCol hColABX
  have hPerXAP : Per X A P :=
    l8_20_1_c A X C C'' C' P
      (⟨C', hMXCC', hCgACAC'⟩)
      (l7_2_c P C' C'' hMP)
      (l7_2_c A C C'' ⟨hBetCAC'', hCgCAAC''⟩)
      (l7_2_c X C C' hMXCC')
  have hAP : A ≠ P :=
    l8_20_2_c A X C C'' C' P
      (⟨C', hMXCC', hCgACAC'⟩)
      (l7_2_c P C' C'' hMP)
      (l7_2_c A C C'' ⟨hBetCAC'', hCgCAAC''⟩)
      (l7_2_c X C C' hMXCC')
      hXC
  obtain ⟨T, hBetPTC, hBetATX⟩ := l3_17_c C'' A C C' X P
    (midpoint_bet_c C'' A C (l7_2_c A C C'' ⟨hBetCAC'', hCgCAAC''⟩))
    (midpoint_bet_c C' X C (l7_2_c X C C' hMXCC'))
    (midpoint_bet_c C'' P C' (l7_2_c P C' C'' hMP))
  rcases eq_dec_points_c A X with hax | hax
  · have hMACC' : Midpoint A C C' := by rw [hax]; exact hMXCC'
    have hC'A : C' ≠ A := by
      intro h
      rw [h] at hMACC'
      obtain ⟨-, hc⟩ := hMACC'
      exact hXC (by rw [← hax]; exact (cong_identity C A A hc).symm)
    have hPerpABCA : Perp A B C A := by rw [← hax] at hPerpABCX; exact hPerpABCX
    have hPerp' : Perp A B C' A :=
      perp_col0_c C A A B C' A (perp_sym_c A B C A hPerpABCA)
        hC'A (bet_col_c C A C' (midpoint_bet_c C A C' hMACC')) (col_trivial_2_c C A)
    exact ⟨C', A, hPerp', col_trivial_3_c A B,
      midpoint_bet_c C A C' hMACC'⟩
  · refine ⟨P, T, ⟨A, hAB, Ne.symm hAP, col_trivial_1_c A B, col_trivial_3_c A P, ?_⟩,
      col_permutation_5_c A T B
        (col_transitivity_1_c A X T B hax
          (col_permutation_5_c A T X (bet_col_c A T X hBetATX))
          (col_permutation_5_c A B X hColABX)),
      between_symmetry_c P T C hBetPTC⟩
    intro U V hU hV
    have hPerXAV : Per X A V :=
      per_col_c X A P V hAP hPerXAP (col_permutation_3_c V P A hV)
    have hPerVAU : Per V A U :=
      per_col_c V A X U hax (l8_2_c X A V hPerXAV)
        (col3_c A B A X U hAB (col_trivial_3_c A B) hColABX
          (col_permutation_1_c U A B hU))
    exact l8_2_c V A U hPerVAU

theorem l8_21_c (A B C : Tpoint) (hAB : A ≠ B) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := by
  have o := col_dec_c A B C
  rcases o with H0 | H0
  · have H1 := not_col_exists_c A B hAB
    obtain ⟨C', H2⟩ := H1
    have H3 := l8_21_aux_c A B C' H2
    obtain ⟨P, H4⟩ := H3
    obtain ⟨T, H5⟩ := H4
    obtain ⟨H6, H7⟩ := H5
    obtain ⟨_, _⟩ := H7
    exact ⟨P, (⟨C, (⟨H6, (⟨H0, (between_trivial2 C P)⟩)⟩)⟩)⟩
  · exact l8_21_aux_c A B C H0

theorem per_cong_c (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Per B A P) (h₂ : Per A B R) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) : Cong A R P B := by
  have hPerPAB : Per P A B := l8_2_c B A P h₁
  have hBR : B ≠ R := by
    intro hbr
    rw [← hbr] at h₃
    exact hAP (cong_identity A P B h₃)
  have hPerPAX : Per P A X := per_col_c P A B X hAB hPerPAB hCol
  have hPerRBX : Per R B X :=
    per_col_c R B A X (Ne.symm hAB) (l8_2_c A B R h₂) (col_permutation_4_c A B X hCol)
  have hXA : X ≠ A := by
    intro hxa
    rw [hxa] at hBet
    exact per_not_colp_c A B P R hAB hAP hBR h₁ h₂ (bet_col_c P A R hBet)
  obtain ⟨P', hMPP'⟩ := symmetric_point_construction_c P A
  obtain ⟨R', hBetP'XR', hCgXR'XR⟩ := segment_construction P' X X R
  obtain ⟨M, hMRR'⟩ := l7_25_c R R' X (cong_symmetry_c X R' X R hCgXR'XR)
  have hPerXMR : Per X M R := ⟨R', hMRR', cong_symmetry_c X R' X R hCgXR'XR⟩
  have hCgXPXP' : Cong X P X P' := by
    obtain ⟨P'', hMP'', hCg''⟩ := l8_2_c P A X hPerPAX
    have hpp : P' = P'' := symmetric_point_uniqueness_c P A P' P'' hMPP' hMP''
    rw [← hpp] at hCg''
    exact hCg''
  have hPP' : P ≠ P' := by
    intro hpp
    rw [← hpp] at hMPP'
    exact hAP (l7_3_c A P hMPP')
  have hNColXPP' : ¬ Col X P P' := by
    intro hcol
    have hColPAX : Col P A X :=
      col3_c P P' P A X hPP' (col_trivial_3_c P P')
        (col_permutation_5_c P A P' (bet_col_c P A P' (midpoint_bet_c P A P' hMPP')))
        (col_permutation_1_c X P P' hcol)
    rcases l8_9_c P A X hPerPAX hColPAX with hpa | hxa'
    · exact hAP hpa.symm
    · exact hXA hxa'
  have hBetAXM : Bet A X M := l7_22_c P R P' R' X A M hBet hBetP'XR'
    hCgXPXP' (cong_symmetry_c X R' X R hCgXR'XR) hMPP' hMRR'
  have hXR : X ≠ R := by
    intro hxr
    rw [← hxr] at hPerRBX
    exact hBR ((l8_8_c X B hPerRBX).symm.trans hxr)
  have hXR' : X ≠ R' := by
    intro hxr'
    rw [← hxr'] at hCgXR'XR
    exact hXR (cong_reverse_identity_c X X R hCgXR'XR)
  have hColXRP : Col X R P := col_permutation_1_c P X R (bet_col_c P X R hBet)
  have hMX : M ≠ X := by
    intro hmx
    rw [hmx] at hMRR'
    have hColXRR' : Col X R R' :=
      col_permutation_4_c R X R' (bet_col_c R X R' (midpoint_bet_c R X R' hMRR'))
    have hColXPR' : Col X P R' :=
      col_transitivity_1_c X R P R' hXR hColXRP hColXRR'
    exact hNColXPP' (col_transitivity_1_c X R' P P' hXR'
      (col_permutation_5_c X P R' hColXPR')
      (col_permutation_1_c P' X R' (bet_col_c P' X R' hBetP'XR')))
  have hMR : M ≠ R := by
    intro hmr
    rw [hmr] at hMRR'
    obtain ⟨-, hcg⟩ := hMRR'
    have hRR' : R = R' := cong_reverse_identity_c R R R' hcg
    rw [← hRR'] at hBetP'XR'
    exact hNColXPP' (col_transitivity_1_c X R P P' hXR hColXRP
      (col_permutation_1_c P' X R (bet_col_c P' X R hBetP'XR')))
  have hNColAXR : ¬ Col A X R := by
    intro hcol
    have hColABR : Col A B R :=
      col3_c A X A B R (Ne.symm hXA) (col_trivial_3_c A X)
        (col_permutation_5_c A B X hCol) hcol
    exact per_not_col_c A B R hAB hBR h₂ hColABR
  have hPerpAXRM : Perp A X R M :=
    perp_right_comm_c A X M R
      (perp_col2_c X M A X M R (per_perp_c X M R (Ne.symm hMX) hMR hPerXMR)
        (Ne.symm hXA)
        (col_permutation_1_c A X M (bet_col_c A X M hBetAXM))
        (col_trivial_3_c X M))
  have hPerpAXRB : Perp A X R B :=
    perp_right_comm_c A X B R
      (perp_col2_c A B A X B R (per_perp_c A B R hAB hBR h₂)
        (Ne.symm hXA) (col_trivial_3_c A B) hCol)
  have hMB : M = B := l8_18_uniqueness_c A X R M B hNColAXR
    (bet_col_c A X M hBetAXM) hPerpAXRM
    (col_permutation_5_c A B X hCol) hPerpAXRB
  rw [hMB] at hMRR'
  have hPX : P ≠ X := by
    intro hpx
    rw [← hpx] at hNColXPP'
    exact hNColXPP' (col_trivial_1_c P P')
  have hOFSC : OFSC P X R P' P' X R' P :=
    ⟨hBet, hBetP'XR', cong_commutativity_c X P X P' hCgXPXP',
     cong_symmetry_c X R' X R hCgXR'XR,
     cong_pseudo_reflexivity P P', cong_symmetry_c X P X P' hCgXPXP'⟩
  have hCgRP'R'P : Cong R P' R' P :=
    five_segment_with_def_c P X R P' P' X R' P hOFSC hPX
  obtain ⟨hBetP'AP, hCgP'AAP⟩ := l7_2_c A P P' hMPP'
  obtain ⟨hBetRBR', hCgRBBR'⟩ := hMRR'
  have hCgP'AR'B : Cong P' A R' B :=
    cong_transitivity_c P' A B R R' B
      (cong_transitivity_c P' A A P B R hCgP'AAP h₃)
      (cong_commutativity_c R B B R' hCgRBBR')
  have hIFSC : IFSC P' A P R R' B R P :=
    ⟨hBetP'AP, between_symmetry_c R B R' hBetRBR',
     l2_11_c P' A P R' B R hBetP'AP (between_symmetry_c R B R' hBetRBR')
       hCgP'AR'B h₃,
     h₃,
     cong_left_commutativity_c R P' R' P hCgRP'R'P,
     cong_pseudo_reflexivity P R⟩
  exact cong_right_commutativity_c A R B P (l4_2_c P' A P R R' B R P hIFSC)

theorem perp_cong_c (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Perp A B P A) (h₂ : Perp A B R B) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) : Cong A R P B :=
  per_cong_c A B P R X hAB hAP (perp_per_1_c A B P h₁) (perp_per_1_c B A R (perp_left_comm_c A B R B h₂)) h₃ hCol hBet

theorem perp_exists_c (O A B : Tpoint) (hAB : A ≠ B) : ∃ X, Perp O X A B := sorry

theorem perp_vector_c (A B : Tpoint) (hAB : A ≠ B) : ∃ X Y, Perp A B X Y := sorry

theorem midpoint_existence_aux_c (A B P Q T : Tpoint)
    (hAB : A ≠ B)
    (h₁ : Perp A B Q B) (h₂ : Perp A B P A)
    (h₃ : Col A B T) (h₄ : Bet Q T P) (h₅ : Le A P B Q) :
    ∃ X : Tpoint, Midpoint X A B := by
  obtain ⟨R, hBetBRQ, hCgAPBR⟩ := h₅
  obtain ⟨X, hBetTXB, hBetRXP⟩ :=
    inner_pasch P B Q T R (between_symmetry_c Q T P h₄) hBetBRQ
  have hAP : A ≠ P := Ne.symm (perp_distinct_c A B P A h₂).2
  have hNColABP : ¬ Col A B P := by
    intro hcol
    rcases l8_9_c B A P (perp_per_1_c A B P h₂) (col_permutation_4_c A B P hcol) with hba | hpa
    · exact hAB hba.symm
    · exact (perp_distinct_c A B P A h₂).2 hpa
  have hBR : B ≠ R := by
    intro hbr
    rw [← hbr] at hCgAPBR
    exact hAP (cong_identity A P B hCgAPBR)
  have hColABX : Col A B X := by
    rcases Classical.em (T = B) with htb | htb
    · rw [htb] at hBetTXB
      have hbx : B = X := between_identity B X hBetTXB
      rw [← hbx]
      exact col_trivial_2_c A B
    · exact col3_c T B A B X htb (col_permutation_3_c A B T h₃)
        (col_trivial_2_c T B)
        (col_permutation_5_c T X B (bet_col_c T X B hBetTXB))
  have hPR : P ≠ R := by
    intro hpr
    rw [← hpr] at hBetRXP
    have hpx : P = X := between_identity P X hBetRXP
    rw [← hpx] at hColABX
    exact hNColABP hColABX
  have hPerpABRB : Perp A B R B :=
    perp_sym_c R B A B
      (perp_col2_c Q B R B A B (perp_sym_c A B Q B h₁) (Ne.symm hBR)
        (col_permutation_2_c B R Q (bet_col_c B R Q hBetBRQ)) (col_trivial_2_c Q B))
  have hCgARPB : Cong A R P B :=
    perp_cong_c A B P R X hAB hAP h₂ hPerpABRB hCgAPBR hColABX
      (between_symmetry_c R X P hBetRXP)
  exact ⟨X, (l7_21_c A P B R X
    (fun h => hNColABP (col_permutation_5_c A P B h)) hPR hCgAPBR
    (cong_right_commutativity_c P B A R (cong_symmetry_c A R P B hCgARPB))
    (col_permutation_5_c A B X hColABX)
    (bet_col_c P X R (between_symmetry_c R X P hBetRXP))).1⟩

theorem midpoint_existence_c (A B : Tpoint) : ∃ X, Midpoint X A B := by
  rcases Classical.em (A = B) with hab | hAB
  · refine ⟨A, ?_⟩
    rw [hab]
    exact l7_3_2_c B
  · obtain ⟨Q, T₀, hPerpBAQB, -, -⟩ := l8_21_c B A A (Ne.symm hAB)
    obtain ⟨P, T, hPerpABPA, hColABT, hBetQTP⟩ := l8_21_c A B Q hAB
    rcases le_cases_c A P B Q with hle | hle
    · exact midpoint_existence_aux_c A B P Q T hAB
        (perp_left_comm_c B A Q B hPerpBAQB) hPerpABPA hColABT hBetQTP hle
    · obtain ⟨X, hM⟩ := midpoint_existence_aux_c B A Q P T (Ne.symm hAB)
        (perp_left_comm_c A B P A hPerpABPA) hPerpBAQB
        (col_permutation_4_c A B T hColABT)
        (between_symmetry_c Q T P hBetQTP) hle
      exact ⟨X, l7_2_c X B A hM⟩

theorem perp_in_id_c (A B C X : Tpoint) (h : Perp_at X A B C A) : X = A := by
  exact l8_14_2_1b_c X A B C A A h (col_trivial_1_c A B) (col_trivial_3_c A C)

theorem l8_22_c (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Per B A P) (h₂ : Per A B R) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) :
    Cong A R P B ∧ Midpoint X A B ∧ Midpoint X P R := sorry

theorem l8_22_bis_c (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Perp A B P A) (h₂ : Perp A B R B) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) :
    Cong A R P B ∧ Midpoint X A B ∧ Midpoint X P R :=
  l8_22_c A B P R X hAB hAP (perp_per_1_c A B P h₁) (perp_per_1_c B A R (perp_comm_c A B B R (perp_comm_c B A R B (perp_comm_c A B B R (perp_right_comm_c A B R B h₂))))) h₃ hCol hBet

theorem perp_in_perp_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp A B C D :=
  ⟨X, h⟩

theorem perp_proj_c (A B C D : Tpoint) (h₁ : Perp A B C D) (hNCol : ¬ Col A C D) :
    ∃ X, Col A B X ∧ Perp A X C D := by
  obtain ⟨X, hX⟩ := h₁
  refine ⟨X, ?_, ?_⟩
  · obtain ⟨_, _, hColXAB, _⟩ := hX
    exact col_permutation_1_c X A B hColXAB
  · apply perp_col_c A B C D X
    · intro hAX
      subst hAX
      obtain ⟨_, _, _, hColACD, _⟩ := hX
      exact hNCol hColACD
    · exact perp_in_perp_c A B C D X hX
    · obtain ⟨_, _, hColXAB, _⟩ := hX
      exact col_permutation_1_c X A B hColXAB

theorem l8_24_c (A B P Q R T : Tpoint)
    (h₁ : Perp P A A B) (h₂ : Perp Q B A B)
    (h₃ : Col A B T) (h₄ : Bet P T Q) (h₅ : Bet B R Q) (h₆ : Cong A P B R) :
    ∃ X, Midpoint X A B ∧ Midpoint X P R := by
  obtain ⟨X, hBetTXB, hBetRXP⟩ := inner_pasch P B Q T R h₄ h₅
  have hPerpABPA : Perp A B P A := perp_sym_c P A A B h₁
  have hAB : A ≠ B := (perp_distinct_c A B P A hPerpABPA).1
  have hAP : A ≠ P := Ne.symm (perp_distinct_c A B P A hPerpABPA).2
  have hColABX : Col A B X := by
    rcases Classical.em (T = B) with htb | htb
    · rw [htb] at hBetTXB
      have hbx : B = X := between_identity B X hBetTXB
      rw [← hbx]; exact col_trivial_2_c A B
    · exact col3_c T B A B X htb (col_permutation_3_c A B T h₃)
        (col_trivial_2_c T B)
        (col_permutation_5_c T X B (bet_col_c T X B hBetTXB))
  have hNColABP : ¬ Col A B P := by
    intro hcol
    rcases l8_9_c B A P (perp_per_1_c A B P hPerpABPA) (col_permutation_4_c A B P hcol) with hba | hpa
    · exact hAB hba.symm
    · exact hAP hpa.symm
  have hBR : B ≠ R := by
    intro hbr
    rw [← hbr] at h₆
    exact hAP (cong_identity A P B h₆)
  have hQB : Q ≠ B := (perp_distinct_c Q B A B h₂).1
  have hPerABQ : Per A B Q := perp_per_2_c B A Q (perp_comm_c A B Q B (perp_sym_c Q B A B h₂))
  have hNColABQ : ¬ Col A B Q := by
    intro hcol
    rcases l8_9_c A B Q hPerABQ hcol with hab | hqb
    · exact hAB hab
    · exact hQB hqb
  have hNColABR : ¬ Col A B R := by
    intro hcol
    exact hNColABQ (col_permutation_4_c B A Q
      (col_transitivity_1_c B R A Q hBR
        (col_permutation_5_c B A R (col_permutation_4_c A B R hcol))
        (bet_col_c B R Q h₅)))
  have hPR : P ≠ R := by
    intro hpr
    rw [← hpr] at hBetRXP
    have hpx : P = X := between_identity P X hBetRXP
    rw [← hpx] at hColABX
    exact hNColABP hColABX
  have hPerpABRB : Perp A B R B :=
    perp_sym_c R B A B
      (perp_left_comm_c B R A B
        (perp_col_c B Q A B R hBR
          (perp_left_comm_c Q B A B h₂)
          (col_permutation_5_c B R Q (bet_col_c B R Q h₅))))
  have hCgARPB : Cong A R P B :=
    perp_cong_c A B P R X hAB hAP hPerpABPA hPerpABRB h₆ hColABX
      (between_symmetry_c R X P hBetRXP)
  exact ⟨X, l7_21_c A P B R X (fun h => hNColABP (col_permutation_5_c A P B h)) hPR h₆
    (cong_right_commutativity_c P B A R (cong_symmetry_c A R P B hCgARPB))
    (col_permutation_5_c A B X hColABX)
    (bet_col_c P X R (between_symmetry_c R X P hBetRXP))⟩

theorem col_per2__per_c (A B C P X : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Per A X P) (h₂ : Per B X P) : Per C X P := by
  obtain ⟨Q, hQ⟩ := symmetric_point_construction_c P X
  refine ⟨Q, hQ, ?_⟩
  exact l4_17_c A B C P Q hAB hCol (per_double_cong_c A X P Q h₁ hQ) (per_double_cong_c B X P Q h₂ hQ)

theorem perp_in_per_1_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X C := by
  have H0 := h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5 A C (col_trivial_1_c A B) (col_trivial_1_c C D)

theorem perp_in_per_2_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X D := by
  have H0 := h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5 A D (col_trivial_1_c A B) (col_trivial_3_c D C)

theorem perp_in_per_3_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X C := by
  have H0 := h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5 B C (col_trivial_3_c B A) (col_trivial_1_c C D)

theorem perp_in_per_4_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X D := by
  have H0 := h
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5 B D (col_trivial_3_c B A) (col_trivial_3_c D C)

theorem ts_distincts_c (A B P Q : Tpoint) (h : TS A B P Q) :
    A ≠ B ∧ A ≠ P ∧ A ≠ Q ∧ B ≠ P ∧ B ≠ Q ∧ P ≠ Q := by
  obtain ⟨hnc1, hnc2, T, hColT, hBet⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; apply hnc1; rw [e]; exact col_trivial_2_c _ _
  · intro e; apply hnc1; rw [← e]; exact col_trivial_1_c _ _
  · intro e; apply hnc2; rw [← e]; exact col_trivial_1_c _ _
  · intro e; apply hnc1; rw [← e]; exact col_trivial_3_c _ _
  · intro e; apply hnc2; rw [← e]; exact col_trivial_3_c _ _
  · intro e
    rw [← e] at hBet
    have hPT := between_identity P T hBet
    apply hnc1
    rw [hPT]
    exact hColT

theorem l9_2_c (A B P Q : Tpoint) (h : TS A B P Q) : TS A B Q P := by
  obtain ⟨hPnCol, hQnCol, T, hTCol, hBet⟩ := h
  refine ⟨hQnCol, hPnCol, T, hTCol, ?_⟩
  exact between_symmetry_c P T Q hBet

theorem mid_preserves_col_c (A B C M A' B' C' : Tpoint)
    (hCol : Col A B C) (h₁ : Midpoint M A A')
    (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') : Col A' B' C' := by
  rcases hCol with H3 | H3
  · have H4 := l7_15_c A B C A' B' C' M h₁ h₂ h₃ H3
    exact bet_col_c A' B' C' H4
  · rcases H3 with H4 | H4
    · have H5 := l7_15_c B C A B' C' A' M h₂ h₃ h₁ H4
      exact col_permutation_2_c B' C' A' (bet_col_c B' C' A' H5)
    · have H5 := l7_15_c C A B C' A' B' M h₃ h₁ h₂ H4
      exact col_permutation_1_c C' A' B' (bet_col_c C' A' B' H5)

theorem per_mid_per_c (A B X Y M : Tpoint)
    (hAB : A ≠ B) (h₁ : Per X A B)
    (h₂ : Midpoint M A B) (h₃ : Midpoint M X Y) :
    Cong A X B Y ∧ Per Y B A := by
  have hCg1 : Cong A X B Y := l7_13_c M A X B Y (l7_2_c M A B h₂) (l7_2_c M X Y h₃)
  obtain ⟨B', hMidAB', hCgXB⟩ := h₁
  obtain ⟨hBetBAB', hCgBAAB'⟩ := hMidAB'
  obtain ⟨A', hMidBA'⟩ := symmetric_point_construction_c A B
  obtain ⟨hBetABA', hCgABBA'⟩ := hMidBA'
  have hCg2 : Cong B X A Y := l7_13_c M B X A Y h₂ (l7_2_c M X Y h₃)
  have hCgAB'BA' : Cong A B' B A' :=
    cong_transitivity_c A B' B A B A'
      (cong_symmetry_c B A A B' hCgBAAB')
      (cong_left_commutativity_c A B B A' hCgABBA')
  have hOFSC : OFSC B A B' X A B A' Y :=
    ⟨hBetBAB', hBetABA', cong_pseudo_reflexivity B A, hCgAB'BA', hCg2, hCg1⟩
  have hCgB'XA'Y : Cong B' X A' Y :=
    five_segment_with_def_c B A B' X A B A' Y hOFSC (Ne.symm hAB)
  have c1 : Cong Y A X B :=
    cong_commutativity_c A Y B X (cong_symmetry_c B X A Y hCg2)
  have c2 : Cong Y A X B' := cong_transitivity_c Y A X B X B' c1 hCgXB
  have c3 : Cong X B' A' Y :=
    cong_transitivity_c X B' B' X A' Y (cong_pseudo_reflexivity X B') hCgB'XA'Y
  have c4 : Cong Y A A' Y := cong_transitivity_c Y A X B' A' Y c2 c3
  exact ⟨hCg1, A', ⟨hBetABA', hCgABBA'⟩, cong_right_commutativity_c Y A A' Y c4⟩

theorem sym_preserve_diff_c (A B M A' B' : Tpoint)
    (hAB : A ≠ B) (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') :
    A' ≠ B' := by
  intro H2
  subst H2
  have H4 := l7_9_c A B M A' h₁ h₂
  exact ((hAB H4)).elim

theorem l9_4_1_aux_c (P Q A C R S M : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem per_col_eq_c (A B C : Tpoint)
    (h₁ : Per A B C) (hCol : Col A B C) (hBC : B ≠ C) : A = B := by
  obtain ⟨C', hMid, hCong⟩ := h₁
  obtain ⟨hBet, hCg⟩ := hMid
  have hCAC' : Col C A C' :=
    col_transitivity_1_c C B A C' (Ne.symm hBC)
      (col_permutation_3_c A B C hCol) (bet_col_c C B C' hBet)
  rcases l7_20_c A C C' hCAC' hCong with hCC' | hM
  · rw [← hCC'] at hBet hCg
    exact absurd (l7_3_c B C ⟨hBet, hCg⟩) hBC
  · exact l7_17_c C C' A B hM ⟨hBet, hCg⟩

theorem l9_4_1_c (P Q A C R S M : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem mid_two_sides_c (A B M X Y : Tpoint)
    (h₁ : Midpoint M A B) (hNCol : ¬ Col A B X) (h₂ : Midpoint M X Y) :
    TS A B X Y := by
  obtain ⟨hBetAMB, _⟩ := h₁
  obtain ⟨hBetXMY, hCongXM⟩ := h₂
  have hColMAB : Col M A B := col_permutation_4_c A M B (Or.inl hBetAMB)
  have hNColX : ¬ Col X A B := fun hc => hNCol (col_permutation_1_c X A B hc)
  have hMY : M ≠ Y := by
    intro e
    rw [← e] at hCongXM
    have hXM := cong_identity X M M hCongXM
    apply hNColX
    rw [hXM]
    exact hColMAB
  have hNColY : ¬ Col Y A B := by
    intro hc
    apply hNCol
    exact colx_c M Y X A B hMY (col_permutation_1_c M A B hColMAB)
      (col_permutation_1_c Y A B hc)
      (col_permutation_5_c M X Y (col_permutation_4_c X M Y (Or.inl hBetXMY)))
  exact ⟨hNColX, hNColY, M, hColMAB, hBetXMY⟩

theorem col_preserves_two_sides_c (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h : TS A B X Y) :
    TS C D X Y := by
  obtain ⟨hXAB, hYAB, T, hTAB, hBet⟩ := h
  have hAB : A ≠ B := by
    intro heq
    subst heq
    exact hXAB (col_trivial_2_c X A)
  refine ⟨?_, ?_, T, ?_, hBet⟩
  · intro hXCD
    apply hXAB
    apply col_permutation_2_c
    exact colx_c C D X A B hCD h₁ h₂ (col_permutation_5_c C X D (col_permutation_4_c X C D hXCD))
  · intro hYCD
    apply hYAB
    apply col_permutation_2_c
    exact colx_c C D Y A B hCD h₁ h₂ (col_permutation_5_c C Y D (col_permutation_4_c Y C D hYCD))
  · exact col3_c A B T C D hAB (col_permutation_1_c T A B hTAB) h₁ h₂

theorem out_out_two_sides_c (A B X Y U V I : Tpoint)
    (hAB : A ≠ B) (h₁ : TS A B X Y)
    (hCol1 : Col I A B) (hCol2 : Col I X Y)
    (hOut1 : Out I X U) (hOut2 : Out I Y V) : TS A B U V := by
  obtain ⟨hNX, hNY, T, hTC, hBet⟩ := h₁
  obtain ⟨hXI, hUI, horX⟩ := hOut1
  obtain ⟨hYI, hVI, horY⟩ := hOut2
  have hIU : I ≠ U := Ne.symm hUI
  have hIV : I ≠ V := Ne.symm hVI
  have hABI : Col A B I := col_permutation_1_c I A B hCol1
  have hNU : ¬ Col U A B := by
    intro hU
    have hIUX : Col I U X := by
      rcases horX with hb | hb
      · exact col_permutation_5_c I X U (bet_col_c I X U hb)
      · exact bet_col_c I U X hb
    have hABU : Col A B U := col_permutation_1_c U A B hU
    exact hNX (col3_c I U X A B hIU hIUX
      (col_permutation_1_c A I U (col_transitivity_1_c A B I U hAB hABI hABU))
      (col_permutation_1_c B I U (col_transitivity_1_c B A I U (Ne.symm hAB)
        (col_permutation_4_c A B I hABI) (col_permutation_4_c A B U hABU))))
  have hNV : ¬ Col V A B := by
    intro hV
    have hIVY : Col I V Y := by
      rcases horY with hb | hb
      · exact col_permutation_5_c I Y V (bet_col_c I Y V hb)
      · exact bet_col_c I V Y hb
    have hABV : Col A B V := col_permutation_1_c V A B hV
    exact hNY (col3_c I V Y A B hIV hIVY
      (col_permutation_1_c A I V (col_transitivity_1_c A B I V hAB hABI hABV))
      (col_permutation_1_c B I V (col_transitivity_1_c B A I V (Ne.symm hAB)
        (col_permutation_4_c A B I hABI) (col_permutation_4_c A B V hABV))))
  have hXY : X ≠ Y := by
    intro hxy
    rw [hxy] at hBet
    have hYT : Y = T := between_identity Y T hBet
    rw [← hYT] at hTC
    exact hNY hTC
  have hIT : I = T := l6_21_c A B X Y I T
    (fun hc => hNX (col_permutation_2_c A B X hc)) hXY
    (col_permutation_1_c I A B hCol1) (col_permutation_1_c T A B hTC)
    (col_permutation_1_c I X Y hCol2)
    (col_permutation_5_c X T Y (bet_col_c X T Y hBet))
  rw [← hIT] at hBet
  exact ⟨hNU, hNV, I, hCol1,
    bet_out_out_bet_c X I Y U V hBet ⟨hXI, hUI, horX⟩ ⟨hYI, hVI, horY⟩⟩

theorem l9_4_2_aux_c (P Q A C R S U V : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := sorry

theorem l9_4_2_c (P Q A C R S U V : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := by
  have H6 := le_cases_c S C R A
  rcases H6 with H7 | H7
  · exact l9_4_2_aux_c P Q A C R S U V H7 h₁ hR hPerpA hS hPerpC hOutU hOutV
  · exact l9_2_c P Q V U ((let H8 := l9_2_c P Q A C h₁; l9_4_2_aux_c P Q C A S R V U H7 H8 hS hPerpC hR hPerpA hOutV hOutU))

theorem l9_5_c (P Q A C R B : Tpoint)
    (h₁ : TS P Q A C) (hR : Col R P Q) (hOut : Out R A B) : TS P Q B C := sorry

theorem outer_pasch_c (A B C P Q : Tpoint) (h₁ : Bet A C P) (h₂ : Bet B Q C) :
    ∃ X, Bet A X B ∧ Bet P Q X := sorry

theorem os_distincts_c (A B X Y : Tpoint) (h : OS A B X Y) :
    A ≠ B ∧ A ≠ X ∧ A ≠ Y ∧ B ≠ X ∧ B ≠ Y := by
  obtain ⟨Z, HTS1, HTS2⟩ := h
  have HTS3 := ts_distincts_c A B X Z HTS1
  have HTS4 := ts_distincts_c A B Y Z HTS2
  obtain ⟨hAB1, hAX, _, hBX, _, _⟩ := HTS3
  obtain ⟨_, hAY, _, hBY, _, _⟩ := HTS4
  exact ⟨hAB1, hAX, hAY, hBX, hBY⟩

theorem invert_one_side_c (A B P Q : Tpoint) (h : OS A B P Q) : OS B A P Q := by
  obtain ⟨R, h1, h2⟩ := h
  obtain ⟨nc1, nc2, T, hcolT, hbet⟩ := h1
  obtain ⟨nc1', nc2', T', hcolT', hbet'⟩ := h2
  exact ⟨R,
    ⟨not_col_permutation_5_c P A B nc1, not_col_permutation_5_c R A B nc2,
     T, col_permutation_5_c T A B hcolT, hbet⟩,
    ⟨not_col_permutation_5_c Q A B nc1', not_col_permutation_5_c R A B nc2',
     T', col_permutation_5_c T' A B hcolT', hbet'⟩⟩

theorem l9_8_1_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : TS P Q B C) :
    OS P Q A B :=
  ⟨C, (⟨h₁, h₂⟩)⟩

theorem not_two_sides_id_c (A P Q : Tpoint) : ¬ TS P Q A A := by
  intro H
  obtain ⟨_, H0⟩ := H
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨T, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  have H6 := between_identity A T H5
  subst H6
  exact H1 H4

theorem l9_8_2_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : OS P Q A B) :
    TS P Q B C := sorry

theorem l9_9_c (P Q A B : Tpoint) (h : TS P Q A B) : ¬ OS P Q A B := sorry

theorem l9_9_bis_c (P Q A B : Tpoint) (h : OS P Q A B) : ¬ TS P Q A B := by
  intro H0
  obtain ⟨C, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  have H4 := l9_8_1_c P Q A B C H2 H3
  have H5 := l9_9_c P Q A B H0
  exact ((H5 H4)).elim

theorem one_side_chara_c (P Q A B : Tpoint) (h : OS P Q A B) :
    ∀ X, Col X P Q → ¬ Bet A X B := sorry

theorem l9_10_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) : ∃ C, TS P Q A C := by
  obtain ⟨A', hA'⟩ := symmetric_point_construction_c A P
  refine ⟨A', ?_, ?_, P, ?_, ?_⟩
  · exact hNCol
  · intro hCol
    apply hNCol
    apply col_permutation_2_c
    apply col_transitivity_1_c P A'
    · intro hEq
      rw [← hEq] at hA'
      have hMid := l7_2_c P A P hA'
      have hEq2 := is_midpoint_id_c P A hMid
      rw [← hEq2] at hNCol
      exact hNCol (col_trivial_1_c P Q)
    · exact col_permutation_4_c A' P Q hCol
    · right; right
      exact midpoint_bet_c A P A' hA'
  · exact col_trivial_1_c P Q
  · exact midpoint_bet_c A P A' hA'

theorem one_side_reflexivity_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) :
    OS P Q A A := by
  obtain ⟨C, hMid⟩ := symmetric_point_construction_c A P
  obtain ⟨hBet, hCong⟩ := hMid
  have hNC : ¬ Col C P Q := by
    intro h0
    rcases eq_dec_points_c C P with hCP | hCP
    · rw [hCP] at hCong
      have hAP : A = P := cong_identity A P P hCong
      exact hNCol (by rw [hAP]; exact col_trivial_1_c P Q)
    · exact hNCol (col_permutation_4_c P A Q
        (col_transitivity_1_c P C A Q (Ne.symm hCP)
          (col_permutation_1_c A P C (bet_col_c A P C hBet))
          (col_permutation_4_c C P Q h0)))
  exact ⟨C, ⟨hNCol, hNC, P, col_trivial_1_c P Q, hBet⟩,
         ⟨hNCol, hNC, P, col_trivial_1_c P Q, hBet⟩⟩

theorem one_side_symmetry_c (P Q A B : Tpoint) (h : OS P Q A B) :
    OS P Q B A := by
  obtain ⟨C, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  exact ⟨C, (⟨H2, H1⟩)⟩

theorem one_side_transitivity_c (P Q A B C : Tpoint)
    (h₁ : OS P Q A B) (h₂ : OS P Q B C) : OS P Q A C := by
  obtain ⟨X, H1⟩ := h₁
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨Y, H4⟩ := h₂
  obtain ⟨H5, H6⟩ := H4
  exact ⟨X, (⟨H2, (l9_2_c P Q X C (l9_8_2_c P Q Y X C (l9_2_c P Q C Y H6) (l9_8_1_c P Q Y X B (l9_2_c P Q B Y H5) (l9_2_c P Q B X H3))))⟩)⟩

theorem l9_17_c (A B C P Q : Tpoint) (h₁ : OS P Q A C) (h₂ : Bet A B C) :
    OS P Q A B := sorry

theorem l9_18_c (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    TS X Y A B ↔ (Bet A P B ∧ ¬ Col X Y A ∧ ¬ Col X Y B) := by
  constructor
  · intro hTS
    obtain ⟨hNA, hNB, T, hTCol, hBet⟩ := hTS
    have hXY : X ≠ Y := by
      intro hEq
      subst hEq
      exact hNB (col_trivial_2_c B X)
    have hPT : P = T := by
      apply l6_21_c X Y A B P T
      · exact not_col_permutation_5_c X A Y (not_col_permutation_4_c A X Y hNA)
      · intro hEq
        subst hEq
        have : A = T := between_identity A T hBet
        subst this
        exact hNA hTCol
      · exact h₁
      · exact col_permutation_5_c X T Y (col_permutation_4_c T X Y hTCol)
      · exact h₂
      · exact col_permutation_5_c A T B (bet_col_c A T B hBet)
    subst hPT
    refine ⟨hBet, ?_, ?_⟩
    · exact not_col_permutation_5_c X A Y (not_col_permutation_4_c A X Y hNA)
    · exact not_col_permutation_5_c X B Y (not_col_permutation_4_c B X Y hNB)
  · intro hConj
    obtain ⟨hBet, hNA, hNB⟩ := hConj
    refine ⟨?_, ?_, P, ?_, hBet⟩
    · exact not_col_permutation_5_c A Y X (not_col_permutation_3_c X Y A hNA)
    · exact not_col_permutation_5_c B Y X (not_col_permutation_3_c X Y B hNB)
    · exact col_permutation_2_c X Y P h₁

theorem l9_19_c (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    OS X Y A B ↔ (Out P A B ∧ ¬ Col X Y A) := sorry

theorem one_side_not_col123_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B X := by
  obtain ⟨C, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  obtain ⟨H4, H5⟩ := H1
  obtain ⟨_, _⟩ := H5
  intro H6
  exact H4 (col_permutation_2_c A B X H6)

theorem one_side_not_col124_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B Y :=
  one_side_not_col123_c A B Y X (one_side_symmetry_c A B X Y h)

theorem col_two_sides_c (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : TS A B P Q) : TS A C P Q := by
  obtain ⟨hPAB, hQAB, T, hTAB, hBet⟩ := h
  refine ⟨?_, ?_, T, ?_, hBet⟩
  · intro hPAC
    apply hPAB
    apply col_permutation_2_c
    exact col_transitivity_1_c A C B P hAC (col_permutation_5_c A B C hCol) (col_permutation_1_c P A C hPAC)
  · intro hQAC
    apply hQAB
    apply col_permutation_2_c
    exact col_transitivity_1_c A C B Q hAC (col_permutation_5_c A B C hCol) (col_permutation_1_c Q A C hQAC)
  · apply col_permutation_2_c
    apply col_transitivity_1_c A B C T
    · intro hAB
      subst hAB
      exact hQAB (col_trivial_2_c Q A)
    · exact hCol
    · exact col_permutation_1_c T A B hTAB

theorem col_one_side_c (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : OS A B P Q) : OS A C P Q := by
  obtain ⟨T, H2⟩ := h
  obtain ⟨H3, H4⟩ := H2
  exact ⟨T, (⟨(col_two_sides_c A B C P T hCol hAC H3), (col_two_sides_c A B C Q T hCol hAC H4)⟩)⟩

theorem out_out_one_side_c (A B X Y Z : Tpoint)
    (h₁ : OS A B X Y) (h₂ : Out A Y Z) : OS A B X Z := sorry

theorem out_one_side_c (A B X Y : Tpoint)
    (h₁ : ¬ Col A B X ∨ ¬ Col A B Y) (h₂ : Out A X Y) : OS A B X Y := sorry

theorem bet__ts_c (A B X Y : Tpoint)
    (hAY : A ≠ Y) (hNCol : ¬ Col A B X) (hBet : Bet X A Y) : TS A B X Y :=
  ⟨(not_col_permutation_5_c X B A (not_col_permutation_3_c A B X hNCol)), (⟨((fun H => hNCol (col_transitivity_1_c A Y B X hAY (col_permutation_5_c A B Y (col_permutation_1_c Y A B H)) (col_permutation_1_c X A Y (bet_col_c X A Y hBet))))), (⟨A, (⟨(col_trivial_1_c A B), hBet⟩)⟩)⟩)⟩

theorem bet_ts__ts_c (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    TS A B X Z := by
  obtain ⟨hNX, hNY, T, hT1, hT2⟩ := h₁
  have hXY : X ≠ Y := by
    intro hxy
    rw [hxy] at hT2
    have hYT : Y = T := between_identity Y T hT2
    rw [← hYT] at hT1
    exact hNY hT1
  refine ⟨hNX, ?_, T, hT1, between_exchange4_c X T Y Z hT2 h₂⟩
  intro hZ
  have hZT : Z = T := l6_21_c A B X Y Z T
    (fun hc => hNX (col_permutation_2_c A B X hc)) hXY
    (col_permutation_1_c Z A B hZ) (col_permutation_1_c T A B hT1)
    (bet_col_c X Y Z h₂)
    (col_permutation_5_c X T Y (bet_col_c X T Y hT2))
  rw [hZT] at h₂
  have hYT : Y = T := between_identity Y T (between_exchange3_c X Y T Y h₂ hT2)
  rw [← hYT] at hT1
  exact hNY hT1

theorem bet_ts__os_c (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    OS A B Y Z :=
  ⟨X, (⟨(l9_2_c A B X Y h₁), (l9_2_c A B X Z (bet_ts__ts_c A B X Y Z h₁ h₂))⟩)⟩

theorem l9_31_c (A X Y Z : Tpoint) (h₁ : OS A X Y Z) (h₂ : OS A Z Y X) :
    TS A Y X Z := sorry

theorem col123__nos_c (A B P Q : Tpoint) (h : Col P Q A) : ¬ OS P Q A B :=
  (fun HOne => (let H := one_side_not_col123_c P Q A B HOne; H h))

theorem col124__nos_c (A B P Q : Tpoint) (h : Col P Q B) : ¬ OS P Q A B :=
  (fun HOne => (let HN := col123__nos_c B A P Q h; HN (one_side_symmetry_c P Q A B HOne)))

theorem col2_os__os_c (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h₃ : OS A B X Y) :
    OS C D X Y := by
  obtain ⟨Z, Hts1, Hts2⟩ := h₃
  exact ⟨Z, col_preserves_two_sides_c A B C D X Z hCD h₁ h₂ Hts1, col_preserves_two_sides_c A B C D Y Z hCD h₁ h₂ Hts2⟩

theorem os_out_os_c (A B C D C' P : Tpoint)
    (hCol : Col A B P) (h₁ : OS A B C D) (h₂ : Out P C C') :
    OS A B C' D := sorry

theorem ts_ts_os_c (A B C D : Tpoint) (h₁ : TS A B C D) (h₂ : TS C D A B) :
    OS A C B D := sorry

theorem two_sides_not_col_c (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A B X := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  intro H2
  exact H0 (col_permutation_2_c A B X H2)

theorem col_one_side_out_c (A B X Y : Tpoint) (hCol : Col A X Y) (h : OS A B X Y) :
    Out A X Y := sorry

theorem col_two_sides_bet_c (A B X Y : Tpoint)
    (hCol : Col A X Y) (h : TS A B X Y) : Bet X A Y := sorry

theorem os_ts1324__os_c (A X Y Z : Tpoint)
    (h₁ : OS A X Y Z) (h₂ : TS A Y X Z) : OS A Z X Y := sorry

theorem ts2__ex_bet2_c (A B C D : Tpoint) (h₁ : TS A C B D) (h₂ : TS B D A C) :
    ∃ X, Bet A X C ∧ Bet B X D := sorry

theorem out_one_side_1_c (A B C D X : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (hOut : Out X C D) :
    OS A B C D := sorry

theorem out_two_sides_two_sides_c (A B X Y P PX : Tpoint)
    (hA_PX : A ≠ PX) (hCol : Col A B PX) (hOut : Out PX X P)
    (h : TS A B P Y) : TS A B X Y := sorry

theorem l8_21_bis_c (A B C X Y : Tpoint)
    (hXY : X ≠ Y) (hNCol : ¬ Col C A B) :
    ∃ P : Tpoint, Cong A P X Y ∧ Perp A B P A ∧ TS A B C P := sorry

theorem ts__ncol_c (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A X Y ∨ ¬ Col B X Y := by
  obtain ⟨hNX, hNY, T, hTC, hBet⟩ := h
  rcases eq_dec_points_c X T with hXT | hXT
  · rw [← hXT] at hTC
    exact absurd hTC hNX
  · have hXY : X ≠ Y := by
      intro hxy
      rw [← hxy] at hBet
      exact hXT (between_identity X T hBet)
    rcases eq_dec_points_c A T with hAT | hAT
    · refine Or.inr (fun hCol => hNX ?_)
      rw [← hAT] at hBet
      exact col_transitivity_1_c X Y A B hXY
        (col_permutation_5_c X A Y (bet_col_c X A Y hBet))
        (col_permutation_1_c B X Y hCol)
    · refine Or.inl (fun hCol => hNX ?_)
      have c3 : Col X T A := col_transitivity_1_c X Y T A hXY
        (col_permutation_5_c X T Y (bet_col_c X T Y hBet))
        (col_permutation_1_c A X Y hCol)
      have c4 : Col T X B := col_transitivity_1_c T A X B (Ne.symm hAT)
        (col_permutation_1_c X T A c3) hTC
      exact col_transitivity_1_c X T A B hXT c3 (col_permutation_4_c T X B c4)

theorem one_or_two_sides_aux_c (A B C D X : Tpoint)
    (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (h₁ : Col A C X) (h₂ : Col B D X) : TS A B C D ∨ OS A B C D := sorry

theorem cop__one_or_two_sides_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B) :
    TS A B C D ∨ OS A B C D := by
  obtain ⟨X, H2⟩ := hCop
  rcases H2 with H3 | H3
  · obtain ⟨H4, H5⟩ := H3
    have o := or_bet_out_c C X D
    rcases o with x | x
    · exact Or.inl (⟨hNC1, (⟨hNC2, (⟨X, (⟨(col_permutation_5_c X B A (col_permutation_3_c A B X H4)), x⟩)⟩)⟩)⟩)
    · rcases x with x0 | x0
      · exact Or.inr (out_one_side_1_c A B C D X (not_col_permutation_5_c A C B (not_col_permutation_4_c C A B hNC1)) H4 x0)
      · exact ((x0 (col_permutation_5_c C D X H5))).elim
  · rcases H3 with H4 | H4
    · obtain ⟨H5, H6⟩ := H4
      exact one_or_two_sides_aux_c A B C D X hNC1 hNC2 H5 H6
    · obtain ⟨H5, H6⟩ := H4
      have o := one_or_two_sides_aux_c A B D C X hNC2 hNC1 H5 H6
      rcases o with H7 | H7
      · exact Or.inl (l9_2_c A B D C H7)
      · exact Or.inr (one_side_symmetry_c A B D C H7)

theorem os__coplanar_c (A B C D : Tpoint) (h : OS A B C D) :
    Coplanar A B C D := sorry

theorem coplanar_trans_1_c (P Q R A B : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B) :
    Coplanar Q R A B := sorry

theorem col_cop__cop_c (A B C D E : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D) (hCol : Col C D E) :
    Coplanar A B C E := sorry

theorem bet_cop__cop_c (A B C D E : Tpoint)
    (hCop : Coplanar A B C E) (hBet : Bet C D E) : Coplanar A B C D := by
  have o := point_equality_decidability C E
  rcases o with x | x
  · subst x
    have HBet1 := between_identity C D hBet
    subst HBet1
    exact hCop
  · exact col_cop__cop_c A B C E D hCop x (col_permutation_5_c C D E (bet_col_c C D E hBet))

theorem col2_cop__cop_c (A B C D E F : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D)
    (h₁ : Col C D E) (h₂ : Col C D F) : Coplanar A B E F := sorry

theorem col_cop2__cop_c (A B C U V P : Tpoint)
    (hUV : U ≠ V) (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C V)
    (hCol : Col U V P) : Coplanar A B C P := sorry

theorem bet_cop2__cop_c (A B C U V W : Tpoint)
    (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C W) (hBet : Bet U V W) :
    Coplanar A B C V := by
  have o := point_equality_decidability U W
  rcases o with x | x
  · subst x
    have HBet1 := between_identity U V hBet
    subst HBet1
    exact h₁
  · exact col_cop2__cop_c A B C U W V x h₁ h₂ (col_permutation_5_c U V W (bet_col_c U V W hBet))

theorem coplanar_pseudo_trans_c (A B C D P Q R : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B)
    (h₃ : Coplanar P Q R C) (h₄ : Coplanar P Q R D) :
    Coplanar A B C D := sorry

theorem l9_30_c (A B C D E F P X Y Z : Tpoint)
    (hNCopP : ¬ Coplanar A B C P) (hNColDEF : ¬ Col D E F)
    (hCopDEF_P : Coplanar D E F P)
    (h₁ : Coplanar A B C X) (h₂ : Coplanar A B C Y) (h₃ : Coplanar A B C Z)
    (h₄ : Coplanar D E F X) (h₅ : Coplanar D E F Y) (h₆ : Coplanar D E F Z) :
    Col X Y Z := sorry

theorem cop_per2__col_c (A X Y Z : Tpoint)
    (hCop : Coplanar A X Y Z) (hAZ : A ≠ Z)
    (h₁ : Per X Z A) (h₂ : Per Y Z A) : Col X Y Z := sorry

theorem cop_perp2__col_c (X Y Z A B : Tpoint)
    (hCop : Coplanar A B Y Z) (h₁ : Perp X Y A B) (h₂ : Perp X Z A B) :
    Col X Y Z := sorry

theorem two_sides_dec_c (A B C D : Tpoint) : TS A B C D ∨ ¬ TS A B C D := sorry

theorem cop_nts__os_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNTS : ¬ TS A B C D) : OS A B C D := by
  have o := cop__one_or_two_sides_c A B C D hCop hNC1 hNC2
  rcases o with H3 | H3
  · exact ((hNTS H3)).elim
  · exact H3

theorem cop_nos__ts_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNOS : ¬ OS A B C D) : TS A B C D := by
  have o := cop__one_or_two_sides_c A B C D hCop hNC1 hNC2
  rcases o with H3 | H3
  · exact H3
  · exact ((hNOS H3)).elim

theorem one_side_dec_c (A B C D : Tpoint) : OS A B C D ∨ ¬ OS A B C D := sorry

theorem cop_dec_c (A B C D : Tpoint) : Coplanar A B C D ∨ ¬ Coplanar A B C D := sorry

theorem ex_diff_cop_c (A B C D : Tpoint) :
    ∃ E, Coplanar A B C E ∧ D ≠ E := by
  rcases point_equality_decidability A D with hAD | hAD
  · rcases point_equality_decidability B D with hBD | hBD
    · obtain ⟨E, hDE⟩ := another_point_c D
      refine ⟨E, ?_, hDE⟩
      rw [hAD, hBD]
      exact ⟨E, Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩⟩
    · exact ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_2_c _ _⟩⟩, Ne.symm hBD⟩
  · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c _ _, col_trivial_2_c _ _⟩⟩, Ne.symm hAD⟩

theorem ex_ncol_cop_c (A B C D E : Tpoint) (hDE : D ≠ E) :
    ∃ F, Coplanar A B C F ∧ ¬ Col D E F := by
  rcases col_dec_c A B C with hABC | hABC
  · obtain ⟨F, hF⟩ := not_col_exists_c D E hDE
    exact ⟨F, ⟨C, Or.inl ⟨hABC, col_trivial_3_c C F⟩⟩, hF⟩
  · rcases col_dec_c D E A with hDEA | hDEA
    · rcases col_dec_c D E B with hDEB | hDEB
      · refine ⟨C, ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c A C, col_trivial_2_c B C⟩)⟩,
          fun hDEC => hABC (col3_c D E A B C hDE hDEA hDEB hDEC)⟩
      · exact ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c A B, col_trivial_2_c C B⟩⟩, hDEB⟩
    · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c A B, col_trivial_2_c C A⟩⟩, hDEA⟩

theorem ex_ncol_cop2_c (A B C D : Tpoint) :
    ∃ E F, Coplanar A B C E ∧ Coplanar A B C F ∧ ¬ Col D E F := by
  obtain ⟨E, HE, HDE⟩ := ex_diff_cop_c A B C D
  obtain ⟨F, HF, HCol⟩ := ex_ncol_cop_c A B C D E HDE
  exact ⟨E, F, HE, HF, HCol⟩

theorem col2_cop2__eq_c (A B C U V P Q : Tpoint)
    (hNCop : ¬ Coplanar A B C U) (hUV : U ≠ V)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q)
    (h₃ : Col U V P) (h₄ : Col U V Q) : P = Q := sorry

theorem cong3_cop2__col_c (A B C P Q : Tpoint)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q) (hPQ : P ≠ Q)
    (h₃ : Cong A P A Q) (h₄ : Cong B P B Q) (h₅ : Cong C P C Q) :
    Col A B C := sorry

theorem l9_38_c (A B C P Q : Tpoint) (h : TSP A B C P Q) : TSP A B C Q P := by
  obtain ⟨HP, HQ, T, HT, HBet⟩ := h
  exact ⟨HQ, HP, T, HT, between_symmetry HBet⟩

theorem l9_39_c (A B C D P Q R : Tpoint)
    (h₁ : TSP A B C P R) (hCop : Coplanar A B C D) (hOut : Out D P Q) :
    TSP A B C Q R := sorry

theorem l9_41_1_c (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : TSP A B C Q R) : OSP A B C P Q :=
  ⟨R, (⟨h₁, h₂⟩)⟩

theorem l9_41_2_c (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : OSP A B C P Q) : TSP A B C Q R := sorry

theorem tsp_exists_c (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    ∃ Q, TSP A B C P Q := sorry

theorem osp_reflexivity_c (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    OSP A B C P P := sorry

theorem osp_symmetry_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    OSP A B C Q P := by
  rcases h with ⟨R, hR1, hR2⟩
  exact ⟨R, hR2, hR1⟩

theorem osp_transitivity_c (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P Q) (h₂ : OSP A B C Q R) : OSP A B C P R := sorry

theorem cop3_tsp__tsp_c (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : TSP A B C P Q) : TSP D E F P Q := sorry

theorem cop3_osp__osp_c (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : OSP A B C P Q) : OSP D E F P Q := sorry

theorem ncop_distincts_c (A B C D : Tpoint) (h : ¬ Coplanar A B C D) :
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inr (Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨C, Or.inr (Or.inr ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inr (Or.inr ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩⟩

theorem tsp_distincts_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q ∧ P ≠ Q := by
  obtain ⟨HP, HQ, T, hT, hBet⟩ := h
  obtain ⟨hab, hac, hap, hbc, hbp, hcp⟩ := ncop_distincts_c A B C P HP
  obtain ⟨_, _, haq, _, hbq, hcq⟩ := ncop_distincts_c A B C Q HQ
  refine ⟨hab, hac, hbc, hap, hbp, hcp, haq, hbq, hcq, ?_⟩
  intro hpq
  rw [hpq] at hBet
  have hTQ := between_identity Q T hBet
  rw [← hTQ] at hT
  exact HQ hT

theorem osp_distincts_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q := by
  obtain ⟨R, HPR, HQR⟩ := h
  have hPR := tsp_distincts_c A B C P R HPR
  have hQR := tsp_distincts_c A B C Q R HQR
  obtain ⟨hAB, hAC, hBC, hAP, hBP, hCP, -, -, -, -⟩ := hPR
  obtain ⟨-, -, -, hAQ, hBQ, hCQ, -, -, -, -⟩ := hQR
  exact ⟨hAB, hAC, hBC, hAP, hBP, hCP, hAQ, hBQ, hCQ⟩

theorem tsp__ncop1_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C P := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  exact H0

theorem tsp__ncop2_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C Q := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨H1, _⟩ := H0
  exact H1

theorem osp__ncop1_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C P := by
  rcases h with ⟨R, hTSP, _⟩
  exact tsp__ncop1_c A B C P R hTSP

theorem osp__ncop2_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C Q := by
  obtain ⟨R, H1, H2⟩ := h
  exact tsp__ncop1_c A B C Q R H2

theorem tsp__nosp_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ OSP A B C P Q := sorry

theorem osp__ntsp_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ TSP A B C P Q := sorry

theorem osp_bet__osp_c (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P R) (h₂ : Bet P Q R) : OSP A B C P Q := sorry

theorem l9_18_3_c (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    TSP A B C X Y ↔ Bet X P Y ∧ ¬ Coplanar A B C X ∧ ¬ Coplanar A B C Y := sorry

theorem bet_cop__tsp_c (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hPY : P ≠ Y)
    (hCop : Coplanar A B C P) (hBet : Bet X P Y) : TSP A B C X Y := sorry

theorem cop_out__osp_c (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hCop : Coplanar A B C P)
    (hOut : Out P X Y) : OSP A B C X Y := sorry

theorem l9_19_3_c (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    OSP A B C X Y ↔ Out P X Y ∧ ¬ Coplanar A B C X := sorry

theorem cop2_ts__tsp_c (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : TS D E X Y) : TSP A B C X Y := sorry

theorem cop2_os__osp_c (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : OS D E X Y) : OSP A B C X Y := sorry

theorem cop3_tsp__ts_c (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : TSP A B C X Y) : TS D E X Y :=
  (let HX := tsp__ncop1_c A B C X Y h₄; (let HY := tsp__ncop2_c A B C X Y h₄; cop_nos__ts_c D E X Y h₃ ((fun H => HX (col_cop2__cop_c A B C D E X hDE h₁ h₂ (col_permutation_5_c D X E (col_permutation_4_c X D E H))))) ((fun H => HY (col_cop2__cop_c A B C D E Y hDE h₁ h₂ (col_permutation_5_c D Y E (col_permutation_4_c Y D E H))))) ((fun H => (let HTSP0 := tsp__nosp_c A B C X Y h₄; HTSP0 (cop2_os__osp_c A B C D E X Y HX h₁ h₂ H))))))

theorem cop3_osp__os_c (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : OSP A B C X Y) : OS D E X Y :=
  (let HX := osp__ncop1_c A B C X Y h₄; (let HY := osp__ncop2_c A B C X Y h₄; cop_nts__os_c D E X Y h₃ ((fun H => HX (col_cop2__cop_c A B C D E X hDE h₁ h₂ (col_permutation_5_c D X E (col_permutation_4_c X D E H))))) ((fun H => HY (col_cop2__cop_c A B C D E Y hDE h₁ h₂ (col_permutation_5_c D Y E (col_permutation_4_c Y D E H))))) ((fun H => (let HOSP0 := osp__ntsp_c A B C X Y h₄; HOSP0 (cop2_ts__tsp_c A B C D E X Y HX h₁ h₂ H))))))

theorem cop_tsp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : TSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := by
  rcases col_dec_c D E P with hcol | hncol
  · have hd := tsp_distincts_c A B C D E h
    rcases point_equality_decidability P A with hPA | hPA
    · refine ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_2_c _ _⟩⟩,
        ⟨P, Or.inl ⟨hcol, col_trivial_3_c _ _⟩⟩, ?_⟩
      rw [hPA]
      exact hd.1
    · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c _ _, col_trivial_2_c _ _⟩⟩,
        ⟨P, Or.inl ⟨hcol, col_trivial_3_c _ _⟩⟩, hPA⟩
  · obtain ⟨_, _, T, hTcop, hbet⟩ := h
    have hColDET : Col D E T := col_permutation_5_c D T E (Or.inl hbet)
    refine ⟨T, hTcop, ⟨T, Or.inl ⟨hColDET, col_trivial_2_c _ _⟩⟩, ?_⟩
    intro e
    apply hncol
    rw [e]
    exact hColDET

theorem cop_osp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : OSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := sorry

theorem sac__coplanar_c (A B C D : Tpoint) (h : Saccheri A B C D) :
    Coplanar A B C D := sorry

theorem ex_sym_c (A B X : Tpoint) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y) := sorry

theorem is_image_is_image_spec_c (P P' A B : Tpoint) (hAB : A ≠ B) :
    Reflect P' P A B ↔ ReflectL P' P A B :=
  ⟨fun h => h.elim (fun ⟨_, hr⟩ => hr) (fun ⟨hab, _⟩ => absurd hab hAB), fun h => Or.inl ⟨hAB, h⟩⟩

theorem ex_sym1_c (A B X : Tpoint) (hAB : A ≠ B) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y ∧ Reflect X Y A B) := sorry

theorem l10_2_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P1 P A B) (h₂ : Reflect P2 P A B) : P1 = P2 := sorry

theorem l10_2_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P1 P A B) (h₂ : ReflectL P2 P A B) : P1 = P2 := sorry

theorem l10_2_existence_spec_c (A B P : Tpoint) :
    ∃ P', ReflectL P' P A B := sorry

theorem l10_2_existence_c (A B P : Tpoint) :
    ∃ P', Reflect P' P A B := by
  have o := point_equality_decidability A B
  rcases o with H | H
  · subst H
    obtain ⟨P', H0⟩ := (symmetric_point_construction_c P A)
    exact ⟨P', (Or.inr (⟨rfl, H0⟩))⟩
  · obtain ⟨P', H0⟩ := (l10_2_existence_spec_c A B P)
    exact ⟨P', (Or.inl (⟨((fun H1 => (let H2 := H H1; (H2).elim))), H0⟩))⟩

theorem l10_4_spec_c (A B P P' : Tpoint) (h : ReflectL P P' A B) :
    ReflectL P' P A B := by
  obtain ⟨⟨X, hMid, hCol⟩, hOr⟩ := h
  refine ⟨⟨X, l7_2_c X P' P hMid, hCol⟩, ?_⟩
  rcases hOr with hp | he
  · exact Or.inl (perp_right_comm_c A B P' P hp)
  · exact Or.inr he.symm

theorem l10_4_c (A B P P' : Tpoint) (h : Reflect P P' A B) :
    Reflect P' P A B := by
  rcases h with ⟨hne, hL⟩ | ⟨heq, hMid⟩
  · exact Or.inl ⟨hne, l10_4_spec_c A B P P' hL⟩
  · exact Or.inr ⟨heq, l7_2_c A P' P hMid⟩

theorem l10_5_c (A B P P' P'' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect P'' P' A B) : P = P'' := sorry

theorem l10_6_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P P1 A B) (h₂ : Reflect P P2 A B) : P1 = P2 := sorry

theorem l10_6_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P P1 A B) (h₂ : ReflectL P P2 A B) : P1 = P2 := sorry

theorem l10_6_existence_spec_c (A B P' : Tpoint) (hAB : A ≠ B) :
    ∃ P, ReflectL P' P A B := by
  have H0 := l10_2_existence_spec_c A B P'
  obtain ⟨P, H⟩ := H0
  exact ⟨P, (l10_4_spec_c A B P P' H)⟩

theorem l10_6_existence_c (A B P' : Tpoint) :
    ∃ P, Reflect P' P A B := by
  have H := l10_2_existence_c A B P'
  obtain ⟨P, H0⟩ := H
  exact ⟨P, (l10_4_c A B P P' H0)⟩

theorem l10_7_c (A B P P' Q Q' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect Q' Q A B) (h₃ : P' = Q') : P = Q := by
  subst h₃
  exact l10_2_uniqueness_c A B P' P Q (l10_4_c A B P' P h₁) (l10_4_c A B P' Q h₂)

theorem l10_8_c (A B P : Tpoint) (h : Reflect P P A B) : Col P A B := by
  rcases h with ⟨hne, hL⟩ | ⟨heq, hMid⟩
  · obtain ⟨⟨X, hMidX, hColX⟩, _⟩ := hL
    have hXP : X = P := l7_3_c X P hMidX
    rw [hXP] at hColX
    exact col_permutation_2_c A B P hColX
  · have hAP : A = P := l7_3_c A P hMid
    rw [← hAP]
    exact col_trivial_1_c A B

theorem col__refl_c (A B P : Tpoint) (h : Col P A B) : ReflectL P P A B :=
  ⟨(⟨P, (⟨(l7_3_2_c P), (col_permutation_5_c A P B (col_permutation_4_c P A B h))⟩)⟩), (Or.inr rfl)⟩

theorem is_image_spec_col_cong_c (A B P P' X : Tpoint)
    (h₁ : ReflectL P P' A B) (h₂ : Col A B X) : Cong P X P' X := by
  obtain ⟨⟨M, hMid, hColM⟩, hOr⟩ := h₁
  rcases hOr with hPerp | hPP
  · obtain ⟨hBetM, hCgM⟩ := hMid
    rcases eq_dec_points_c M X with hMX | hMX
    · rw [hMX] at hCgM
      exact cong_left_commutativity_c X P P' X (cong_symmetry_c P' X X P hCgM)
    · have hPerpMX : Perp M X P' P := perp_col2_c A B M X P' P hPerp hMX hColM h₂
      obtain ⟨-, -, -, -, hUV⟩ := l8_14_2_1b_bis_c M X P' P M hPerpMX
        (col_trivial_1_c M X)
        (col_permutation_4_c P' M P (bet_col_c P' M P hBetM))
      have hPerXMP : Per X M P := hUV X P (col_trivial_3_c X M) (col_trivial_3_c P P')
      obtain ⟨P0, hM0, hCg0⟩ := hPerXMP
      have hP0 : P0 = P' := symmetric_point_uniqueness_c P M P0 P'
        hM0 (l7_2_c M P' P ⟨hBetM, hCgM⟩)
      rw [hP0] at hCg0
      exact cong_commutativity_c X P X P' hCg0
  · rw [hPP]
    exact cong_reflexivity P X

theorem is_image_col_cong_c (A B P P' X : Tpoint) (hAB : A ≠ B)
    (h₁ : Reflect P P' A B) (h₂ : Col A B X) : Cong P X P' X := by
  rcases h₁ with ⟨-, hL⟩ | ⟨heq, hMid⟩
  · exact is_image_spec_col_cong_c A B P P' X hL h₂
  · exact absurd heq hAB

theorem image_id_c (A B T T' : Tpoint) (hAB : A ≠ B)
    (hCol : Col A B T) (hRefl : Reflect T T' A B) : T = T' := sorry

theorem osym_not_col_c (A B P P' : Tpoint)
    (h₁ : Reflect P P' A B) (h₂ : ¬ Col A B P) : ¬ Col A B P' := sorry

theorem midpoint_preserves_image_c (A B P P' Q Q' M : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B M) (hRefl : Reflect P P' A B)
    (h₁ : Midpoint M P Q) (h₂ : Midpoint M P' Q') : Reflect Q Q' A B := sorry

theorem image_in_is_image_spec_c (M A B P P' : Tpoint)
    (h : ReflectL_at M P P' A B) : ReflectL P P' A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H0
  exact ⟨(⟨M, (⟨H2, H3⟩)⟩), H1⟩

theorem image_in_gen_is_image_c (M A B P P' : Tpoint)
    (h : Reflect_at M P P' A B) : Reflect P P' A B := by
  rcases h with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    have H3 := image_in_is_image_spec_c M A B P P' H2
    exact Or.inl (⟨((fun H4 => (let H5 := H1 H4; (H5).elim))), H3⟩)
  · obtain ⟨H1, H2⟩ := H0
    obtain ⟨H3, H4⟩ := H2
    subst H1
    subst H3
    exact Or.inr (⟨rfl, H4⟩)

theorem image_image_in_c (A B P P' M : Tpoint) (hPP' : P ≠ P')
    (h₁ : ReflectL P P' A B) (h₂ : Col A B M) (h₃ : Col P M P') :
    ReflectL_at M P P' A B := sorry

theorem image_in_col_c (A B P P' Y : Tpoint)
    (h : ReflectL_at Y P P' A B) : Col P P' Y := by
  obtain ⟨H0, _⟩ := h
  obtain ⟨H1, _⟩ := H0
  have H2 := midpoint_col_c P' Y P H1
  exact col_permutation_5_c P Y P' (col_permutation_2_c Y P' P H2)

theorem is_image_spec_rev_c (P P' A B : Tpoint)
    (h : ReflectL P P' A B) : ReflectL P P' B A := by
  obtain ⟨⟨M0, hM0_mid, hM0_col⟩, hperp_or_eq⟩ := h
  refine ⟨⟨M0, hM0_mid, col_permutation_4_c A B M0 hM0_col⟩, ?_⟩
  cases hperp_or_eq with
  | inl hperp => exact Or.inl (perp_left_comm_c A B P' P hperp)
  | inr heq => exact Or.inr heq

theorem is_image_rev_c (P P' A B : Tpoint)
    (h : Reflect P P' A B) : Reflect P P' B A := by
  rcases h with ⟨hne, hrefl⟩ | ⟨heq, hmid⟩
  · left
    exact ⟨Ne.symm hne, is_image_spec_rev_c P P' A B hrefl⟩
  · right
    subst heq
    exact ⟨rfl, hmid⟩

theorem midpoint_preserves_per_c (A B C A1 B1 C1 M : Tpoint)
    (hPer : Per A B C)
    (h₁ : Midpoint M A A1) (h₂ : Midpoint M B B1) (h₃ : Midpoint M C C1) :
    Per A1 B1 C1 := by
  obtain ⟨C', H3⟩ := hPer
  obtain ⟨H4, H5⟩ := H3
  have mp := symmetric_point_construction_c C' M
  obtain ⟨C1', H6⟩ := mp
  exact ⟨C1', (⟨(symmetry_preserves_midpoint_c C B C' C1 B1 C1' M h₃ h₂ H6 H4), (l7_16_c A C A C' A1 C1 A1 C1' M h₁ h₃ h₁ H6 H5)⟩)⟩

theorem col__image_spec_c (A B X : Tpoint) (h : Col A B X) :
    ReflectL X X A B :=
  ⟨(⟨X, (⟨(l7_3_2_c X), h⟩)⟩), (Or.inr rfl)⟩

theorem image_triv_c (A B : Tpoint) : Reflect A A A B := by
  have o := point_equality_decidability A B
  rcases o with H | H
  · exact Or.inr (⟨H, (l7_3_2_c A)⟩)
  · exact Or.inl (⟨H, (col__image_spec_c A B A (col_trivial_3_c A B))⟩)

theorem cong_midpoint__image_c (A B X Y : Tpoint)
    (h₁ : Cong A X A Y) (h₂ : Midpoint B X Y) : Reflect Y X A B := by
  rcases eq_dec_points_c A B with rfl | hAB
  · right
    exact ⟨rfl, h₂⟩
  · left
    refine ⟨hAB, ?_, ?_⟩
    · exact ⟨B, h₂, col_trivial_2_c A B⟩
    · rcases eq_dec_points_c X Y with rfl | hXY
      · right
        rfl
      · left
        apply perp_sym_c
        obtain ⟨hBX, hBY⟩ := midpoint_distinct_1_c B X Y hXY h₂
        apply col_per_perp_c A B X Y hAB hBX (Ne.symm hBY) (Ne.symm hXY) (midpoint_col_c X B Y h₂)
        exact ⟨Y, h₂, h₁⟩

theorem col_image_spec__eq_c (A B P P' : Tpoint)
    (h₁ : Col A B P) (h₂ : ReflectL P P' A B) : P = P' :=
  l10_6_uniqueness_spec_c A B P P P' (col__image_spec_c A B P h₁) h₂

theorem image_spec_triv_c (A B : Tpoint) : ReflectL A A B B :=
  col__image_spec_c B B A (col_trivial_1_c B A)

theorem image_spec__eq_c (A P P' : Tpoint) (h : ReflectL P P' A A) : P = P' := sorry

theorem image__midpoint_c (A P P' : Tpoint) (h : Reflect P P' A A) :
    Midpoint A P' P := by
  rcases h with H0 | H0
  · obtain ⟨H1, _⟩ := H0
    exact ((H1 rfl)).elim
  · obtain ⟨_, H1⟩ := H0
    exact H1

theorem is_image_spec_dec_c (A B C D : Tpoint) :
    ReflectL A B C D ∨ ¬ ReflectL A B C D := sorry

theorem l10_14_c (P P' A B : Tpoint) (hPP' : P ≠ P') (hAB : A ≠ B)
    (h : Reflect P P' A B) : TS A B P P' := sorry

theorem l10_15_c (A B C P : Tpoint)
    (hCol : Col A B C) (hNCol : ¬ Col A B P) :
    ∃ Q, Perp A B Q C ∧ OS A B P Q := sorry

theorem ex_per_cong_c (A B C D X Y : Tpoint)
    (hAB : A ≠ B) (hXY : X ≠ Y) (hCol : Col A B C) (hNCol : ¬ Col A B D) :
    ∃ P, Per P C A ∧ Cong P C X Y ∧ OS A B P D := sorry

theorem exists_cong_per_c (A B X Y : Tpoint) :
    ∃ C, Per A B C ∧ Cong B C X Y := sorry

#print axioms GeocoqTranslate.Tarski.Base.cong_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.cong_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_left_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_right_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3421_c
#print axioms GeocoqTranslate.Tarski.Base.cong_4312_c
#print axioms GeocoqTranslate.Tarski.Base.cong_4321_c
#print axioms GeocoqTranslate.Tarski.Base.cong_trivial_identity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_reverse_identity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_2134_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_1243_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_2143_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_3412_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_4312_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_3421_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_4321_c
#print axioms GeocoqTranslate.Tarski.Base.five_segment_with_def_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_3_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_4_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_sym_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_swap_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_swap_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.eq_dec_points_c
#print axioms GeocoqTranslate.Tarski.Base.distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l2_11_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cong3_c
#print axioms GeocoqTranslate.Tarski.Base.construction_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.Cong_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Cong_perm_c
#print axioms GeocoqTranslate.Tarski.Base.bet_col_c
#print axioms GeocoqTranslate.Tarski.Base.between_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.between_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.Bet_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Bet_perm_c
#print axioms GeocoqTranslate.Tarski.Base.between_trivial2_c
#print axioms GeocoqTranslate.Tarski.Base.between_equality_c
#print axioms GeocoqTranslate.Tarski.Base.between_equality_2_c
#print axioms GeocoqTranslate.Tarski.Base.between_exchange3_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq12__neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq21__neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq23__neq_c
#print axioms GeocoqTranslate.Tarski.Base.bet_neq32__neq_c
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
#print axioms GeocoqTranslate.Tarski.Base.l4_2_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_1_c
#print axioms GeocoqTranslate.Tarski.Base.l4_5_c
#print axioms GeocoqTranslate.Tarski.Base.l4_6_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_bet_eq_c
#print axioms GeocoqTranslate.Tarski.Base.l5_1_c
#print axioms GeocoqTranslate.Tarski.Base.l5_2_c
#print axioms GeocoqTranslate.Tarski.Base.segment_construction_2_c
#print axioms GeocoqTranslate.Tarski.Base.l5_3_c
#print axioms GeocoqTranslate.Tarski.Base.bet3__bet_c
#print axioms GeocoqTranslate.Tarski.Base.le_bet_c
#print axioms GeocoqTranslate.Tarski.Base.l5_5_1_c
#print axioms GeocoqTranslate.Tarski.Base.l5_5_2_c
#print axioms GeocoqTranslate.Tarski.Base.l5_6_c
#print axioms GeocoqTranslate.Tarski.Base.le_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.le_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.between_cong_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.between_cong_2_c
#print axioms GeocoqTranslate.Tarski.Base.between_cong_3_c
#print axioms GeocoqTranslate.Tarski.Base.le_anti_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.cong_dec_c
#print axioms GeocoqTranslate.Tarski.Base.bet_dec_c
#print axioms GeocoqTranslate.Tarski.Base.col_dec_c
#print axioms GeocoqTranslate.Tarski.Base.le_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.le_cases_c
#print axioms GeocoqTranslate.Tarski.Base.le_zero_c
#print axioms GeocoqTranslate.Tarski.Base.le_diff_c
#print axioms GeocoqTranslate.Tarski.Base.lt_diff_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cong_eq_c
#print axioms GeocoqTranslate.Tarski.Base.cong__le_c
#print axioms GeocoqTranslate.Tarski.Base.cong__le3412_c
#print axioms GeocoqTranslate.Tarski.Base.le1221_c
#print axioms GeocoqTranslate.Tarski.Base.le_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.le_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.le_comm_c
#print axioms GeocoqTranslate.Tarski.Base.ge_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.ge_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.ge_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lt_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lt_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lt_comm_c
#print axioms GeocoqTranslate.Tarski.Base.gt_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.gt_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.gt_comm_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_lt__lt_c
#print axioms GeocoqTranslate.Tarski.Base.fourth_point_c
#print axioms GeocoqTranslate.Tarski.Base.third_point_c
#print axioms GeocoqTranslate.Tarski.Base.l5_12_a_c
#print axioms GeocoqTranslate.Tarski.Base.bet__le1213_c
#print axioms GeocoqTranslate.Tarski.Base.bet__le2313_c
#print axioms GeocoqTranslate.Tarski.Base.bet__lt1213_c
#print axioms GeocoqTranslate.Tarski.Base.bet__lt2313_c
#print axioms GeocoqTranslate.Tarski.Base.l5_12_b_c
#print axioms GeocoqTranslate.Tarski.Base.bet_le_eq_c
#print axioms GeocoqTranslate.Tarski.Base.or_lt_cong_gt_c
#print axioms GeocoqTranslate.Tarski.Base.lt__le_c
#print axioms GeocoqTranslate.Tarski.Base.le1234_lt__lt_c
#print axioms GeocoqTranslate.Tarski.Base.le3456_lt__lt_c
#print axioms GeocoqTranslate.Tarski.Base.lt_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.not_and_lt_c
#print axioms GeocoqTranslate.Tarski.Base.nlt_c
#print axioms GeocoqTranslate.Tarski.Base.le__nlt_c
#print axioms GeocoqTranslate.Tarski.Base.cong__nlt_c
#print axioms GeocoqTranslate.Tarski.Base.nlt__le_c
#print axioms GeocoqTranslate.Tarski.Base.lt__nle_c
#print axioms GeocoqTranslate.Tarski.Base.nle__lt_c
#print axioms GeocoqTranslate.Tarski.Base.lt1123_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2__le_c
#print axioms GeocoqTranslate.Tarski.Base.Le_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Lt_cases_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_dec_c
#print axioms GeocoqTranslate.Tarski.Base.out_diff1_c
#print axioms GeocoqTranslate.Tarski.Base.out_diff2_c
#print axioms GeocoqTranslate.Tarski.Base.out_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.out_col_c
#print axioms GeocoqTranslate.Tarski.Base.l6_2_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out__bet_c
#print axioms GeocoqTranslate.Tarski.Base.l6_3_1_c
#print axioms GeocoqTranslate.Tarski.Base.l6_3_2_c
#print axioms GeocoqTranslate.Tarski.Base.l6_4_1_c
#print axioms GeocoqTranslate.Tarski.Base.l6_4_2_c
#print axioms GeocoqTranslate.Tarski.Base.out_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.l6_6_c
#print axioms GeocoqTranslate.Tarski.Base.l6_7_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_out_bet_c
#print axioms GeocoqTranslate.Tarski.Base.out2_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.l6_11_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l6_11_existence_c
#print axioms GeocoqTranslate.Tarski.Base.segment_construction_3_c
#print axioms GeocoqTranslate.Tarski.Base.l6_13_1_c
#print axioms GeocoqTranslate.Tarski.Base.l6_13_2_c
#print axioms GeocoqTranslate.Tarski.Base.l6_16_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_transitivity_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_transitivity_2_c
#print axioms GeocoqTranslate.Tarski.Base.l6_21_c
#print axioms GeocoqTranslate.Tarski.Base.col2__eq_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_exists_c
#print axioms GeocoqTranslate.Tarski.Base.col3_c
#print axioms GeocoqTranslate.Tarski.Base.colx_c
#print axioms GeocoqTranslate.Tarski.Base.out2__bet_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2__le1346_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2__le2356_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2__le1245_c
#print axioms GeocoqTranslate.Tarski.Base.cong_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.out_cong_cong_c
#print axioms GeocoqTranslate.Tarski.Base.not_out_bet_c
#print axioms GeocoqTranslate.Tarski.Base.or_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.not_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.not_bet_and_out_c
#print axioms GeocoqTranslate.Tarski.Base.out_to_bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_out2_col_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_out_out_c
#print axioms GeocoqTranslate.Tarski.Base.bet2__out_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet_out_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet_out_2_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet__out_c
#print axioms GeocoqTranslate.Tarski.Base.segment_reverse_c
#print axioms GeocoqTranslate.Tarski.Base.diff_col_ex_c
#print axioms GeocoqTranslate.Tarski.Base.diff_bet_ex3_c
#print axioms GeocoqTranslate.Tarski.Base.diff_col_ex3_c
#print axioms GeocoqTranslate.Tarski.Base.Out_cases_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_dec_c
#print axioms GeocoqTranslate.Tarski.Base.is_midpoint_id_c
#print axioms GeocoqTranslate.Tarski.Base.is_midpoint_id_2_c
#print axioms GeocoqTranslate.Tarski.Base.l7_2_c
#print axioms GeocoqTranslate.Tarski.Base.l7_3_c
#print axioms GeocoqTranslate.Tarski.Base.l7_3_2_c
#print axioms GeocoqTranslate.Tarski.Base.symmetric_point_construction_c
#print axioms GeocoqTranslate.Tarski.Base.symmetric_point_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l7_9_c
#print axioms GeocoqTranslate.Tarski.Base.l7_9_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l7_13_c
#print axioms GeocoqTranslate.Tarski.Base.l7_15_c
#print axioms GeocoqTranslate.Tarski.Base.l7_16_c
#print axioms GeocoqTranslate.Tarski.Base.symmetry_preserves_midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.Mid_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Mid_perm_c
#print axioms GeocoqTranslate.Tarski.Base.l7_17_c
#print axioms GeocoqTranslate.Tarski.Base.l7_17_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l7_20_c
#print axioms GeocoqTranslate.Tarski.Base.l7_20_bis_c
#print axioms GeocoqTranslate.Tarski.Base.cong_col_mid_c
#print axioms GeocoqTranslate.Tarski.Base.l7_21_c
#print axioms GeocoqTranslate.Tarski.Base.l7_22_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l7_22_c
#print axioms GeocoqTranslate.Tarski.Base.bet_col1_c
#print axioms GeocoqTranslate.Tarski.Base.l7_25_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_distinct_1_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_distinct_2_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_distinct_3_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_def_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_bet_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_col_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_cong_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_out_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_out_1_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_not_midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.swap_diff_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cong_half_1_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cong_half_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong_mid2__cong_c
#print axioms GeocoqTranslate.Tarski.Base.mid__lt_c
#print axioms GeocoqTranslate.Tarski.Base.le_mid2__le13_c
#print axioms GeocoqTranslate.Tarski.Base.le_mid2__le12_c
#print axioms GeocoqTranslate.Tarski.Base.lt_mid2__lt13_c
#print axioms GeocoqTranslate.Tarski.Base.lt_mid2__lt12_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong_bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet1_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet2_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet3_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet4_c
#print axioms GeocoqTranslate.Tarski.Base.col_bet2_cong1_c
#print axioms GeocoqTranslate.Tarski.Base.col_bet2_cong2_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lt2__lt_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lt_le__lt_c
#print axioms GeocoqTranslate.Tarski.Base.per_dec_c
#print axioms GeocoqTranslate.Tarski.Base.l8_2_c
#print axioms GeocoqTranslate.Tarski.Base.Per_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Per_perm_c
#print axioms GeocoqTranslate.Tarski.Base.l8_3_c
#print axioms GeocoqTranslate.Tarski.Base.l8_4_c
#print axioms GeocoqTranslate.Tarski.Base.l8_5_c
#print axioms GeocoqTranslate.Tarski.Base.l8_6_c
#print axioms GeocoqTranslate.Tarski.Base.l8_7_c
#print axioms GeocoqTranslate.Tarski.Base.l8_8_c
#print axioms GeocoqTranslate.Tarski.Base.per_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.per_distinct_1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_9_c
#print axioms GeocoqTranslate.Tarski.Base.l8_10_c
#print axioms GeocoqTranslate.Tarski.Base.col_col_per_per_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_dec_c
#print axioms GeocoqTranslate.Tarski.Base.perp_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l8_12_c
#print axioms GeocoqTranslate.Tarski.Base.per_col_c
#print axioms GeocoqTranslate.Tarski.Base.l8_13_2_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_2_1a_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_2_1b_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_2_1b_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_2_2_c
#print axioms GeocoqTranslate.Tarski.Base.l8_14_3_c
#print axioms GeocoqTranslate.Tarski.Base.l8_15_1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_15_2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_per_c
#print axioms GeocoqTranslate.Tarski.Base.perp_sym_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col0_c
#print axioms GeocoqTranslate.Tarski.Base.per_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.per_perp_c
#print axioms GeocoqTranslate.Tarski.Base.perp_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_sym_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_comm_c
#print axioms GeocoqTranslate.Tarski.Base.Perp_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Perp_perm_c
#print axioms GeocoqTranslate.Tarski.Base.Perp_in_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Perp_in_perm_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_col_c
#print axioms GeocoqTranslate.Tarski.Base.perp_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.perp_per_1_c
#print axioms GeocoqTranslate.Tarski.Base.perp_per_2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col4_c
#print axioms GeocoqTranslate.Tarski.Base.perp_not_eq_1_c
#print axioms GeocoqTranslate.Tarski.Base.perp_not_eq_2_c
#print axioms GeocoqTranslate.Tarski.Base.diff_per_diff_c
#print axioms GeocoqTranslate.Tarski.Base.per_not_colp_c
#print axioms GeocoqTranslate.Tarski.Base.per_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.perp_not_col2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_col_perp_in_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col2_bis_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_perp_bis_c
#print axioms GeocoqTranslate.Tarski.Base.col_per_perp_c
#print axioms GeocoqTranslate.Tarski.Base.per_cong_mid_c
#print axioms GeocoqTranslate.Tarski.Base.per_double_cong_c
#print axioms GeocoqTranslate.Tarski.Base.cong_perp_or_mid_c
#print axioms GeocoqTranslate.Tarski.Base.col_per2_cases_c
#print axioms GeocoqTranslate.Tarski.Base.l8_16_1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_16_2_c
#print axioms GeocoqTranslate.Tarski.Base.l8_18_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l8_20_1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_20_2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_col1_c
#print axioms GeocoqTranslate.Tarski.Base.l8_18_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_c
#print axioms GeocoqTranslate.Tarski.Base.per_cong_c
#print axioms GeocoqTranslate.Tarski.Base.perp_cong_c
#print axioms GeocoqTranslate.Tarski.Base.perp_exists_c
#print axioms GeocoqTranslate.Tarski.Base.perp_vector_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_existence_aux_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_existence_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_id_c
#print axioms GeocoqTranslate.Tarski.Base.l8_22_c
#print axioms GeocoqTranslate.Tarski.Base.l8_22_bis_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_perp_c
#print axioms GeocoqTranslate.Tarski.Base.perp_proj_c
#print axioms GeocoqTranslate.Tarski.Base.l8_24_c
#print axioms GeocoqTranslate.Tarski.Base.col_per2__per_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_per_1_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_per_2_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_per_3_c
#print axioms GeocoqTranslate.Tarski.Base.perp_in_per_4_c
#print axioms GeocoqTranslate.Tarski.Base.ts_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.l9_2_c
#print axioms GeocoqTranslate.Tarski.Base.mid_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.per_mid_per_c
#print axioms GeocoqTranslate.Tarski.Base.sym_preserve_diff_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_1_aux_c
#print axioms GeocoqTranslate.Tarski.Base.per_col_eq_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_1_c
#print axioms GeocoqTranslate.Tarski.Base.mid_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.col_preserves_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.out_out_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_2_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_2_c
#print axioms GeocoqTranslate.Tarski.Base.l9_5_c
#print axioms GeocoqTranslate.Tarski.Base.outer_pasch_c
#print axioms GeocoqTranslate.Tarski.Base.os_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.invert_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.l9_8_1_c
#print axioms GeocoqTranslate.Tarski.Base.not_two_sides_id_c
#print axioms GeocoqTranslate.Tarski.Base.l9_8_2_c
#print axioms GeocoqTranslate.Tarski.Base.l9_9_c
#print axioms GeocoqTranslate.Tarski.Base.l9_9_bis_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_chara_c
#print axioms GeocoqTranslate.Tarski.Base.l9_10_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.l9_17_c
#print axioms GeocoqTranslate.Tarski.Base.l9_18_c
#print axioms GeocoqTranslate.Tarski.Base.l9_19_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_not_col123_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_not_col124_c
#print axioms GeocoqTranslate.Tarski.Base.col_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.col_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.out_out_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.out_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.bet__ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet_ts__ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet_ts__os_c
#print axioms GeocoqTranslate.Tarski.Base.l9_31_c
#print axioms GeocoqTranslate.Tarski.Base.col123__nos_c
#print axioms GeocoqTranslate.Tarski.Base.col124__nos_c
#print axioms GeocoqTranslate.Tarski.Base.col2_os__os_c
#print axioms GeocoqTranslate.Tarski.Base.os_out_os_c
#print axioms GeocoqTranslate.Tarski.Base.ts_ts_os_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.col_one_side_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_two_sides_bet_c
#print axioms GeocoqTranslate.Tarski.Base.os_ts1324__os_c
#print axioms GeocoqTranslate.Tarski.Base.ts2__ex_bet2_c
#print axioms GeocoqTranslate.Tarski.Base.out_one_side_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_two_sides_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_bis_c
#print axioms GeocoqTranslate.Tarski.Base.ts__ncol_c
#print axioms GeocoqTranslate.Tarski.Base.one_or_two_sides_aux_c
#print axioms GeocoqTranslate.Tarski.Base.cop__one_or_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.os__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_trans_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.col2_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop2__cop_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop2__cop_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_pseudo_trans_c
#print axioms GeocoqTranslate.Tarski.Base.l9_30_c
#print axioms GeocoqTranslate.Tarski.Base.cop_per2__col_c
#print axioms GeocoqTranslate.Tarski.Base.cop_perp2__col_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_dec_c
#print axioms GeocoqTranslate.Tarski.Base.cop_nts__os_c
#print axioms GeocoqTranslate.Tarski.Base.cop_nos__ts_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_dec_c
#print axioms GeocoqTranslate.Tarski.Base.cop_dec_c
#print axioms GeocoqTranslate.Tarski.Base.ex_diff_cop_c
#print axioms GeocoqTranslate.Tarski.Base.ex_ncol_cop_c
#print axioms GeocoqTranslate.Tarski.Base.ex_ncol_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.col2_cop2__eq_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_cop2__col_c
#print axioms GeocoqTranslate.Tarski.Base.l9_38_c
#print axioms GeocoqTranslate.Tarski.Base.l9_39_c
#print axioms GeocoqTranslate.Tarski.Base.l9_41_1_c
#print axioms GeocoqTranslate.Tarski.Base.l9_41_2_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_exists_c
#print axioms GeocoqTranslate.Tarski.Base.osp_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.osp_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.osp_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_tsp__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_osp__osp_c
#print axioms GeocoqTranslate.Tarski.Base.ncop_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.osp_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__nosp_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ntsp_c
#print axioms GeocoqTranslate.Tarski.Base.osp_bet__osp_c
#print axioms GeocoqTranslate.Tarski.Base.l9_18_3_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop_out__osp_c
#print axioms GeocoqTranslate.Tarski.Base.l9_19_3_c
#print axioms GeocoqTranslate.Tarski.Base.cop2_ts__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop2_os__osp_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_tsp__ts_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_osp__os_c
#print axioms GeocoqTranslate.Tarski.Base.cop_tsp__ex_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.cop_osp__ex_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.sac__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.ex_sym_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_is_image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.ex_sym1_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_uniqueness_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_existence_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_2_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l10_4_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_4_c
#print axioms GeocoqTranslate.Tarski.Base.l10_5_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_uniqueness_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_existence_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_6_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l10_7_c
#print axioms GeocoqTranslate.Tarski.Base.l10_8_c
#print axioms GeocoqTranslate.Tarski.Base.col__refl_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_col_cong_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_col_cong_c
#print axioms GeocoqTranslate.Tarski.Base.image_id_c
#print axioms GeocoqTranslate.Tarski.Base.osym_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_image_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_is_image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_gen_is_image_c
#print axioms GeocoqTranslate.Tarski.Base.image_image_in_c
#print axioms GeocoqTranslate.Tarski.Base.image_in_col_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_rev_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_rev_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_per_c
#print axioms GeocoqTranslate.Tarski.Base.col__image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.image_triv_c
#print axioms GeocoqTranslate.Tarski.Base.cong_midpoint__image_c
#print axioms GeocoqTranslate.Tarski.Base.col_image_spec__eq_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec_triv_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec__eq_c
#print axioms GeocoqTranslate.Tarski.Base.image__midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_dec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_14_c
#print axioms GeocoqTranslate.Tarski.Base.l10_15_c
#print axioms GeocoqTranslate.Tarski.Base.ex_per_cong_c
#print axioms GeocoqTranslate.Tarski.Base.exists_cong_per_c
end GeocoqTranslate.Tarski.Base