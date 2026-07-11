import GeocoqTranslate.Tarski_dev.Ch04

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

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
    (h₃ : Le o a O A) (h₄ : Le o b O B) : Le a b A B := by
  rcases eq_dec_points_c A O with hAO | hAO
  · subst hAO
    obtain ⟨E, hBetAEA, hCong⟩ := h₃
    have hEA : E = A := (between_identity A E hBetAEA).symm
    rw [hEA] at hCong
    have hoa : o = a := cong_identity o a A hCong
    rw [hoa] at h₄
    exact h₄
  · rcases eq_dec_points_c B O with hBO | hBO
    · subst hBO
      obtain ⟨E, hBetBEB, hCong⟩ := h₄
      have hEB : E = B := (between_identity B E hBetBEB).symm
      rw [hEB] at hCong
      have hob : o = b := cong_identity o b B hCong
      rw [hob] at h₃
      exact le_right_comm_c a b B A (le_left_comm_c b a B A h₃)
    · obtain ⟨b', hBetAOb', hCongOb'bo⟩ := segment_construction A O b o
      obtain ⟨a', hBetBOa', hCongOa'ao⟩ := segment_construction B O a o
      obtain ⟨a'', hBetOa''A, hCongoaOa''⟩ := h₃
      have hBetBOa'' : Bet B O a'' :=
        between_inner_transitivity_c B O a'' A (between_symmetry_c A O B h₂) hBetOa''A
      have hCongOa''ao : Cong O a'' a o := cong_3421_c o a O a'' hCongoaOa''
      have haa' : a' = a'' :=
        construction_uniqueness hBO hBetBOa' hCongOa'ao hBetBOa'' hCongOa''ao
      rw [← haa'] at hBetOa''A hCongoaOa''
      have hBetAa'O : Bet A a' O := between_symmetry_c O a' A hBetOa''A
      have hBeta'Ob' : Bet a' O b' := between_exchange3_c A a' O b' hBetAa'O hBetAOb'
      have hBetBa'A : Bet B a' A :=
        between_exchange2_c B O a' A (between_symmetry_c A O B h₂) hBetOa''A
      have hLeBa'BA : Le B a' B A := ⟨a', hBetBa'A, cong_reflexivity B a'⟩
      obtain ⟨b'', hBetOb''B, hCongobOb''⟩ := h₄
      have hBetAOb'' : Bet A O b'' :=
        between_inner_transitivity_c A O b'' B h₂ hBetOb''B
      have hCongOb''bo : Cong O b'' b o := cong_3421_c o b O b'' hCongobOb''
      have hbb' : b' = b'' :=
        construction_uniqueness hAO hBetAOb' hCongOb'bo hBetAOb'' hCongOb''bo
      rw [← hbb'] at hBetOb''B hCongobOb''
      have hBeta'OB : Bet a' O B := between_symmetry_c B O a' hBetBOa'
      have hBeta'b'B : Bet a' b' B := between_exchange2_c a' O b' B hBeta'OB hBetOb''B
      have hLea'b'a'B : Le a' b' a' B := ⟨b', hBeta'b'B, cong_reflexivity a' b'⟩
      have hLea'BAB : Le a' B A B :=
        le_right_comm_c a' B B A (le_left_comm_c B a' B A hLeBa'BA)
      have hLea'b'AB : Le a' b' A B :=
        le_transitivity_c a' b' a' B A B hLea'b'a'B hLea'BAB
      have hConga'Oao : Cong a' O a o := cong_4321_c o a O a' hCongoaOa''
      have hCongOb'ob : Cong O b' o b := cong_symmetry_c o b O b' hCongobOb''
      have hConga'b'ab : Cong a' b' a b :=
        l2_11_c a' O b' a o b hBeta'Ob' h₁ hConga'Oao hCongOb'ob
      exact l5_6_c a' b' A B a b A B hLea'b'AB hConga'b'ab (cong_reflexivity A B)

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

end GeocoqTranslate.Tarski.Base
