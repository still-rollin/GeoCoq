import GeocoqTranslate.Tarski_dev.ColCongInstances

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

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
    have hAX : A ≠ X := bet_neq12_neq_c A P X hBetAPX (Ne.symm hPA)
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

theorem cong_mid2_cong_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A M A' M') : Cong A B A' B' := by
  obtain ⟨x, x0⟩ := h₁
  obtain ⟨x1, x2⟩ := h₂
  exact l2_11 x x1 h₃ (cong_transitivity (cong_transitivity (cong_symmetry x0) h₃) x2)

theorem mid_lt_c (A M B : Tpoint) (hAB : A ≠ B) (h : Midpoint M A B) :
    Lt A M A B := by
  have a := midpoint_distinct_1_c M A B hAB h
  obtain ⟨x, x0⟩ := a
  obtain ⟨x1, x2⟩ := h
  exact ⟨(⟨M, (⟨x1, (cong_reflexivity A M)⟩)⟩), ((fun H1 => x0 (between_cong_c A B M x1 H1)))⟩

theorem le_mid2_le13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A M A' M') : Le A B A' B' := by
  obtain ⟨x, x0⟩ := h₁
  obtain ⟨x1, x2⟩ := h₂
  exact bet2_le2_le1346_c A M B A' M' B' x x1 h₃ (l5_6_c A M A' M' M B M' B' h₃ x0 x2)

theorem le_mid2_le12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A B A' B') : Le A M A' M' := by
  rcases (le_cases_c A M A' M') with H | H
  · exact H
  · have H0 := le_mid2_le13_c A' M' B' A M B h₂ h₁ H
    exact cong_le_c A M A' M' (cong_cong_half_1_c A M B A' M' B' h₁ h₂ (le_anti_symmetry_c A B A' B' h₃ H0))

theorem lt_mid2_lt13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A M A' M') : Lt A B A' B' := by
  obtain ⟨x, x0⟩ := h₃
  exact ⟨(le_mid2_le13_c A M B A' M' B' h₁ h₂ x), ((fun H0 => x0 (cong_cong_half_1_c A M B A' M' B' h₁ h₂ H0)))⟩

theorem lt_mid2_lt12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A B A' B') : Lt A M A' M' := by
  obtain ⟨x, x0⟩ := h₃
  exact ⟨(le_mid2_le12_c A M B A' M' B' h₁ h₂ x), ((fun H0 => x0 (cong_mid2_cong_c A M B A' M' B' h₁ h₂ H0)))⟩

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
    Bet C A D ∨ Bet C B D := by
  obtain ⟨D1, hBetBAD1, hCongAD1BC⟩ := segment_construction B A B C
  obtain ⟨D2, hBetABD2, hCongBD2AC⟩ := segment_construction A B A C
  have hBetCAD1 : Bet C A D1 :=
    between_exchange3_c B C A D1 (between_symmetry_c A C B hBet) hBetBAD1
  have hCongABCD1 : Cong A B C D1 :=
    l2_11_c A C B C A D1 hBet hBetCAD1 (cong_pseudo_reflexivity A C)
      (cong_left_commutativity_c B C A D1 (cong_symmetry_c A D1 B C hCongAD1BC))
  rcases eq_dec_points_c A B with hAB | hAB
  · subst hAB
    have hCD : C = D := cong_identity C D A (cong_symmetry_c A A C D hCong)
    subst hCD
    exact Or.inl (by
      have hAC : A = C := between_identity A C hBet
      rw [← hAC]
      exact between_trivial_c A A)
  · have hColDCD1 : Col D C D1 :=
      col3_c A B D C D1 hAB hCol
        (col_permutation_5_c A C B (bet_col_c A C B hBet))
        (col_permutation_4_c B A D1 (bet_col_c B A D1 hBetBAD1))
    have hCongCDCD1 : Cong C D C D1 :=
      cong_transitivity_c C D A B C D1 (cong_symmetry_c A B C D hCong) hCongABCD1
    rcases l7_20_c C D D1 hColDCD1 hCongCDCD1 with hDD1 | hMid
    · exact Or.inl (by rw [hDD1]; exact hBetCAD1)
    · rcases eq_dec_points_c A C with hAC | hAC
      · subst hAC
        exact Or.inl (between_trivial2_c A D)
      · have hBetABD2' : Bet C B D2 :=
          between_exchange3_c A C B D2 hBet hBetABD2
        have hCongBACD2 : Cong B A C D2 :=
          l2_11_c B C A C B D2 (between_symmetry_c A C B hBet) hBetABD2'
            (cong_pseudo_reflexivity B C)
            (cong_left_commutativity_c A C B D2 (cong_symmetry_c B D2 A C hCongBD2AC))
        have hBetD1CB : Bet D1 C B :=
          outer_transitivity_between2_c D1 A C B
            (between_symmetry_c C A D1 hBetCAD1) hBet hAC
        rcases eq_dec_points_c B C with hBC | hBC
        · subst hBC
          exact Or.inr (between_trivial2_c B D)
        · have hBetD1CD2 : Bet D1 C D2 :=
            outer_transitivity_between_c D1 C B D2 hBetD1CB hBetABD2' (Ne.symm hBC)
          have hCongCDCD2 : Cong C D C D2 :=
            cong_transitivity_c C D A B C D2 (cong_symmetry_c A B C D hCong)
              (cong_left_commutativity_c B A C D2 hCongBACD2)
          have hCongD2CCD1 : Cong D2 C C D1 :=
            cong_transitivity_c D2 C C D C D1
              (cong_left_commutativity_c C D2 C D (cong_symmetry_c C D C D2 hCongCDCD2))
              (cong_left_commutativity_c D C C D1 hMid.2)
          have hMidCD2D1 : Midpoint C D2 D1 :=
            ⟨between_symmetry_c D1 C D2 hBetD1CD2, hCongD2CCD1⟩
          have hDD2 : D = D2 :=
            symmetric_point_uniqueness_c D1 C D D2 (l7_2_c C D D1 hMid) (l7_2_c C D2 D1 hMidCD2D1)
          exact Or.inr (by rw [hDD2]; exact hBetABD2')

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
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet B C D := by
  rcases point_equality_decidability A B with e | hAB
  · subst e
    have hCD : C = D := cong_identity C D A (cong_symmetry_c A A C D h₁)
    subst hCD
    exact between_trivial_c A C
  · have hColCAD : Col C A D := by
      have hColABC : Col A B C := bet_col_c A B C hBet
      show Col C A D
      colr
    have hBetCBA : Bet C B A := between_symmetry_c A B C hBet
    have hCongCABD : Cong C A B D := by cong_r
    have hCongCDAB : Cong C D A B := by cong_r
    exact col_cong2_bet2_c C A B D hColCAD hBetCBA hCongCABD hCongCDAB

theorem col_cong2_bet4_c (A B C D : Tpoint)
    (hCol : Col A B C) (hBet : Bet A B D)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet B D C := by
  rcases point_equality_decidability A B with e | hAB
  · subst e
    have hCD : C = D := cong_identity C D A (cong_symmetry_c A A C D h₁)
    subst hCD
    exact between_trivial_c A C
  · have hColADC : Col A D C := by
      have hColABD : Col A B D := bet_col_c A B D hBet
      show Col A D C
      colr
    exact col_cong2_bet1_c A D B C hColADC hBet h₂ (cong_right_commutativity_c A B C D h₁)

theorem col_bet2_cong1_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C B D) : Cong A C D B :=
  l4_3 hBet (between_symmetry h₂) (cong_symmetry (cong_symmetry (cong_right_commutativity h₁))) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C B))))

theorem col_bet2_cong2_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C A D) : Cong D A B C :=
  l4_3 (between_symmetry h₂) (between_symmetry hBet) (cong_symmetry (cong_symmetry (cong_4321_c A B C D h₁))) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity A C))))

theorem bet2_lt2_lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Lt o a O A) (h₄ : Lt o b O B) : Lt a b A B := by
  refine ⟨bet2_le2_le_c O o A B a b h₁ h₂ h₃.1 h₄.1, ?_⟩
  intro hCong
  rcases eq_dec_points_c O A with hOA | hOA
  · rw [hOA] at h₃
    have hoa : o = a := le_zero_c o a A h₃.1
    refine absurd ?_ h₃.2
    rw [hoa]; exact cong_trivial_identity_c a A
  · rcases eq_dec_points_c O B with hOB | hOB
    · rw [hOB] at h₄
      have hob : o = b := le_zero_c o b B h₄.1
      refine absurd ?_ h₄.2
      rw [hob]; exact cong_trivial_identity_c b B
    · obtain ⟨a', hBetOa'A, hCongoaOa'⟩ := h₃.1
      obtain ⟨b', hBetOb'B, hCongobOb'⟩ := h₄.1
      have hBeta'Ob' : Bet a' O b' :=
        between_inner_transitivity_c a' O b' B
          (between_exchange3_c A a' O B (between_symmetry_c O a' A hBetOa'A) h₂) hBetOb'B
      have hCongABa'b' : Cong a b a' b' :=
        l2_11_c a o b a' O b' h₁ hBeta'Ob'
          (cong_commutativity_c o a O a' hCongoaOa') hCongobOb'
      have hConga'b'AB : Cong a' b' A B :=
        cong_transitivity_c a' b' a b A B (cong_symmetry_c a b a' b' hCongABa'b') hCong
      have hBetAb'B : Bet A b' B := between_exchange2_c A O b' B h₂ hBetOb'B
      have hBetAa'B : Bet A a' B :=
        between_exchange4_c A a' O B (between_symmetry_c O a' A hBetOa'A) h₂
      rcases eq_dec_points_c A a' with hAa' | hAa'
      · have hCongAb'AB : Cong A b' A B := by
          have h := hConga'b'AB; rw [← hAa'] at h; exact h
        have hb'B : b' = B := between_cong_c A B b' hBetAb'B hCongAb'AB
        exact h₄.2 (by rw [hb'B] at hCongobOb'; exact hCongobOb')
      · rcases eq_dec_points_c B b' with hBb' | hBb'
        · have hCongBa'BA : Cong B a' B A := by
            have h := hConga'b'AB; rw [← hBb'] at h; exact cong_commutativity_c a' B A B h
          have hBetBa'A : Bet B a' A := between_symmetry_c A a' B hBetAa'B
          have ha'A : a' = A := between_cong_c B A a' hBetBa'A hCongBa'BA
          exact h₃.2 (by rw [ha'A] at hCongoaOa'; exact hCongoaOa')
        · have hColABb' : Col A B b' := by
            have hc : Col A b' B := bet_col_c A b' B hBetAb'B
            colr
          have hBetAOb' : Bet A O b' := between_inner_transitivity_c A O b' B h₂ hBetOb'B
          have hBetAa'b' : Bet A a' b' :=
            between_exchange4_c A a' O b' (between_symmetry_c O a' A hBetOa'A) hBetAOb'
          rcases col_cong_bet_c A B a' b' hColABb'
              (cong_symmetry_c a' b' A B hConga'b'AB) hBetAa'B with hc1 | hc2
          · exact hAa' (between_equality_c A a' b' hBetAa'b' hc1)
          · have hBetBOa' : Bet B O a' :=
              between_inner_transitivity_c B O a' A (between_symmetry_c A O B h₂) hBetOa'A
            have hBetBb'a' : Bet B b' a' :=
              between_exchange4_c B b' O a' (between_symmetry_c O b' B hBetOb'B) hBetBOa'
            exact hBb' (between_equality_c b' B a'
              (between_symmetry_c a' B b' hc2) hBetBb'a').symm

theorem bet2_lt_le_lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Cong o a O A) (h₄ : Lt o b O B) : Lt a b A B := by
  obtain ⟨h_le, h_ncong⟩ := h₄
  constructor
  · have h_le_oa : Le o a O A := ⟨A, between_trivial_c O A, h₃⟩
    exact bet2_le2_le_c O o A B a b h₁ h₂ h_le_oa h_le
  · intro h_cong_ab
    obtain ⟨b', hb'_bet, hb'_cong⟩ := segment_construction A O o b
    apply h_ncong
    have h_cong_oa : Cong a o A O := cong_commutativity_c o a O A h₃
    exact l4_3_1_c a o b A O B h₁ h₂ h_cong_oa h_cong_ab

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
#print axioms GeocoqTranslate.Tarski.Base.cong_mid2_cong_c
#print axioms GeocoqTranslate.Tarski.Base.mid_lt_c
#print axioms GeocoqTranslate.Tarski.Base.le_mid2_le13_c
#print axioms GeocoqTranslate.Tarski.Base.le_mid2_le12_c
#print axioms GeocoqTranslate.Tarski.Base.lt_mid2_lt13_c
#print axioms GeocoqTranslate.Tarski.Base.lt_mid2_lt12_c
#print axioms GeocoqTranslate.Tarski.Base.midpoint_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong_bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet1_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet2_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet3_c
#print axioms GeocoqTranslate.Tarski.Base.col_cong2_bet4_c
#print axioms GeocoqTranslate.Tarski.Base.col_bet2_cong1_c
#print axioms GeocoqTranslate.Tarski.Base.col_bet2_cong2_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lt2_lt_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lt_le_lt_c

end GeocoqTranslate.Tarski.Base
