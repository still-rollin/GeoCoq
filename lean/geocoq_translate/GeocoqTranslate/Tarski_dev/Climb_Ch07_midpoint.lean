import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem midpoint_dec_c (I A B : Tpoint) : Midpoint I A B ∨ ¬ Midpoint I A B := sorry

theorem is_midpoint_id_c (A B : Tpoint) (h : Midpoint A A B) : A = B := by
  obtain ⟨H0, H1⟩ := h
  have H2 := cong_symmetry H1
  have H3 := cong_identity A B A H2
  exact eq_ind A (fun B0 => Bet A A B0 - > A = B0) (fun _ => eq_refl) B H3 H0

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
  exact eq_ind A (fun M0 => Cong A M0 M0 A - > M0 = A) (fun _ => eq_refl) M H2 H1

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
  · exact eq_ind A (fun P0 => Bet A P0 P₁ - > Cong A P0 P0 P₁ - > Bet A P0 P₂ - > Cong A P0 P0 P₂ - > P₁ = P₂) (fun _ H6 _ H7 => (let H8 := cong_symmetry H6; (let H9 := cong_identity A P₁ A H8; eq_ind A (fun P3 => P3 = P₂) ((let H10 := cong_symmetry H7; (let H11 := cong_identity A P₂ A H10; eq_ind A (fun P3 => A = P3) eq_refl P₂ H11))) P₁ H9))) P H5 H3 H4 H1 H2
  · exact construction_uniqueness H5 H3 (cong_symmetry H4) H1 (cong_symmetry H2)

theorem l7_9_c (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A Q X) :
    P = Q := by
  obtain ⟨H1, H2⟩ := h₂
  obtain ⟨H3, H4⟩ := h₁
  have o := point_equality_decidability A X
  rcases o with H5 | H5
  · exact eq_ind A (fun X0 => Bet P A X0 - > Cong P A A X0 - > Bet Q A X0 - > Cong Q A A X0 - > P = Q) (fun _ H6 _ H7 => (let H8 := cong_identity P A A H6; eq_ind P (fun A0 => Cong Q A0 A0 A0 - > P = Q) (fun H9 => (let H10 := cong_identity Q P P H9; eq_ind Q (fun P0 => P0 = Q) eq_refl P H10)) A H8 H7)) X H5 H3 H4 H1 H2
  · exact construction_uniqueness (Ne.symm H5) (between_symmetry H3) (cong_symmetry (cong_symmetry (cong_commutativity H4))) (between_symmetry H1) (cong_symmetry (cong_symmetry (cong_commutativity H2)))

theorem l7_9_bis_c (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A X Q) :
    P = Q := sorry

theorem l7_13_c (A P Q P' Q' : Tpoint)
    (h₁ : Midpoint A P' P) (h₂ : Midpoint A Q' Q) : Cong P Q P' Q' := sorry

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
    Midpoint A B C ∧ Midpoint A C B := sorry

theorem l7_17_c (P P' A B : Tpoint) (h₁ : Midpoint A P P') (h₂ : Midpoint B P P') :
    A = B := sorry

theorem l7_17_bis_c (P P' A B : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint B P' P) : A = B :=
  l7_17_c P P' A B h₁ (l7_2_c B P' P h₂)

theorem l7_20_c (M A B : Tpoint) (hCol : Col A M B) (hCong : Cong M A M B) :
    A = B ∨ Midpoint M A B := sorry

theorem l7_20_bis_c (M A B : Tpoint) (hAB : A ≠ B)
    (hCol : Col A M B) (hCong : Cong M A M B) : Midpoint M A B := by
  have o := l7_20_c M A B hCol hCong
  rcases o with H2 | H2
  · have H3 := hAB H2
    exact False_ind (Midpoint M A B) H3
  · exact H2

theorem cong_col_mid_c (A B C : Tpoint) (hAC : A ≠ C)
    (hCol : Col A B C) (hCong : Cong A B B C) : Midpoint B A C := by
  have H2 := l7_20_c B A C hCol (cong_symmetry (cong_symmetry (cong_left_commutativity hCong)))
  rcases H2 with H3 | H3
  · have H4 := hAC H3
    exact False_ind (Midpoint B A C) H4
  · exact H3

theorem l7_21_c (A B C D P : Tpoint)
    (hNCol : ¬ Col A B C) (hBD : B ≠ D)
    (h₁ : Cong A B C D) (h₂ : Cong B C D A)
    (h₃ : Col A P C) (h₄ : Col B P D) :
    Midpoint P A C ∧ Midpoint P B D := sorry

theorem l7_22_aux_c (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂)
    (h₇ : Le C A₁ C A₂) : Bet M₁ C M₂ := sorry

theorem l7_22_c (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂) : Bet M₁ C M₂ := sorry

theorem bet_col1_c (A B C D : Tpoint) (h₁ : Bet A B D) (h₂ : Bet A C D) :
    Col A B C := by
  have H1 := l5_3 h₁ h₂
  rcases H1 with H2 | H2
  · exact Or.inl H2
  · exact Or.inr (Or.inl (between_symmetry H2))

theorem l7_25_c (A B C : Tpoint) (h : Cong C A C B) : ∃ X, Midpoint X A B := sorry

theorem midpoint_distinct_1_c (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    I ≠ A ∧ I ≠ B := sorry

theorem midpoint_distinct_2_c (I A B : Tpoint) (hIA : I ≠ A) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ B := sorry

theorem midpoint_distinct_3_c (I A B : Tpoint) (hIB : I ≠ B) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ A := sorry

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
  exact ⟨((let H1 := midpoint_distinct_1_c B A C hAC h; and_ind (fun H2 _ => H2) H1)), (⟨(Ne.symm hAC), (Or.inl (midpoint_bet_c A B C h))⟩)⟩

theorem midpoint_out_1_c (A B C : Tpoint) (hAC : A ≠ C) (h : Midpoint B A C) :
    Out C A B :=
  l6_6 (midpoint_out_c C B A (Ne.symm hAC) (l7_2_c B A C h))

theorem midpoint_not_midpoint_c (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    ¬ Midpoint B A I := sorry

theorem swap_diff_c (A B : Tpoint) (h : A ≠ B) : B ≠ A :=
  (fun H0 => h (Eq.symm H0))

theorem cong_cong_half_1_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong A M A' M' := sorry

theorem cong_cong_half_2_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong B M B' M' :=
  cong_cong_half_1_c B M A B' M' A' (l7_2_c M A B h₁) (l7_2_c M' A' B' h₂) (cong_symmetry (cong_symmetry (cong_commutativity h₃)))

theorem cong_mid2__cong_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A M A' M') : Cong A B A' B' := sorry

theorem mid__lt_c (A M B : Tpoint) (hAB : A ≠ B) (h : Midpoint M A B) :
    Lt A M A B := sorry

theorem le_mid2__le13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A M A' M') : Le A B A' B' := sorry

theorem le_mid2__le12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A B A' B') : Le A M A' M' := sorry

theorem lt_mid2__lt13_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A M A' M') : Lt A B A' B' := sorry

theorem lt_mid2__lt12_c (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A B A' B') : Lt A M A' M' := sorry

theorem midpoint_preserves_out_c (A B C A' B' C' M : Tpoint)
    (h₀ : Out A B C)
    (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') :
    Out A' B' C' := by
  obtain ⟨H3, H4⟩ := h₀
  obtain ⟨H5, H6⟩ := H4
  exact ⟨((fun H7 => eq_ind_r (fun B'0 => Midpoint M B B'0 - > False) (fun H8 => (let H9 := symmetric_point_uniqueness_c A' M A B (l7_2_c M A A' h₁) (l7_2_c M B A' H8); H3 (Eq.symm H9))) H7 h₂)), (⟨((fun H7 => eq_ind_r (fun C'0 => Midpoint M C C'0 - > False) (fun H8 => (let H9 := symmetric_point_uniqueness_c A' M A C (l7_2_c M A A' h₁) (l7_2_c M C A' H8); H5 (Eq.symm H9))) H7 h₃)), (or_ind (fun H7 => Or.inl (l7_15_c A B C A' B' C' M h₁ h₂ h₃ H7)) (fun H7 => Or.inr (l7_15_c A C B A' C' B' M h₁ h₃ h₂ H7)) H6)⟩)⟩

theorem col_cong_bet_c (A B C D : Tpoint)
    (hCol : Col A B D) (hCong : Cong A B C D) (hBet : Bet A C B) :
    Bet C A D ∨ Bet C B D := sorry

theorem col_cong2_bet1_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet C B D := sorry

theorem col_cong2_bet2_c (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet C A D := sorry

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
    (h₁ : Cong A B C D) (h₂ : Bet C A D) : Cong D A B C := sorry

theorem bet2_lt2__lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Lt o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

theorem bet2_lt_le__lt_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Cong o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

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
end GeocoqTranslate.Tarski.Base