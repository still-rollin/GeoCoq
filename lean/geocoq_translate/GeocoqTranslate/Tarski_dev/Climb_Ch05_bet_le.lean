import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l5_1_c (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet A C D ∨ Bet A D C := sorry

theorem l5_2_c (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet B C D ∨ Bet B D C := by
  have H2 := l5_1 hAB h₁ h₂
  rcases H2 with H3 | H3
  · exact Or.inl (between_symmetry (between_symmetry (between_exchange3 h₁ H3)))
  · exact Or.inr (between_symmetry (between_symmetry (between_exchange3 h₂ H3)))

theorem segment_construction_2_c (A Q B C : Tpoint) (hAQ : A ≠ Q) :
    ∃ X, (Bet Q A X ∨ Bet Q X A) ∧ Cong Q X B C := sorry

theorem l5_3_c (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet A C D) : Bet A B C ∨ Bet A C B := by
  have H1 := point_construction_different D A
  obtain ⟨P, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₁))
  have H6 := between_symmetry (between_symmetry (between_inner_transitivity (between_symmetry H3) h₂))
  exact l5_2 (Ne.symm H4) H5 H6

theorem bet3__bet_c (A B C D E : Tpoint)
    (h₁ : Bet A B E) (h₂ : Bet A D E) (h₃ : Bet B C D) : Bet A C E := sorry

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
  obtain ⟨P, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  have H3 := l4_5 H1 H2
  obtain ⟨y, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨y, (and_ind (fun H7 H8 => and_ind (fun _ _ => ⟨H5, H7⟩) H8) H6)⟩

theorem l5_6_c (A B C D A' B' C' D' : Tpoint)
    (h₁ : Le A B C D) (h₂ : Cong A B A' B') (h₃ : Cong C D C' D') :
    Le A' B' C' D' := by
  obtain ⟨y, H2⟩ := h₁
  obtain ⟨H3, H4⟩ := H2
  have H5 := l4_5 H3 h₃
  obtain ⟨z, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  exact ⟨z, (⟨H7, (and_ind (fun H9 H10 => and_ind (fun _ _ => cong_transitivity (cong_symmetry h₂) (cong_transitivity H4 H9)) H10) H8)⟩)⟩

theorem le_reflexivity_c (A B : Tpoint) : Le A B A B :=
  ⟨B, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))), (cong_reflexivity A B)⟩)⟩

theorem le_transitivity_c (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Le C D E F) : Le A B E F := by
  obtain ⟨y, H1⟩ := h₁
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨z, H4⟩ := h₂
  obtain ⟨H5, H6⟩ := H4
  have H7 := l4_5 H2 H6
  obtain ⟨P, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  exact ⟨P, (⟨(between_symmetry (between_symmetry (between_exchange4 H9 H5))), (and_ind (fun H11 H12 => and_ind (fun _ _ => cong_transitivity H3 H11) H12) H10)⟩)⟩

theorem between_cong_c (A B C : Tpoint) (hBet : Bet A C B) (hCong : Cong A C A B) :
    C = B :=
  (let H1 := l4_6 (hBet) (⟨hCong, (⟨(cong_symmetry hCong), (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C B))))⟩)⟩); between_equality (between_symmetry H1) (between_symmetry hBet))

theorem cong3_symmetry_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem between_cong_2_c (A B D E : Tpoint)
    (h₁ : Bet A D B) (h₂ : Bet A E B) (h₃ : Cong A D A E) : D = E := sorry

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

theorem cong_dec_c (A B C D : Tpoint) : Cong A B C D ∨ ¬ Cong A B C D := sorry

theorem bet_dec_c (A B C : Tpoint) : Bet A B C ∨ ¬ Bet A B C := by
  obtain ⟨C', HC'⟩ := (segment_construction A B B C)
  obtain ⟨H, H0⟩ := HC'
  rcases (point_equality_decidability C C') with H1 | H1
  · subst H1
    exact Or.inl H
  · rcases (point_equality_decidability A B) with H2 | H2
    · exact Or.inl (eq_ind_r (fun A0 => Bet A0 B C' - > Bet A0 B C) (fun _ => between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 B C))))) H2 H)
    · exact Or.inr ((fun H3 => H1 (between_cong_3_c A B C C' H2 H3 H (cong_symmetry H0))))

theorem col_dec_c (A B C : Tpoint) : Col A B C ∨ ¬ Col A B C := by
  rcases (bet_dec_c A B C) with H | H
  · rcases (bet_dec_c B C A) with _ | _
    · rcases (bet_dec_c C A B) with _ | _
      · exact Or.inl (Or.inl H)
      · exact Or.inl (Or.inl H)
    · rcases (bet_dec_c C A B) with _ | _
      · exact Or.inl (Or.inl H)
      · exact Or.inl (Or.inl H)
  · rcases (bet_dec_c B C A) with H0 | H0
    · rcases (bet_dec_c C A B) with _ | _
      · exact Or.inl (Or.inr (Or.inl H0))
      · exact Or.inl (Or.inr (Or.inl H0))
    · rcases (bet_dec_c C A B) with H1 | H1
      · exact Or.inl (Or.inr (Or.inr H1))
      · exact Or.inr ((fun H2 => or_ind (fun H3 => (let H4 := H H3; False_ind False H4)) (fun H3 => or_ind (fun H4 => (let H5 := H0 H4; False_ind False H5)) (fun H4 => (let H5 := H1 H4; False_ind False H5)) H3) H2))

theorem le_trivial_c (A C D : Tpoint) : Le A A C D :=
  ⟨C, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 C D))))), (cong_trivial_identity A C)⟩)⟩

theorem le_cases_c (A B C D : Tpoint) : Le A B C D ∨ Le C D A B := by
  have o := point_equality_decidability A B
  rcases o with H | H
  · exact eq_ind A (fun B0 => Le A B0 C D \/ Le C D A B0) (Or.inl (le_trivial_c A C D)) B H
  · have H0 := segment_construction_2_c B A C D (Ne.symm H)
    obtain ⟨X, H1⟩ := H0
    obtain ⟨H2, H3⟩ := H1
    rcases H2 with H4 | H4
    · exact Or.inl (l5_5_2_c A B C D (⟨X, (⟨H4, H3⟩)⟩))
    · exact Or.inr (⟨X, (⟨H4, (cong_symmetry H3)⟩)⟩)

theorem le_zero_c (A B C : Tpoint) (h : Le A B C C) : A = B :=
  (let H0 := le_trivial_c C A B; (let H1 := le_anti_symmetry_c A B C C h H0; (let H2 := cong_identity A B C H1; eq_ind A (fun B0 => Le A B0 C C - > Le C C A B0 - > A = B0) (fun _ _ => eq_refl) B H2 h H0)))

theorem le_diff_c (A B C D : Tpoint) (hAB : A ≠ B) (h : Le A B C D) : C ≠ D :=
  (fun Heq => eq_ind C (fun D0 => Le A B C D0 - > False) (fun HLe0 => hAB (le_zero_c A B C HLe0)) D Heq h)

theorem lt_diff_c (A B C D : Tpoint) (h : Lt A B C D) : C ≠ D := sorry

theorem bet_cong_eq_c (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) (h₃ : Cong B C A D) : C = D ∧ A = B :=
  (let H2 := (let H2 := l5_5_2_c A C A D (⟨D, (⟨h₂, (cong_reflexivity A D)⟩)⟩); (let H3 := l5_5_2_c C B C A (⟨A, (⟨(between_symmetry h₁), (cong_reflexivity C A)⟩)⟩); (let H4 := le_anti_symmetry_c A C A D H2 (l5_6_c C B C A A D A C H3 (cong_symmetry (cong_symmetry (cong_left_commutativity h₃))) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity C A))))); between_cong_c A D C h₂ H4))); ⟨H2, (eq_ind C (fun D0 => Bet A C D0 - > Cong B C A D0 - > A = B) (fun _ H3 => Eq.symm (between_cong_c C A B (between_symmetry h₁) (cong_symmetry (cong_symmetry (cong_commutativity H3))))) D H2 h₂ h₃)⟩)

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
  obtain ⟨H0, H1⟩ := h
  exact ⟨(ex_ind (fun P H2 => and_ind (fun H3 H4 => ⟨P, ((let H5 := cong_left_commutativity H4; ⟨H3, H5⟩))⟩) H2) H0), ((fun H2 => H1 (cong_left_commutativity H2)))⟩

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
    Lt A' B' C' D' := sorry

theorem fourth_point_c (A B C P : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCol : Col A B P) (hBet : Bet A B C) :
    Bet P A B ∨ Bet A P B ∨ Bet B P C ∨ Bet B C P := by
  rcases hCol with H2 | H2
  · have HH := l5_2 hAB hBet H2
    exact Or.inr (Or.inr (or_ind (fun H3 => Or.inr H3) (fun H3 => Or.inl H3) HH))
  · rcases H2 with H3 | H3
    · exact Or.inr (Or.inl (between_symmetry H3))
    · exact Or.inl H3

theorem third_point_c (A B P : Tpoint) (h : Col A B P) :
    Bet P A B ∨ Bet A P B ∨ Bet A B P := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inl (between_symmetry H1))
    · exact Or.inl H1

theorem l5_12_a_c (A B C : Tpoint) (h : Bet A B C) : Le A B A C ∧ Le B C A C :=
  ⟨(⟨B, (⟨h, (cong_reflexivity A B)⟩)⟩), (le_comm_c C B C A (⟨B, (⟨(between_symmetry h), (cong_reflexivity C B)⟩)⟩))⟩

theorem bet__le1213_c (A B C : Tpoint) (h : Bet A B C) : Le A B A C := sorry

theorem bet__le2313_c (A B C : Tpoint) (h : Bet A B C) : Le B C A C := sorry

theorem bet__lt1213_c (A B C : Tpoint) (hBC : B ≠ C) (h : Bet A B C) :
    Lt A B A C :=
  ⟨(bet__le1213_c A B C h), ((fun H => hBC (between_cong_c A C B h H)))⟩

theorem bet__lt2313_c (A B C : Tpoint) (hAB : A ≠ B) (h : Bet A B C) :
    Lt B C A C :=
  lt_comm_c C B C A (bet__lt1213_c C B A (Ne.symm hAB) (between_symmetry h))

theorem l5_12_b_c (A B C : Tpoint)
    (hCol : Col A B C) (h₁ : Le A B A C) (h₂ : Le B C A C) : Bet A B C := by
  rcases hCol with H2 | H2
  · exact H2
  · rcases H2 with H3 | H3
    · have H4 := l5_12_a_c B C A H3
      obtain ⟨H5, H6⟩ := H4
      have H7 := le_anti_symmetry_c A B A C h₁ (le_comm_c C A B A H6)
      have H8 := between_cong_c A B C (between_symmetry H3) (cong_symmetry H7)
      exact eq_ind C (fun B0 => Bet B0 C A - > Le A B0 A C - > Le B0 C A C - > Le B0 C B0 A - > Le C A B0 A - > Cong A B0 A C - > Bet A B0 C) (fun _ _ _ _ _ _ => between_trivial A C) B H8 H3 h₁ h₂ H5 H6 H7
    · have H4 := l5_12_a_c B A C (between_symmetry H3)
      obtain ⟨H5, H6⟩ := H4
      have H7 := le_anti_symmetry_c B C A C h₂ H6
      have H8 := between_cong_c C B A H3 (cong_symmetry (cong_commutativity H7))
      subst H8
      exact between_symmetry (between_trivial C B)

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

theorem lt__le_c (A B C D : Tpoint) (h : Lt A B C D) : Le A B C D := sorry

theorem le1234_lt__lt_c (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Lt C D E F) : Lt A B E F := sorry

theorem le3456_lt__lt_c (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Le C D E F) : Lt A B E F := sorry

theorem lt_transitivity_c (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Lt C D E F) : Lt A B E F :=
  le1234_lt__lt_c A B C D E F (lt__le_c A B C D h₁) h₂

theorem not_and_lt_c (A B C D : Tpoint) : ¬ (Lt A B C D ∧ Lt C D A B) := sorry

theorem nlt_c (A B : Tpoint) : ¬ Lt A B A B :=
  (fun Hlt => not_and_lt_c B A B (⟨Hlt, Hlt⟩))

theorem le__nlt_c (A B C D : Tpoint) (h : Le A B C D) : ¬ Lt C D A B := by
  exact fun HLt => not_and_lt_c B C D (⟨(⟨h, (and_ind (fun _ H0 => (fun H1 => H0 (cong_symmetry H1))) HLt)⟩), HLt⟩)

theorem cong__nlt_c (A B C D : Tpoint) (h : Cong A B C D) : ¬ Lt A B C D :=
  le__nlt_c C D A B (⟨B, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial A B))))), (cong_symmetry h)⟩)⟩)

theorem nlt__le_c (A B C D : Tpoint) (h : ¬ Lt A B C D) : Le C D A B := sorry

theorem lt__nle_c (A B C D : Tpoint) (h : Lt A B C D) : ¬ Le C D A B :=
  (fun HLe => le__nlt_c D A B HLe h)

theorem nle__lt_c (A B C D : Tpoint) (h : ¬ Le A B C D) : Lt C D A B := sorry

theorem lt1123_c (A B C : Tpoint) (hBC : B ≠ C) : Lt A A B C := sorry

theorem bet2_le2__le_c (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Le o a O A) (h₄ : Le o b O B) : Le a b A B := sorry

theorem Le_cases_c (A B C D : Tpoint)
    (h : Le A B C D ∨ Le B A C D ∨ Le A B D C ∨ Le B A D C) :
    Le A B C D := sorry

theorem Lt_cases_c (A B C D : Tpoint)
    (h : Lt A B C D ∨ Lt B A C D ∨ Lt A B D C ∨ Lt B A D C) :
    Lt A B C D := sorry

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