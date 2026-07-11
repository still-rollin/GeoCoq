import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem bet_out_c (A B C : Tpoint) (hBA : B ≠ A) (h : Bet A B C) : Out A B C :=
  ⟨hBA, (⟨((fun H1 => eq_ind C (fun A0 => B <> A0 - > Bet A0 B C - > False) (fun H2 H3 => (let H4 := between_identity C B H3; eq_ind C (fun B0 => B0 <> C - > False) (fun H5 => H5 eq_refl) B H4 H2)) A H1 hBA h)), (Or.inl h)⟩)⟩

theorem bet_out_1_c (A B C : Tpoint) (hBA : B ≠ A) (h : Bet C B A) : Out A B C :=
  bet_out hBA (between_symmetry h)

theorem out_dec_c (P A B : Tpoint) : Out P A B ∨ ¬ Out P A B := sorry

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
  exact ⟨(fun H3 => ⟨hAP, (⟨hBP, (l5_2 hCP (between_symmetry h) (between_symmetry H3))⟩)⟩), (fun H3 => and_ind (fun H4 H5 => and_ind (fun _ H6 => or_ind (fun H7 => between_symmetry (between_symmetry (outer_transitivity_between2 (between_symmetry H7) h H4))) (fun H7 => between_symmetry (between_symmetry (between_exchange3 (between_symmetry H7) h))) H6) H5) H3)⟩

theorem bet_out__bet_c (A B C P : Tpoint) (h₁ : Bet A P C) (h₂ : Out P A B) :
    Bet B P C := sorry

theorem l6_3_1_c (A B P : Tpoint) (h : Out P A B) :
    A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨H0, (⟨H2, (or_ind (fun H4 => (let H5 := point_construction_different A P; ex_ind (fun C H6 => and_ind (fun H7 H8 => ⟨C, (⟨(Ne.symm H8), (⟨H7, (between_symmetry (between_symmetry (outer_transitivity_between2 (between_symmetry H4) H7 H0)))⟩)⟩)⟩) H6) H5)) (fun H4 => (let H5 := point_construction_different B P; ex_ind (fun C H6 => and_ind (fun H7 H8 => ⟨C, (⟨(Ne.symm H8), (⟨(between_symmetry (between_symmetry (outer_transitivity_between2 (between_symmetry H4) H7 H2))), H7⟩)⟩)⟩) H6) H5)) H3)⟩)⟩

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
  · exact False_ind (A <> P /\ B <> P /\ (Bet P A B \/ Bet P B A)) (H1 H2)
  · have o := point_equality_decidability A P
    rcases o with H3 | H3
    · exact eq_ind A (fun P0 => Bet P0 B A \/ Bet B A P0 - > ~ Bet A P0 B - > A <> P0 /\ B <> P0 /\ (Bet P0 A B \/ Bet P0 B A)) (fun H4 H5 => or_ind (fun _ => ⟨((fun _ => H5 (between_trivial2 A B))), (⟨((fun _ => H5 (between_trivial2 A B))), (Or.inl (between_trivial2 A B))⟩)⟩) (fun _ => ⟨((fun _ => H5 (between_trivial2 A B))), (⟨((fun _ => H5 (between_trivial2 A B))), (Or.inl (between_trivial2 A B))⟩)⟩) H4) P H3 H2 H1
    · have o0 := point_equality_decidability B P
      rcases o0 with H4 | H4
      · exact eq_ind B (fun P0 => Bet P0 B A \/ Bet B A P0 - > ~ Bet A P0 B - > A <> P0 - > A <> P0 /\ B <> P0 /\ (Bet P0 A B \/ Bet P0 B A)) (fun H5 H6 H7 => or_ind (fun H8 => ⟨((fun H9 => (let H10 := H7 H9; False_ind False H10))), (⟨((fun _ => H6 (between_trivial A B))), (Or.inr H8)⟩)⟩) (fun H8 => ⟨((fun H9 => (let H10 := H7 H9; False_ind False H10))), (⟨((fun _ => H6 (between_trivial A B))), (Or.inl H8)⟩)⟩) H5) P H4 H2 H1 H3
      · rcases H2 with H5 | H5
        · exact ⟨H3, (⟨H4, (Or.inr H5)⟩)⟩
        · exact ⟨H3, (⟨H4, (Or.inl (between_symmetry H5))⟩)⟩

theorem out_trivial_c (P A : Tpoint) (hAP : A ≠ P) : Out P A A :=
  ⟨hAP, (⟨hAP, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 A P)))))⟩)⟩

theorem l6_6_c (P A B : Tpoint) (h : Out P A B) : Out P B A := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  rcases H3 with H4 | H4
  · exact ⟨((fun H5 => (let H6 := H2 H5; False_ind False H6))), (⟨((fun H5 => (let H6 := H0 H5; False_ind False H6))), (Or.inr H4)⟩)⟩
  · exact ⟨((fun H5 => (let H6 := H2 H5; False_ind False H6))), (⟨((fun H5 => (let H6 := H0 H5; False_ind False H6))), (Or.inl H4)⟩)⟩

theorem l6_7_c (P A B C : Tpoint) (h₁ : Out P A B) (h₂ : Out P B C) : Out P A C := by
  obtain ⟨H1, H2⟩ := h₂
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := h₁
  obtain ⟨_, H7⟩ := H6
  exact ⟨H5, (⟨H3, (or_ind (fun H8 => or_ind (fun H9 => Or.inl (between_exchange4 H8 H9)) (fun H9 => l5_3 H8 H9) H4) (fun H8 => or_ind (fun H9 => l5_1 (Ne.symm H1) H8 H9) (fun H9 => Or.inr (between_symmetry (between_symmetry (between_exchange4 H9 H8)))) H4) H7)⟩)⟩

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
    (h₃ : Out A Y R) (h₄ : Cong A Y B C) : X = Y := sorry

theorem l6_11_existence_c (A B C R : Tpoint) (hRA : R ≠ A) (hBC : B ≠ C) :
    ∃ X, Out A X R ∧ Cong A X B C := sorry

theorem segment_construction_3_c (A B X Y : Tpoint) (hAB : A ≠ B) (hXY : X ≠ Y) :
    ∃ C, Out A B C ∧ Cong A C X Y := sorry

theorem l6_13_1_c (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Le P A P B) :
    Bet P A B := by
  obtain ⟨H1, H2⟩ := h₁
  obtain ⟨H3, H4⟩ := H2
  rcases H4 with H5 | H5
  · exact H5
  · obtain ⟨Y, H6⟩ := h₂
    obtain ⟨H7, H8⟩ := H6
    have H9 := l6_11_uniqueness_c P P A B Y A (⟨((fun H9 => eq_ind Y (fun P0 => A <> P0 - > B <> P0 - > Bet P0 B A - > Bet P0 Y B - > Cong P0 A P0 Y - > False) (fun H10 H11 H12 _ H13 => (let H14 := cong_identity Y A Y H13; eq_ind Y (fun A0 => Bet Y B A0 - > A0 <> Y - > False) (fun H15 _ => (let H16 := between_identity Y B H15; eq_ind Y (fun B0 => B0 <> Y - > False) (fun H17 => H17 eq_refl) B H16 H11)) A H14 H12 H10)) P H9 H1 H3 H5 H7 H8)), (⟨H3, (Or.inl H7)⟩)⟩) (cong_symmetry H8) (⟨H1, (⟨H3, (Or.inr H5)⟩)⟩) (cong_reflexivity P A)
    subst H9
    exact H7

theorem l6_13_2_c (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Bet P A B) :
    Le P A P B :=
  ⟨A, (⟨h₂, (cong_reflexivity P A)⟩)⟩

theorem l6_16_1_c (P Q S X : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col S P Q) (h₂ : Col X P Q) : Col X P S := sorry

theorem col_transitivity_1_c (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col P A B := sorry

theorem col_transitivity_2_c (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col Q A B := sorry

theorem l6_21_c (A B C D P Q : Tpoint)
    (hNCol : ¬ Col A B C) (hCD : C ≠ D)
    (h₁ : Col A B P) (h₂ : Col A B Q)
    (h₃ : Col C D P) (h₄ : Col C D Q) : P = Q := sorry

theorem col2__eq_c (A B X Y : Tpoint)
    (h₁ : Col A X Y) (h₂ : Col B X Y) (h₃ : ¬ Col A X B) : X = Y := sorry

theorem not_col_exists_c (A B : Tpoint) (hAB : A ≠ B) : ∃ C, ¬ Col A B C := sorry

theorem col3_c (X Y A B C : Tpoint) (hXY : X ≠ Y)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col X Y C) : Col A B C := sorry

theorem colx_c (A B C X Y : Tpoint) (hAB : A ≠ B)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col A B C) : Col X Y C := sorry

theorem out2__bet_c (A B C : Tpoint) (h₁ : Out A B C) (h₂ : Out C A B) : Bet A B C := sorry

theorem bet2_le2__le1346_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le B C B' C') : Le A C A' C' := sorry

theorem bet2_le2__le2356_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le A' C' A C) : Le B' C' B C := sorry

theorem bet2_le2__le1245_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le B C B' C') (h₄ : Le A' C' A C) : Le A' B' A B := sorry

theorem cong_preserves_bet_c (B A' A0 E D' D0 : Tpoint)
    (h₁ : Bet B A' A0) (h₂ : Cong B A' E D') (h₃ : Cong B A0 E D0)
    (h₄ : Out E D' D0) : Bet E D' D0 := sorry

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
    Bet A B C := sorry

theorem or_bet_out_c (A B C : Tpoint) : Bet A B C ∨ Out B A C ∨ ¬ Col A B C := sorry

theorem not_bet_out_c (A B C : Tpoint) (h₁ : Col A B C) (h₂ : ¬ Bet A B C) :
    Out B A C := sorry

theorem not_bet_and_out_c (A B C : Tpoint) : ¬ (Bet A B C ∧ Out B A C) := by
  exact fun H => and_ind (fun H0 H1 => and_ind (fun H2 H3 => and_ind (fun H4 H5 => or_ind (fun H6 => (let H7 := between_equality H0 H6; False_ind False (H2 H7))) (fun H6 => (let H7 := between_equality (between_symmetry H0) H6; False_ind False (H4 H7))) H5) H3) H1) H

theorem out_to_bet_c (A B C A' B' C' : Tpoint)
    (h₁ : Col A' B' C')
    (h₂ : Out B A C ↔ Out B' A' C')
    (h₃ : Bet A B C) : Bet A' B' C' := sorry

theorem col_out2_col_c (A B C AA CC : Tpoint)
    (h₁ : Col A B C) (h₂ : Out B A AA) (h₃ : Out B C CC) : Col AA B CC := sorry

theorem bet2_out_out_c (A B C B' C' : Tpoint)
    (hBA : B ≠ A) (hB'A : B' ≠ A) (h₁ : Out A C C')
    (h₂ : Bet A B C) (h₃ : Bet A B' C') : Out A B B' := by
  have o := point_equality_decidability B' C'
  rcases o with H4 | H4
  · exact eq_ind B' (fun C'0 => Out A C C'0 - > Bet A B' C'0 - > Out A B B') (fun H5 _ => and_ind (fun _ H6 => and_ind (fun H7 H8 => ⟨hBA, (⟨H7, (or_ind (fun H9 => Or.inl (between_exchange4 h₂ H9)) (fun H9 => l5_3 h₂ H9) H8)⟩)⟩) H6) H5) C' H4 h₁ h₃
  · obtain ⟨_, H5⟩ := h₁
    obtain ⟨_, H6⟩ := H5
    exact ⟨hBA, (⟨hB'A, (or_ind (fun H7 => (let H8 := between_exchange4 h₂ H7; l5_3 H8 h₃)) (fun H7 => (let H8 := between_exchange3 h₃ H7; (let H9 := outer_transitivity_between h₃ H8 H4; l5_3 h₂ H9))) H6)⟩)⟩

theorem bet2__out_c (A B C B' : Tpoint)
    (hAB : A ≠ B) (hAB' : A ≠ B')
    (h₁ : Bet A B C) (h₂ : Bet A B' C) : Out A B B' :=
  bet2_out_out_c A B C B' C (Ne.symm hAB) (Ne.symm hAB') ((let H3 := bet_neq12__neq h₁ hAB; out_trivial (Ne.symm H3))) h₁ h₂

theorem out_bet_out_1_c (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P A B := by
  have o := point_equality_decidability B P
  rcases o with H1 | H1
  · exact eq_ind B (fun P0 => Out P0 A C - > Out P0 A B) (fun H2 => False_ind (Out B A B) (not_bet_and_out_c B C (⟨h₂, H2⟩))) P H1 h₁
  · obtain ⟨H2, H3⟩ := h₁
    obtain ⟨_, H4⟩ := H3
    exact ⟨H2, (⟨H1, (or_ind (fun H5 => Or.inl (between_inner_transitivity H5 h₂)) (fun H5 => Or.inr (between_exchange2 H5 (between_symmetry h₂))) H4)⟩)⟩

theorem out_bet_out_2_c (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P B C :=
  l6_6 (out_bet_out_1_c C B A P (l6_6 h₁) (between_symmetry h₂))

theorem out_bet__out_c (A B P Q : Tpoint) (h₁ : Bet P Q A) (h₂ : Out Q A B) :
    Out P A B := sorry

theorem segment_reverse_c (A B C : Tpoint) (h : Bet A B C) :
    ∃ B', Bet A B' C ∧ Cong C B' A B := sorry

theorem diff_col_ex_c (A B : Tpoint) : ∃ C, A ≠ C ∧ B ≠ C ∧ Col A B C := sorry

theorem diff_bet_ex3_c (A B C : Tpoint) (h : Bet A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := sorry

theorem diff_col_ex3_c (A B C : Tpoint) (h : Col A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := sorry

theorem Out_cases_c (A B C : Tpoint) (h : Out A B C ∨ Out A C B) : Out A B C := by
  rcases h with H0 | H0
  · exact H0
  · exact l6_6 H0

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
end GeocoqTranslate.Tarski.Base