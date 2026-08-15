import GeocoqTranslate.Tarski_dev.Ch05

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

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

theorem bet_out_bet_c (A B C P : Tpoint) (h₁ : Bet A P C) (h₂ : Out P A B) :
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

theorem l6_13_2_c (P A B : Tpoint) (h₁ : Bet P A B) :
    Le P A P B :=
  ⟨A, (⟨h₁, (cong_reflexivity P A)⟩)⟩

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

theorem col2_eq_c (A B X Y : Tpoint)
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

theorem out2_bet_c (A B C : Tpoint) (h₁ : Out A B C) (h₂ : Out C A B) : Bet A B C := by
  have Hout3 := l6_4_1_c A B C h₂
  obtain ⟨x, x0⟩ := Hout3
  obtain ⟨x1, x2⟩ := h₁
  obtain ⟨x3, x4⟩ := x2
  rcases x4 with x5 | x5
  · exact x5
  · exact ((x0 x5)).elim

theorem bet2_le2_le1346_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le B C B' C') : Le A C A' C' := by
  rcases eq_dec_points_c A B with hAB | hAB
  · rw [hAB] at ⊢
    exact le_transitivity_c B C B' C' A' C' h₄ (l5_12_a_c A' B' C' h₂).2
  · rcases eq_dec_points_c B C with hBC | hBC
    · rw [← hBC]
      exact le_transitivity_c A B A' B' A' C' h₃ ⟨B', h₂, cong_reflexivity A' B'⟩
    · have hA'B' : A' ≠ B' := by
        intro e
        rw [e] at h₃
        exact hAB (le_zero_c A B B' h₃)
      have hB'C' : B' ≠ C' := by
        intro e
        rw [e] at h₄
        exact hBC (le_zero_c B C C' h₄)
      obtain ⟨B0, hBetA'B0B', hCongABA'B0⟩ := h₃
      have hA'B0 : A' ≠ B0 := by
        intro e
        rw [e] at hCongABA'B0
        exact hAB (cong_identity A B B0 hCongABA'B0)
      obtain ⟨C0, hBetA'B0C0, hCongB0C0BC⟩ := segment_construction A' B0 B C
      have hB0C0 : B0 ≠ C0 := by
        intro e
        rw [e] at hCongB0C0BC
        exact hBC (cong_reverse_identity_c C0 B C hCongB0C0BC)
      have hBetB0B'C' : Bet B0 B' C' := between_exchange3_c A' B0 B' C' hBetA'B0B' h₂
      have hB0C' : B0 ≠ C' := by
        intro e
        rw [e] at hBetB0B'C'
        exact hB'C' (between_identity C' B' hBetB0B'C').symm
      have hOutB0C0C' : Out B0 C0 C' := by
        refine ⟨Ne.symm hB0C0, Ne.symm hB0C', ?_⟩
        rcases eq_dec_points_c B0 B' with hB0B' | hB0B'
        · rw [hB0B']
          rw [hB0B'] at hBetA'B0C0
          exact l5_2_c A' B' C0 C' hA'B' hBetA'B0C0 h₂
        · rcases l5_2_c A' B0 C0 B' hA'B0 hBetA'B0C0 hBetA'B0B' with hc | hc
          · exact Or.inl (between_exchange4_c B0 C0 B' C' hc hBetB0B'C')
          · exact l5_1_c B0 B' C0 C' hB0B' hc hBetB0B'C'
      have hLeB'C'B0C' : Le B' C' B0 C' :=
        le_comm_c C' B' C' B0 ⟨B', between_symmetry_c B0 B' C' hBetB0B'C', cong_reflexivity C' B'⟩
      have hLeB0C0B0C' : Le B0 C0 B0 C' :=
        le_transitivity_c B0 C0 B' C' B0 C'
          (l5_6_c B C B' C' B0 C0 B' C' h₄ (cong_symmetry_c B0 C0 B C hCongB0C0BC) (cong_reflexivity B' C'))
          hLeB'C'B0C'
      have hBetB0C0C' : Bet B0 C0 C' := l6_13_1_c B0 C0 C' hOutB0C0C' hLeB0C0B0C'
      exact ⟨C0, outer_transitivity_between2_c A' B0 C0 C' hBetA'B0C0 hBetB0C0C' hB0C0,
             l2_11_c A B C A' B0 C0 h₁ hBetA'B0C0 hCongABA'B0
               (cong_symmetry_c B0 C0 B C hCongB0C0BC)⟩

theorem bet2_le2_le2356_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le A' C' A C) : Le B' C' B C := by
  rcases eq_dec_points_c A B with hAB | hAB
  · rw [hAB] at h₄
    exact le_transitivity_c B' C' A' C' B C (l5_12_a_c A' B' C' h₂).2 h₄
  · have hAC : A ≠ C := by
      intro e
      rw [← e] at h₁
      exact hAB (between_identity A B h₁)
    obtain ⟨B0, hBetABB0, hCongAB0A'B'⟩ := l5_5_1_c A B A' B' h₃
    have hAB0 : A ≠ B0 := by
      intro e
      rw [← e] at hBetABB0
      exact hAB (between_identity A B hBetABB0)
    obtain ⟨C0, hBetAC0C, hCongA'C'AC0⟩ := h₄
    have hAC0 : A ≠ C0 := by
      intro e
      rw [← e] at hCongA'C'AC0
      have hA'C' : A' = C' := cong_identity A' C' A hCongA'C'AC0
      rw [hA'C'] at h₂ h₃
      have hC'B' : C' = B' := between_identity C' B' h₂
      rw [hC'B'] at h₃
      exact hAB (le_zero_c A B B' h₃)
    have hBetAB0C0 : Bet A B0 C0 :=
      l6_13_1_c A B0 C0
        (l6_7_c A B0 B C0
          (l6_6_c A B B0 (bet_out_c A B B0 (Ne.symm hAB) hBetABB0))
          (l6_7_c A B C C0
            (bet_out_c A B C (Ne.symm hAB) h₁)
            (l6_6_c A C0 C (bet_out_c A C0 C (Ne.symm hAC0) hBetAC0C))))
        (l5_6_c A' B' A' C' A B0 A C0 (l5_12_a_c A' B' C' h₂).1
          (cong_symmetry_c A B0 A' B' hCongAB0A'B') hCongA'C'AC0)
    have hBetABC0 : Bet A B C0 := between_exchange4_c A B B0 C0 hBetABB0 hBetAB0C0
    exact l5_6_c B0 C0 B C B' C' B C
      (le_transitivity_c B0 C0 B C0 B C
        (l5_12_a_c B B0 C0 (between_exchange3_c A B B0 C0 hBetABB0 hBetAB0C0)).2
        (l5_12_a_c B C0 C (between_exchange3_c A B C0 C hBetABC0 hBetAC0C)).1)
      (l4_3_1_c A B0 C0 A' B' C' hBetAB0C0 h₂ hCongAB0A'B'
        (cong_symmetry_c A' C' A C0 hCongA'C'AC0))
      (cong_reflexivity B C)

theorem bet2_le2_le1245_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le B C B' C') (h₄ : Le A' C' A C) : Le A' B' A B :=
  le_comm_c B' A' B A (bet2_le2_le2356_c C B A C' B' A' (between_symmetry h₁) (between_symmetry h₂) (le_comm_c B C B' C' h₃) (le_comm_c A' C' A C h₄))

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

theorem bet2_out_c (A B C B' : Tpoint)
    (hAB : A ≠ B) (hAB' : A ≠ B')
    (h₁ : Bet A B C) (h₂ : Bet A B' C) : Out A B B' :=
  bet2_out_out_c A B C B' C (Ne.symm hAB) (Ne.symm hAB') ((let H3 := bet_neq12_neq h₁ hAB; out_trivial (Ne.symm H3))) h₁ h₂

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

theorem out_bet_out_c (A B P Q : Tpoint) (h₁ : Bet P Q A) (h₂ : Out Q A B) :
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
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := by
  rcases eq_dec_points_c A B with hAB | hAB
  · rcases eq_dec_points_c B C with hBC | hBC
    · obtain ⟨D, hBetBCD, hCD⟩ := point_construction_different B C
      refine ⟨D, ?_, ?_, hCD, Or.inl ?_⟩
      · subst hAB; subst hBC; exact hCD
      · subst hAB; subst hBC; exact hCD
      · subst hAB; subst hBC; exact hBetBCD
    · obtain ⟨D, hBetBCD, hCD⟩ := point_construction_different B C
      refine ⟨D, ?_, ?_, hCD, Or.inl (outer_transitivity_between_c A B C D h hBetBCD hBC)⟩
      · intro hAD
        subst hAD
        exact hBC (between_equality hBetBCD (between_symmetry_c A B C h))
      · intro hBD
        subst hBD
        exact hBC (between_identity B C hBetBCD)
  · rcases eq_dec_points_c B C with hBC | hBC
    · subst hBC
      obtain ⟨D, hAD, hBD, hCol⟩ := diff_col_ex_c A B
      exact ⟨D, hAD, hBD, hBD, hCol⟩
    · obtain ⟨D, hBetBCD, hCD⟩ := point_construction_different B C
      refine ⟨D, ?_, ?_, hCD, Or.inl (outer_transitivity_between_c A B C D h hBetBCD hBC)⟩
      · intro hAD
        subst hAD
        exact hBC (between_equality hBetBCD (between_symmetry_c A B C h))
      · intro hBD
        subst hBD
        exact hBC (between_identity B C hBetBCD)

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

#print axioms GeocoqTranslate.Tarski.Base.bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_dec_c
#print axioms GeocoqTranslate.Tarski.Base.out_diff1_c
#print axioms GeocoqTranslate.Tarski.Base.out_diff2_c
#print axioms GeocoqTranslate.Tarski.Base.out_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.out_col_c
#print axioms GeocoqTranslate.Tarski.Base.l6_2_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_bet_c
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
#print axioms GeocoqTranslate.Tarski.Base.col2_eq_c
#print axioms GeocoqTranslate.Tarski.Base.not_col_exists_c
#print axioms GeocoqTranslate.Tarski.Base.col3_c
#print axioms GeocoqTranslate.Tarski.Base.colx_c
#print axioms GeocoqTranslate.Tarski.Base.out2_bet_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2_le1346_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2_le2356_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_le2_le1245_c
#print axioms GeocoqTranslate.Tarski.Base.cong_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.out_cong_cong_c
#print axioms GeocoqTranslate.Tarski.Base.not_out_bet_c
#print axioms GeocoqTranslate.Tarski.Base.or_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.not_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.not_bet_and_out_c
#print axioms GeocoqTranslate.Tarski.Base.out_to_bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_out2_col_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_out_out_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_out_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet_out_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet_out_2_c
#print axioms GeocoqTranslate.Tarski.Base.out_bet_out_c
#print axioms GeocoqTranslate.Tarski.Base.segment_reverse_c
#print axioms GeocoqTranslate.Tarski.Base.diff_col_ex_c
#print axioms GeocoqTranslate.Tarski.Base.diff_bet_ex3_c
#print axioms GeocoqTranslate.Tarski.Base.diff_col_ex3_c
#print axioms GeocoqTranslate.Tarski.Base.Out_cases_c

end GeocoqTranslate.Tarski.Base
