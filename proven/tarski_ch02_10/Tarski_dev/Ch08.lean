import GeocoqTranslate.Tarski_dev.Ch07

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

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
    Midpoint B A C := by
  rcases point_equality_decidability H B with e | hHB
  · subst e
    exact ⟨h₁, cong_right_commutativity_c A H C H h₂⟩
  · have hColBCA : Col B C A := by
      have := bet_col_c A B C h₁
      show Col B C A
      colr
    have hPerHBA : Per H B A := per_col_c H B C A hBC h₃ hColBCA
    have hPerABH : Per A B H := l8_2_c H B A hPerHBA
    have hPerCBH : Per C B H := l8_2_c H B C h₃
    obtain ⟨Hp, hMidHp, hCongHp⟩ := hPerCBH
    obtain ⟨Hpp, hMidHpp, hCongHpp⟩ := hPerABH
    have hHpEq : Hp = Hpp := construction_uniqueness_c H B H B Hp Hpp hHB
      (midpoint_bet_c H B Hp hMidHp)
      (cong_commutativity_c Hp B B H (midpoint_cong_c Hp B H (l7_2_c B H Hp hMidHp)))
      (midpoint_bet_c H B Hpp hMidHpp)
      (cong_commutativity_c Hpp B B H (midpoint_cong_c Hpp B H (l7_2_c B H Hpp hMidHpp)))
    subst hHpEq
    have hIFSC : IFSC H B Hp A H B Hp C :=
      ⟨midpoint_bet_c H B Hp hMidHp, midpoint_bet_c H B Hp hMidHp,
       cong_reflexivity_c H Hp, cong_reflexivity_c B Hp,
       cong_commutativity_c A H C H h₂,
       cong_commutativity_c A Hp C Hp
         (cong_transitivity_c A Hp A H C Hp (cong_symmetry_c A H A Hp hCongHpp)
           (cong_transitivity_c A H C H C Hp h₂ hCongHp))⟩
    have hFin := l4_2_c H B Hp A H B Hp C hIFSC
    exact ⟨h₁, cong_left_commutativity_c B A B C hFin⟩

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
    B = B' ∨ ¬ Col B' C D := by
  rcases point_equality_decidability B B' with e | hBB'
  · exact Or.inl e
  · refine Or.inr (fun hColB'CD => hBB' ?_)
    have hColCBB' : Col C B B' := by colr
    have hPerAB'B : Per A B' B := per_col_c A B' C B hB'C h₂ (by colr)
    have hPerABB' : Per A B B' := per_col_c A B C B' hBC h₁ (by colr)
    exact (l8_7_c A B' B hPerAB'B hPerABB').symm

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

theorem perp_exists_c (O A B : Tpoint) (hAB : A ≠ B) : ∃ X, Perp O X A B := by
  rcases col_dec_c A B O with hColO | hNColO
  · obtain ⟨C, hAC, hBC, hOC, hColABC⟩ := diff_col_ex3_c A B O hColO
    obtain ⟨P, T, hPerpOCPO, hColOCT, hBetOTP⟩ := l8_21_c O C O hOC
    have hColOCB : Col O C B := by colr
    have hColOCA : Col O C A := by colr
    have hgoal : Perp B A P O := perp_col2_c O C B A P O hPerpOCPO hAB.symm hColOCB hColOCA
    exact ⟨P, perp_comm_c P O B A (perp_sym_c B A P O hgoal)⟩
  · obtain ⟨X, hColABX, hPerpABOX⟩ := l8_18_existence_c A B O hNColO
    exact ⟨X, perp_sym_c A B O X hPerpABOX⟩

theorem perp_vector_c (A B : Tpoint) (hAB : A ≠ B) : ∃ X Y, Perp A B X Y := by
  obtain ⟨Y, hPerp⟩ := perp_exists_c A A B hAB
  exact ⟨A, Y, perp_sym_c A Y A B hPerp⟩

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
    Cong A R P B ∧ Midpoint X A B ∧ Midpoint X P R := by
  have hCAR : Cong A R P B := per_cong_c A B P R X hAB hAP h₁ h₂ h₃ hCol hBet
  have hNCol : ¬ Col A P B := fun hc => per_not_col_c B A P hAB.symm hAP h₁ (by colr)
  have hPR : P ≠ R := by
    intro e
    subst e
    have hXP : P = X := between_identity P X hBet
    rw [← hXP] at hCol
    exact hNCol (by colr)
  have hColAXB : Col A X B := by colr
  have hColPXR : Col P X R := bet_col_c P X R hBet
  obtain ⟨hM1, hM2⟩ :=
    l7_21_c A P B R X hNCol hPR h₃ (by cong_r) hColAXB hColPXR
  exact ⟨hCAR, hM1, hM2⟩

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

end GeocoqTranslate.Tarski.Base
