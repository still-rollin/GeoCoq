import GeocoqTranslate.Tarski_dev.Ch09

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ex_sym_c (A B X : Tpoint) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y) := by
  have o := col_dec_c A B X
  rcases o with H | H
  · exact ⟨X, (⟨(Or.inr rfl), (⟨X, (⟨H, (l7_3_2_c X)⟩)⟩)⟩)⟩
  · have H0 := l8_18_existence_c A B X H
    obtain ⟨M0, H1⟩ := H0
    obtain ⟨H2, H3⟩ := H1
    have mp := symmetric_point_construction_c X M0
    obtain ⟨Z, H4⟩ := mp
    exact ⟨Z, (⟨(Or.inl (perp_sym_c X Z A B (perp_col_c X M0 A B Z ((fun H5 => (by
  subst H5
  have H7 := l7_3_c M0 X H4
  subst H7
  have H9 := perp_distinct_c A B M0 M0 H3
  obtain ⟨_, H10⟩ := H9
  exact ((H10 rfl)).elim))) (perp_sym_c A B X M0 H3) (Or.inl (midpoint_bet_c X M0 Z H4))))), (⟨M0, (⟨H2, H4⟩)⟩)⟩)⟩

theorem is_image_is_image_spec_c (P P' A B : Tpoint) (hAB : A ≠ B) :
    Reflect P' P A B ↔ ReflectL P' P A B :=
  ⟨fun h => h.elim (fun ⟨_, hr⟩ => hr) (fun ⟨hab, _⟩ => absurd hab hAB), fun h => Or.inl ⟨hAB, h⟩⟩

theorem ex_sym1_c (A B X : Tpoint) (hAB : A ≠ B) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y ∧ Reflect X Y A B) := by
  rcases col_dec_c A B X with hColX | hNColX
  · refine ⟨X, Or.inr rfl, X, hColX, l7_3_2_c X, ?_⟩
    rw [is_image_is_image_spec_c X X A B hAB]
    exact ⟨⟨X, l7_3_2_c X, hColX⟩, Or.inr rfl⟩
  · obtain ⟨M0, hColM0, hPerpXM0⟩ := l8_18_existence_c A B X hNColX
    obtain ⟨Z, hMidM0XZ⟩ := symmetric_point_construction_c X M0
    have hXZ : X ≠ Z := by
      intro e
      have hMidM0XX : Midpoint M0 X X := e ▸ hMidM0XZ
      have hM0X : M0 = X := l7_3_c M0 X hMidM0XX
      have hPerpXX : Perp A B X X := hM0X ▸ hPerpXM0
      exact (perp_distinct_c A B X X hPerpXX).2 rfl
    have hColXM0Z : Col X M0 Z := bet_col_c X M0 Z (midpoint_bet_c X M0 Z hMidM0XZ)
    refine ⟨Z, Or.inl ?_, M0, hColM0, hMidM0XZ, ?_⟩
    · exact perp_sym_c X Z A B (perp_col_c X M0 A B Z hXZ (perp_sym_c A B X M0 hPerpXM0) hColXM0Z)
    · rw [is_image_is_image_spec_c Z X A B hAB]
      exact ⟨⟨M0, l7_2_c M0 X Z hMidM0XZ, hColM0⟩,
        Or.inl (perp_sym_c Z X A B (perp_left_comm_c X Z A B
          (perp_col_c X M0 A B Z hXZ (perp_sym_c A B X M0 hPerpXM0) hColXM0Z)))⟩

theorem l10_2_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P1 P A B) (h₂ : ReflectL P2 P A B) : P1 = P2 := by
  obtain ⟨⟨X, hMidXPP1, hColX⟩, hOr1⟩ := h₁
  obtain ⟨⟨Y, hMidYPP2, hColY⟩, hOr2⟩ := h₂
  have key1 : (Perp A B P X ∧ ¬ Col A B P) ∨ (P = P1 ∧ Col A B P) := by
    rcases hOr1 with hp | he
    · left
      have hb : Bet P X P1 := midpoint_bet_c P X P1 hMidXPP1
      have hColPXP1 : Col P X P1 := bet_col_c P X P1 hb
      have hColPP1X : Col P P1 X := by colr
      have hPX : P ≠ X := by
        intro e
        have hMidPPP1 : Midpoint P P P1 := e ▸ hMidXPP1
        have hEqPP1 : P = P1 := is_midpoint_id_c P P1 hMidPPP1
        exact (perp_distinct_c A B P P1 hp).2 hEqPP1
      have hPerpPX : Perp A B P X :=
        perp_sym_c P X A B (perp_col_c P P1 A B X hPX (perp_sym_c A B P P1 hp) hColPP1X)
      have hNCol := (l8_16_1_c A B P X X hColX hColX hPerpPX).1
      exact ⟨hPerpPX, hNCol⟩
    · right
      have hXP : X = P := l7_3_c X P (he ▸ hMidXPP1)
      exact ⟨he, hXP ▸ hColX⟩
  have key2 : (Perp A B P Y ∧ ¬ Col A B P) ∨ (P = P2 ∧ Col A B P) := by
    rcases hOr2 with hp | he
    · left
      have hb : Bet P Y P2 := midpoint_bet_c P Y P2 hMidYPP2
      have hColPYP2 : Col P Y P2 := bet_col_c P Y P2 hb
      have hColPP2Y : Col P P2 Y := by colr
      have hPY : P ≠ Y := by
        intro e
        have hMidPPP2 : Midpoint P P P2 := e ▸ hMidYPP2
        have hEqPP2 : P = P2 := is_midpoint_id_c P P2 hMidPPP2
        exact (perp_distinct_c A B P P2 hp).2 hEqPP2
      have hPerpPY : Perp A B P Y :=
        perp_sym_c P Y A B (perp_col_c P P2 A B Y hPY (perp_sym_c A B P P2 hp) hColPP2Y)
      have hNCol := (l8_16_1_c A B P Y Y hColY hColY hPerpPY).1
      exact ⟨hPerpPY, hNCol⟩
    · right
      have hYP : Y = P := l7_3_c Y P (he ▸ hMidYPP2)
      exact ⟨he, hYP ▸ hColY⟩
  rcases key1 with ⟨hPerpPX, hNColP⟩ | ⟨he1, hColP⟩
  · rcases key2 with ⟨hPerpPY, _⟩ | ⟨_, hColP2⟩
    · have hXY : X = Y := l8_18_uniqueness_c A B P X Y hNColP hColX hPerpPX hColY hPerpPY
      exact symmetric_point_uniqueness_c P X P1 P2 hMidXPP1 (hXY ▸ hMidYPP2)
    · exact absurd hColP2 hNColP
  · rcases key2 with ⟨_, hNColP2⟩ | ⟨he2, _⟩
    · exact absurd hColP hNColP2
    · exact he1.symm.trans he2

theorem l10_2_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P1 P A B) (h₂ : Reflect P2 P A B) : P1 = P2 := by
  rcases h₁ with ⟨hAB1, hR1⟩ | ⟨hEq1, hMid1⟩
  · rcases h₂ with ⟨_, hR2⟩ | ⟨hEq2, _⟩
    · exact l10_2_uniqueness_spec_c A B P P1 P2 hR1 hR2
    · exact absurd hEq2 hAB1
  · rcases h₂ with ⟨hAB2, _⟩ | ⟨_, hMid2⟩
    · exact absurd hEq1 hAB2
    · exact symmetric_point_uniqueness_c P A P1 P2 hMid1 hMid2

theorem l10_2_existence_spec_c (A B P : Tpoint) :
    ∃ P', ReflectL P' P A B := by
  rcases col_dec_c A B P with hColABP | hNColABP
  · exact ⟨P, ⟨P, l7_3_2_c P, hColABP⟩, Or.inr rfl⟩
  · obtain ⟨X, hColABX, hPerpABPX⟩ := l8_18_existence_c A B P hNColABP
    obtain ⟨P', hMidXPP'⟩ := symmetric_point_construction_c P X
    refine ⟨P', ⟨X, hMidXPP', hColABX⟩, Or.inl ?_⟩
    have hPP' : P ≠ P' := by
      intro heq
      subst heq
      have hXP : X = P := l7_3_c X P hMidXPP'
      subst hXP
      have hd := perp_distinct_c A B X X hPerpABPX
      exact hd.2 rfl
    have hColPXP' : Col P X P' := bet_col_c P X P' (midpoint_bet_c P X P' hMidXPP')
    exact perp_sym_c P P' A B (perp_col_c P X A B P' hPP' (perp_sym_c A B P X hPerpABPX) hColPXP')

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
    (h₁ : Reflect P' P A B) (h₂ : Reflect P'' P' A B) : P = P'' :=
  l10_2_uniqueness_c A B P' P P'' (l10_4_c A B P' P h₁) h₂

theorem l10_6_uniqueness_c (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P P1 A B) (h₂ : Reflect P P2 A B) : P1 = P2 :=
  l10_2_uniqueness_c A B P P1 P2 (l10_4_c A B P P1 h₁) (l10_4_c A B P P2 h₂)

theorem l10_6_uniqueness_spec_c (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P P1 A B) (h₂ : ReflectL P P2 A B) : P1 = P2 :=
  l10_2_uniqueness_spec_c A B P P1 P2 (l10_4_spec_c A B P P1 h₁) (l10_4_spec_c A B P P2 h₂)

theorem l10_6_existence_spec_c (A B P' : Tpoint) :
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

theorem col_refl_c (A B P : Tpoint) (h : Col P A B) : ReflectL P P A B :=
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
    (hCol : Col A B T) (hRefl : Reflect T T' A B) : T = T' := by
  rcases hRefl with ⟨_, hL⟩ | ⟨hEq, _⟩
  · obtain ⟨⟨X, hMidXT'T, hColX⟩, hOr⟩ := hL
    rcases point_equality_decidability T X with hTX | hTX
    · have hMidTT'T : Midpoint T T' T := hTX ▸ hMidXT'T
      exact is_midpoint_id_c T T' (l7_2_c T T' T hMidTT'T)
    · rcases hOr with hPerp | hEq'
      · have hb : Bet T' X T := midpoint_bet_c T' X T hMidXT'T
        have hColTXT' : Col T X T' := by
          have : Col T' X T := bet_col_c T' X T hb
          show Col T X T'
          colr
        have hColT'AB : Col A B T' := by colr
        exact absurd hCol
          (l8_16_1_c A B T T' T' hColT'AB hColT'AB (perp_right_comm_c A B T' T hPerp)).1
      · exact hEq'.symm
  · exact absurd hEq hAB

theorem osym_not_col_c (A B P P' : Tpoint)
    (h₁ : Reflect P P' A B) (h₂ : ¬ Col A B P) : ¬ Col A B P' := by
  have hAB : A ≠ B := by
    intro e
    subst e
    exact h₂ (col_trivial_1_c A P)
  intro hColP'
  have hRefl' : Reflect P' P A B := l10_4_c A B P P' h₁
  have hEq : P' = P := image_id_c A B P' P hAB hColP' hRefl'
  exact h₂ (hEq ▸ hColP')

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

theorem l10_14_c (P P' A B : Tpoint) (hPP' : P ≠ P') (hAB : A ≠ B)
    (h : Reflect P P' A B) : TS A B P P' := by
  have hReflL : ReflectL P P' A B := (is_image_is_image_spec_c P' P A B hAB).mp h
  obtain ⟨⟨M0, hMidM0_raw, hColABM0⟩, hPerpOrEq⟩ := hReflL
  have hMidM0 : Midpoint M0 P P' := l7_2_c M0 P' P hMidM0_raw
  have hPerpRaw : Perp A B P' P := hPerpOrEq.resolve_right hPP'.symm
  have hPerp : Perp A B P P' := perp_right_comm_c A B P' P hPerpRaw
  have hColPM0P' : Col P M0 P' := col_permutation_4_c M0 P P' (midpoint_col_c P M0 P' hMidM0)
  have hPM0 : P ≠ M0 := by
    intro hEq
    subst hEq
    exact hPP' (is_midpoint_id_c P P' hMidM0)
  have hP'M0 : P' ≠ M0 := by
    intro hEq
    subst hEq
    exact hPP' (cong_identity P P' P' hMidM0.2)
  have hDisj : ¬ Col A B P ∨ ¬ Col A B P' := perp_not_col2_c A B P P' hPerp
  have hIffFwd : Col A B P → Col A B P' :=
    fun hCP => colx_c P M0 P' A B hPM0 hCP hColABM0 hColPM0P'
  have hIffBwd : Col A B P' → Col A B P :=
    fun hCP' => colx_c P' M0 P A B hP'M0 hCP' hColABM0 (col_permutation_3_c P M0 P' hColPM0P')
  have hNColABP : ¬ Col A B P := fun hCP => hDisj.elim (fun hn => hn hCP) (fun hn => hn (hIffFwd hCP))
  have hNColABP' : ¬ Col A B P' :=
    fun hCP' => hDisj.elim (fun hn => hn (hIffBwd hCP')) (fun hn => hn hCP')
  exact ⟨fun hc => hNColABP (col_permutation_1_c P A B hc),
    fun hc => hNColABP' (col_permutation_1_c P' A B hc),
    M0, col_permutation_2_c A B M0 hColABM0, midpoint_bet_c P M0 P' hMidM0⟩

theorem image_image_in_c (A B P P' M : Tpoint) (hPP' : P ≠ P')
    (h₁ : ReflectL P P' A B) (h₂ : Col A B M) (h₃ : Col P M P') :
    ReflectL_at M P P' A B := by
  obtain ⟨⟨X, hMidXP'P, hColABX⟩, hPerpOrEq⟩ := h₁
  have hPerp : Perp A B P' P := hPerpOrEq.resolve_right (fun heq => hPP' heq.symm)
  have hAB : A ≠ B := (perp_distinct_c A B P' P hPerp).1
  have hReflect : Reflect P P' A B :=
    Or.inl ⟨hAB, ⟨⟨X, hMidXP'P, hColABX⟩, hPerpOrEq⟩⟩
  have hTS : TS A B P P' := l10_14_c P P' A B hPP' hAB hReflect
  obtain ⟨hNColPAB, hNColP'AB, -⟩ := hTS
  have hEqXM : X = M := l6_21_c A B P' P X M
    (fun hc => hNColP'AB (col_permutation_2_c A B P' hc))
    hPP'.symm
    hColABX h₂
    (col_permutation_1_c X P' P (midpoint_col_c P' X P hMidXP'P))
    (col_permutation_2_c P M P' h₃)
  have hMidMP'P : Midpoint M P' P := hEqXM ▸ hMidXP'P
  exact ⟨⟨hMidMP'P, h₂⟩, Or.inl hPerp⟩

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

theorem midpoint_preserves_image_c (A B P P' Q Q' M : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B M) (hRefl : Reflect P P' A B)
    (h₁ : Midpoint M P Q) (h₂ : Midpoint M P' Q') : Reflect Q Q' A B := by
  have hReflL : ReflectL P P' A B := (is_image_is_image_spec_c P' P A B hAB).mp hRefl
  obtain ⟨⟨X, hMidXP'P, hColABX⟩, hPerpOrEq⟩ := hReflL
  rcases hPerpOrEq with hPerp | hEqPP'
  · -- Case 1: Perp A B P' P
    obtain ⟨Y, hMidMXY⟩ := symmetric_point_construction_c X M
    have hMidYQQ' : Midpoint Y Q Q' :=
      symmetry_preserves_midpoint_c P X P' Q Y Q' M h₁ hMidMXY h₂ (l7_2_c X P' P hMidXP'P)
    have hP'X : P' ≠ X := by
      intro hEq
      subst hEq
      exact (perp_distinct_c A B P' P hPerp).2 (is_midpoint_id_c P' P hMidXP'P)
    have hColP'PX : Col P' P X := col_permutation_1_c X P' P (midpoint_col_c P' X P hMidXP'P)
    have hPerpABP'X : Perp A B P' X :=
      perp_sym_c P' X A B (perp_col_c P' P A B X hP'X (perp_sym_c A B P' P hPerp) hColP'PX)
    have hL8 := l8_16_1_c A B P' M X hColABX hCol hPerpABP'X
    have hNColABP' : ¬ Col A B P' := hL8.1
    have hPerP'XM : Per P' X M := hL8.2
    rcases eq_dec_points_c X M with hXM | hXM
    · -- sub-case X = M
      subst hXM
      have hPeqQ' : P = Q' := l7_9_c P Q' X P' (l7_2_c X P' P hMidXP'P) (l7_2_c X P' Q' h₂)
      have hP'eqQ : P' = Q := l7_9_c P' Q X P hMidXP'P (l7_2_c X P Q h₁)
      rw [← hPeqQ', ← hP'eqQ]
      exact l10_4_c A B P P' hRefl
    · -- sub-case X ≠ M
      have hColMXY : Col M X Y := midpoint_col_c X M Y hMidMXY
      have hColABY : Col A B Y :=
        colx_c X M Y A B hXM hColABX hCol (col_permutation_4_c M X Y hColMXY)
      have hQQ'Ne : Q ≠ Q' := by
        intro hEq
        have hPP'eq : P = P' := l7_9_c P P' M Q h₁ (hEq ▸ h₂)
        exact (perp_distinct_c A B P' P hPerp).2 hPP'eq.symm
      have hP'M : P' ≠ M := fun hEq => hNColABP' (hEq ▸ hCol)
      have hColQ'MP' : Col Q' M P' :=
        col_permutation_2_c M P' Q' (midpoint_col_c P' M Q' h₂)
      have hQ'M : Q' ≠ M := by
        intro hEq
        subst hEq
        exact hP'M (cong_identity P' Q' Q' h₂.2)
      have hNColABQ' : ¬ Col A B Q' :=
        fun hCQ' => hNColABP' (colx_c Q' M P' A B hQ'M hCQ' hCol hColQ'MP')
      have hMY : M ≠ Y := by
        intro hEq
        subst hEq
        exact hXM (cong_identity X M M hMidMXY.2)
      have hPerQ'YM : Per Q' Y M :=
        midpoint_preserves_per_c P' X M Q' Y M M hPerP'XM h₂ hMidMXY (l7_3_2_c M)
      have hPerpABQ'Y : Perp A B Q' Y :=
        l8_16_2_c A B Q' M Y hColABY hCol hMY hNColABQ' hPerQ'YM
      have hColQ'YQ : Col Q' Y Q :=
        col_permutation_2_c Y Q Q' (midpoint_col_c Q Y Q' hMidYQQ')
      have step2 : Perp Q' Q A B :=
        perp_col_c Q' Y A B Q hQQ'Ne.symm (perp_sym_c A B Q' Y hPerpABQ'Y) hColQ'YQ
      have finalPerp : Perp A B Q' Q := perp_sym_c Q' Q A B step2
      have hReflLQQ' : ReflectL Q Q' A B :=
        ⟨⟨Y, l7_2_c Y Q Q' hMidYQQ', hColABY⟩, Or.inl finalPerp⟩
      exact (is_image_is_image_spec_c Q' Q A B hAB).mpr hReflLQQ'
  · -- Case 2: P' = P
    subst hEqPP'
    have hXeqP' : X = P' := l7_3_c X P' hMidXP'P
    subst hXeqP'
    have hQeqQ' : Q = Q' := l7_9_c Q Q' M X (l7_2_c M X Q h₁) (l7_2_c M X Q' h₂)
    subst hQeqQ'
    have hColMXQ : Col M X Q := midpoint_col_c X M Q h₁
    rcases eq_dec_points_c M X with hMX | hMX
    · subst hMX
      have hMeqQ : M = Q := is_midpoint_id_c M Q h₁
      subst hMeqQ
      exact hRefl
    · have hColABQ : Col A B Q :=
        colx_c M X Q A B hMX hCol hColABX hColMXQ
      exact Or.inl ⟨hAB, ⟨⟨Q, l7_3_2_c Q, hColABQ⟩, Or.inr rfl⟩⟩

theorem col_image_spec_c (A B X : Tpoint) (h : Col A B X) :
    ReflectL X X A B :=
  ⟨(⟨X, (⟨(l7_3_2_c X), h⟩)⟩), (Or.inr rfl)⟩

theorem image_triv_c (A B : Tpoint) : Reflect A A A B := by
  have o := point_equality_decidability A B
  rcases o with H | H
  · exact Or.inr (⟨H, (l7_3_2_c A)⟩)
  · exact Or.inl (⟨H, (col_image_spec_c A B A (col_trivial_3_c A B))⟩)

theorem cong_midpoint_image_c (A B X Y : Tpoint)
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

theorem col_image_spec_eq_c (A B P P' : Tpoint)
    (h₁ : Col A B P) (h₂ : ReflectL P P' A B) : P = P' :=
  l10_6_uniqueness_spec_c A B P P P' (col_image_spec_c A B P h₁) h₂

theorem image_spec_triv_c (A B : Tpoint) : ReflectL A A B B :=
  col_image_spec_c B B A (col_trivial_1_c B A)

theorem image_spec_eq_c (A P P' : Tpoint) (h : ReflectL P P' A A) : P = P' :=
  col_image_spec_eq_c A A P P' (col_trivial_1_c A P) h

theorem image_midpoint_c (A P P' : Tpoint) (h : Reflect P P' A A) :
    Midpoint A P' P := by
  rcases h with H0 | H0
  · obtain ⟨H1, _⟩ := H0
    exact ((H1 rfl)).elim
  · obtain ⟨_, H1⟩ := H0
    exact H1

theorem is_image_spec_dec_c (A B C D : Tpoint) :
    ReflectL A B C D ∨ ¬ ReflectL A B C D := by
  rcases point_equality_decidability C D with hCD | hCD
  · subst hCD
    rcases point_equality_decidability A B with hAB | hAB
    · subst hAB
      exact Or.inl (image_spec_triv_c A C)
    · right
      intro H
      obtain ⟨_, hOr⟩ := H
      rcases hOr with hPerp | hEq
      · exact (perp_distinct_c C C B A hPerp).1 rfl
      · exact hAB hEq.symm
  · obtain ⟨B', hB'⟩ := l10_6_existence_spec_c C D A
    rcases point_equality_decidability B B' with hBB' | hBB'
    · subst hBB'
      exact Or.inl hB'
    · right
      intro H
      apply hBB'
      exact l10_6_uniqueness_c C D A B B' (Or.inl ⟨hCD, H⟩) (Or.inl ⟨hCD, hB'⟩)

theorem l10_15_c (A B C P : Tpoint)
    (hCol : Col A B C) (hNCol : ¬ Col A B P) :
    ∃ Q, Perp A B Q C ∧ OS A B P Q := by
  have hAB : A ≠ B := by
    intro e
    subst e
    exact hNCol (col_trivial_1_c A P)
  obtain ⟨X, hTS⟩ : ∃ X, TS A B P X := by
    have hNCol' : ¬ Col P A B := fun h => hNCol (by colr)
    exact l9_10_c A B P hNCol'
  rcases point_equality_decidability A C with hAC | hAC
  · rw [← hAC]
    obtain ⟨Q, T, hPerpQA, hColT, hBetXTQ⟩ := l8_21_c A B X hAB
    refine ⟨Q, hPerpQA, ?_⟩
    have hNColQ : ¬ Col A B Q := perp_not_col_c A B Q hPerpQA
    have hNColQAB : ¬ Col Q A B := fun h => hNColQ (by colr)
    have hColTAB : Col T A B := by colr
    have hTSQX : TS A B Q X := ⟨hNColQAB, hTS.2.1, T, hColTAB, between_symmetry_c X T Q hBetXTQ⟩
    exact l9_8_1_c A B P Q X hTS hTSQX
  · obtain ⟨Q, T, hPerpCAQC, hColCAT, hBetXTQ⟩ := l8_21_c C A X (Ne.symm hAC)
    have hPerpABQC : Perp A B Q C :=
      perp_col_c A C Q C B hAB (perp_left_comm_c C A Q C hPerpCAQC) (by colr)
    have hNColQAB : ¬ Col Q A B := by
      intro hc
      exact (perp_not_col_c C A Q hPerpCAQC) (by colr)
    have hColTAB : Col T A B := by colr
    have hTSQX : TS A B Q X := ⟨hNColQAB, hTS.2.1, T, hColTAB, between_symmetry_c X T Q hBetXTQ⟩
    exact ⟨Q, hPerpABQC, l9_8_1_c A B P Q X hTS hTSQX⟩

theorem ex_per_cong_c (A B C D X Y : Tpoint)
    (hAB : A ≠ B) (hXY : X ≠ Y) (hCol : Col A B C) (hNCol : ¬ Col A B D) :
    ∃ P, Per P C A ∧ Cong P C X Y ∧ OS A B P D := by
  obtain ⟨Q, hPerpABQC, hOSABDQ⟩ := l10_15_c A B C D hCol hNCol
  have hQC : Q ≠ C := (perp_distinct_c A B Q C hPerpABQC).2
  obtain ⟨P, hOutCQP, hCongCPXY⟩ := segment_construction_3_c C Q X Y hQC.symm hXY
  have hCP : C ≠ P := cong_diff_3_c C P X Y hXY hCongCPXY
  have hColCQP : Col C Q P := out_col_c C Q P hOutCQP
  have hPerPCA : Per P C A := by
    rcases point_equality_decidability A C with hAC | hAC
    · have hPerPCC : Per P C C := l8_5_c P C
      exact hAC ▸ hPerPCC
    · have hPerpABCP : Perp A B C P :=
        perp_col1_c A B C Q P hCP (perp_right_comm_c A B Q C hPerpABQC) hColCQP
      have hPerpCPAC : Perp C P A C :=
        perp_col1_c C P A B C hAC (perp_sym_c A B C P hPerpABCP) hCol
      exact perp_per_1_c C P A hPerpCPAC
  have hCongPCXY : Cong P C X Y := cong_left_commutativity_c C P X Y hCongCPXY
  have hOSABPD : OS A B P D :=
    os_out_os_c A B Q D P C hCol (one_side_symmetry_c A B D Q hOSABDQ) hOutCQP
  exact ⟨P, hPerPCA, hCongPCXY, hOSABPD⟩

theorem exists_cong_per_c (A B X Y : Tpoint) :
    ∃ C, Per A B C ∧ Cong B C X Y := by
  rcases point_equality_decidability A B with hAB | hAB
  · subst hAB
    obtain ⟨x, hBetXAx, hCongAxXY⟩ := segment_construction X A X Y
    obtain ⟨C', hMidAxC'⟩ := symmetric_point_construction_c x A
    have hCongAxAC' : Cong A x A C' := cong_left_commutativity_c x A A C' hMidAxC'.2
    exact ⟨x, ⟨C', hMidAxC', hCongAxAC'⟩, hCongAxXY⟩
  · obtain ⟨P, hNColABP⟩ := not_col_exists_c A B hAB
    rcases point_equality_decidability X Y with hXY | hXY
    · subst hXY
      exact ⟨B, l8_5_c A B, cong_trivial_identity_c B X⟩
    · obtain ⟨PP, hPerPPBA, hCongPPBXY, _⟩ :=
        ex_per_cong_c A B B P X Y hAB hXY (col_trivial_2_c A B) hNColABP
      exact ⟨PP, l8_2_c PP B A hPerPPBA, cong_left_commutativity_c PP B X Y hCongPPBXY⟩

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
#print axioms GeocoqTranslate.Tarski.Base.col_refl_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_col_cong_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_col_cong_c
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
#print axioms GeocoqTranslate.Tarski.Base.col_image_spec_c
#print axioms GeocoqTranslate.Tarski.Base.image_triv_c
#print axioms GeocoqTranslate.Tarski.Base.cong_midpoint_image_c
#print axioms GeocoqTranslate.Tarski.Base.col_image_spec_eq_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec_triv_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec_eq_c
#print axioms GeocoqTranslate.Tarski.Base.image_midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.is_image_spec_dec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_14_c
#print axioms GeocoqTranslate.Tarski.Base.l10_15_c
#print axioms GeocoqTranslate.Tarski.Base.ex_per_cong_c
#print axioms GeocoqTranslate.Tarski.Base.exists_cong_per_c

end GeocoqTranslate.Tarski.Base
