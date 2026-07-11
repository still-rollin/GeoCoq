import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ts_distincts_c (A B P Q : Tpoint) (h : TS A B P Q) :
    A ≠ B ∧ A ≠ P ∧ A ≠ Q ∧ B ≠ P ∧ B ≠ Q ∧ P ≠ Q := sorry

theorem l9_2_c (A B P Q : Tpoint) (h : TS A B P Q) : TS A B Q P := sorry

theorem mid_preserves_col_c (A B C M A' B' C' : Tpoint)
    (hCol : Col A B C) (h₁ : Midpoint M A A')
    (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') : Col A' B' C' := sorry

theorem per_mid_per_c (A B X Y M : Tpoint)
    (hAB : A ≠ B) (h₁ : Per X A B)
    (h₂ : Midpoint M A B) (h₃ : Midpoint M X Y) :
    Cong A X B Y ∧ Per Y B A := sorry

theorem sym_preserve_diff_c (A B M A' B' : Tpoint)
    (hAB : A ≠ B) (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') :
    A' ≠ B' := sorry

theorem l9_4_1_aux_c (P Q A C R S M : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem per_col_eq_c (A B C : Tpoint)
    (h₁ : Per A B C) (hCol : Col A B C) (hBC : B ≠ C) : A = B := sorry

theorem l9_4_1_c (P Q A C R S M : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem mid_two_sides_c (A B M X Y : Tpoint)
    (h₁ : Midpoint M A B) (hNCol : ¬ Col A B X) (h₂ : Midpoint M X Y) :
    TS A B X Y := sorry

theorem col_preserves_two_sides_c (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h : TS A B X Y) :
    TS C D X Y := sorry

theorem out_out_two_sides_c (A B X Y U V I : Tpoint)
    (hAB : A ≠ B) (h₁ : TS A B X Y)
    (hCol1 : Col I A B) (hCol2 : Col I X Y)
    (hOut1 : Out I X U) (hOut2 : Out I Y V) : TS A B U V := sorry

theorem l9_4_2_aux_c (P Q A C R S U V : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := sorry

theorem l9_4_2_c (P Q A C R S U V : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := sorry

theorem l9_5_c (P Q A C R B : Tpoint)
    (h₁ : TS P Q A C) (hR : Col R P Q) (hOut : Out R A B) : TS P Q B C := sorry

theorem outer_pasch_c (A B C P Q : Tpoint) (h₁ : Bet A C P) (h₂ : Bet B Q C) :
    ∃ X, Bet A X B ∧ Bet P Q X := sorry

theorem os_distincts_c (A B X Y : Tpoint) (h : OS A B X Y) :
    A ≠ B ∧ A ≠ X ∧ A ≠ Y ∧ B ≠ X ∧ B ≠ Y := sorry

theorem invert_one_side_c (A B P Q : Tpoint) (h : OS A B P Q) : OS B A P Q := sorry

theorem l9_8_1_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : TS P Q B C) :
    OS P Q A B :=
  ⟨C, (⟨h₁, h₂⟩)⟩

theorem not_two_sides_id_c (A P Q : Tpoint) : ¬ TS P Q A A := by
  exact fun H => and_ind (fun _ H0 => and_ind (fun H1 H2 => ex_ind (fun T H3 => and_ind (fun H4 H5 => (let H6 := between_identity A T H5; eq_ind A (fun T0 => Col T0 P Q - > False) (fun H7 => H1 H7) T H6 H4)) H3) H2) H0) H

theorem l9_8_2_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : OS P Q A B) :
    TS P Q B C := sorry

theorem l9_9_c (P Q A B : Tpoint) (h : TS P Q A B) : ¬ OS P Q A B :=
  (fun H0 => (let H1 := l9_8_2_c P Q A B B h H0; (let H2 := not_two_sides_id_c P Q H1; H2)))

theorem l9_9_bis_c (P Q A B : Tpoint) (h : OS P Q A B) : ¬ TS P Q A B := by
  exact fun H0 => ex_ind (fun C H1 => and_ind (fun H2 H3 => (let H4 := l9_8_1_c P Q A B C H2 H3; (let H5 := l9_9_c P Q A B H0; False_ind False (H5 H4)))) H1) h

theorem one_side_chara_c (P Q A B : Tpoint) (h : OS P Q A B) :
    ∀ X, Col X P Q → ¬ Bet A X B := sorry

theorem l9_10_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) : ∃ C, TS P Q A C := sorry

theorem one_side_reflexivity_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) :
    OS P Q A A := sorry

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
    TS X Y A B ↔ (Bet A P B ∧ ¬ Col X Y A ∧ ¬ Col X Y B) := sorry

theorem l9_19_c (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    OS X Y A B ↔ (Out P A B ∧ ¬ Col X Y A) := sorry

theorem one_side_not_col123_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B X := sorry

theorem one_side_not_col124_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B Y :=
  one_side_not_col123_c A B Y X (one_side_symmetry_c A B X Y h)

theorem col_two_sides_c (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : TS A B P Q) : TS A C P Q := sorry

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
    (hAY : A ≠ Y) (hNCol : ¬ Col A B X) (hBet : Bet X A Y) : TS A B X Y := sorry

theorem bet_ts__ts_c (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    TS A B X Z := sorry

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
    OS C D X Y := sorry

theorem os_out_os_c (A B C D C' P : Tpoint)
    (hCol : Col A B P) (h₁ : OS A B C D) (h₂ : Out P C C') :
    OS A B C' D := sorry

theorem ts_ts_os_c (A B C D : Tpoint) (h₁ : TS A B C D) (h₂ : TS C D A B) :
    OS A C B D := sorry

theorem two_sides_not_col_c (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A B X := sorry

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
    ¬ Col A X Y ∨ ¬ Col B X Y := sorry

theorem one_or_two_sides_aux_c (A B C D X : Tpoint)
    (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (h₁ : Col A C X) (h₂ : Col B D X) : TS A B C D ∨ OS A B C D := sorry

theorem cop__one_or_two_sides_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B) :
    TS A B C D ∨ OS A B C D := sorry

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
    (hCop : Coplanar A B C E) (hBet : Bet C D E) : Coplanar A B C D := sorry

theorem col2_cop__cop_c (A B C D E F : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D)
    (h₁ : Col C D E) (h₂ : Col C D F) : Coplanar A B E F := sorry

theorem col_cop2__cop_c (A B C U V P : Tpoint)
    (hUV : U ≠ V) (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C V)
    (hCol : Col U V P) : Coplanar A B C P := sorry

theorem bet_cop2__cop_c (A B C U V W : Tpoint)
    (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C W) (hBet : Bet U V W) :
    Coplanar A B C V := sorry

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
  · exact False_ind (OS A B C D) (hNTS H3)
  · exact H3

theorem cop_nos__ts_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNOS : ¬ OS A B C D) : TS A B C D := by
  have o := cop__one_or_two_sides_c A B C D hCop hNC1 hNC2
  rcases o with H3 | H3
  · exact H3
  · exact False_ind (TS A B C D) (hNOS H3)

theorem one_side_dec_c (A B C D : Tpoint) : OS A B C D ∨ ¬ OS A B C D := sorry

theorem cop_dec_c (A B C D : Tpoint) : Coplanar A B C D ∨ ¬ Coplanar A B C D := sorry

theorem ex_diff_cop_c (A B C D : Tpoint) :
    ∃ E, Coplanar A B C E ∧ D ≠ E := sorry

theorem ex_ncol_cop_c (A B C D E : Tpoint) (hDE : D ≠ E) :
    ∃ F, Coplanar A B C F ∧ ¬ Col D E F := sorry

theorem ex_ncol_cop2_c (A B C D : Tpoint) :
    ∃ E F, Coplanar A B C E ∧ Coplanar A B C F ∧ ¬ Col D E F := sorry

theorem col2_cop2__eq_c (A B C U V P Q : Tpoint)
    (hNCop : ¬ Coplanar A B C U) (hUV : U ≠ V)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q)
    (h₃ : Col U V P) (h₄ : Col U V Q) : P = Q := sorry

theorem cong3_cop2__col_c (A B C P Q : Tpoint)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q) (hPQ : P ≠ Q)
    (h₃ : Cong A P A Q) (h₄ : Cong B P B Q) (h₅ : Cong C P C Q) :
    Col A B C := sorry

theorem l9_38_c (A B C P Q : Tpoint) (h : TSP A B C P Q) : TSP A B C Q P := sorry

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
    OSP A B C Q P := sorry

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
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := sorry

theorem tsp_distincts_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q ∧ P ≠ Q := sorry

theorem osp_distincts_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q := sorry

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
    ¬ Coplanar A B C P := sorry

theorem osp__ncop2_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C Q := sorry

theorem tsp__nosp_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ OSP A B C P Q := sorry

theorem osp__ntsp_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ TSP A B C P Q :=
  (fun HTS => tsp__nosp_c B C P Q HTS h)

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
    (h₃ : Coplanar D E X Y) (h₄ : TSP A B C X Y) : TS D E X Y := sorry

theorem cop3_osp__os_c (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : OSP A B C X Y) : OS D E X Y := sorry

theorem cop_tsp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : TSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := sorry

theorem cop_osp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : OSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := sorry

theorem sac__coplanar_c (A B C D : Tpoint) (h : Saccheri A B C D) :
    Coplanar A B C D := sorry

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
end GeocoqTranslate.Tarski.Base