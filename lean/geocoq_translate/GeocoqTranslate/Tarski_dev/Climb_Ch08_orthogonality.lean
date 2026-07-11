import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem per_dec_c (A B C : Tpoint) : Per A B C ∨ ¬ Per A B C := sorry

theorem l8_2_c (A B C : Tpoint) (h : Per A B C) : Per C B A := sorry

theorem Per_cases_c (A B C : Tpoint) (h : Per A B C ∨ Per C B A) : Per A B C := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · exact l8_2_c C B A H1

theorem Per_perm_c (A B C : Tpoint) (h : Per A B C) : Per A B C ∧ Per C B A :=
  ⟨h, (l8_2_c A B C h)⟩

theorem l8_3_c (A B C A' : Tpoint)
    (h₁ : Per A B C) (hAB : A ≠ B) (hCol : Col B A A') : Per A' B C := sorry

theorem l8_4_c (A B C C' : Tpoint) (h₁ : Per A B C) (h₂ : Midpoint B C C') :
    Per A B C' := sorry

theorem l8_5_c (A B : Tpoint) : Per A B B := sorry

theorem l8_6_c (A B C A' : Tpoint)
    (h₁ : Per A B C) (h₂ : Per A' B C) (h₃ : Bet A C A') : B = C := sorry

theorem l8_7_c (A B C : Tpoint) (h₁ : Per A B C) (h₂ : Per A C B) : B = C := sorry

theorem l8_8_c (A B : Tpoint) (h : Per A B A) : A = B :=
  l8_7_c A A B (l8_2_c B A A (l8_5_c B A)) h

theorem per_distinct_c (A B C : Tpoint) (h : Per A B C) (hAB : A ≠ B) : A ≠ C :=
  (fun H1 => eq_ind A (fun C0 => Per A B C0 - > False) (fun H2 => hAB (l8_8_c A B H2)) C H1 h)

theorem per_distinct_1_c (A B C : Tpoint) (h : Per A B C) (hBC : B ≠ C) :
    A ≠ C :=
  (fun H1 => eq_ind A (fun C0 => Per A B C0 - > B <> C0 - > False) (fun H2 H3 => H3 (Eq.symm (l8_8_c A B H2))) C H1 h hBC)

theorem l8_9_c (A B C : Tpoint) (h₁ : Per A B C) (hCol : Col A B C) :
    A = B ∨ C = B := sorry

theorem l8_10_c (A B C A' B' C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Cong_3 A B C A' B' C') : Per A' B' C' := sorry

theorem col_col_per_per_c (A X C U V : Tpoint)
    (hAX : A ≠ X) (hCX : C ≠ X)
    (h₁ : Col U A X) (h₂ : Col V C X) (h₃ : Per A X C) : Per U X V := sorry

theorem perp_in_dec_c (X A B C D : Tpoint) :
    Perp_at X A B C D ∨ ¬ Perp_at X A B C D := sorry

theorem perp_distinct_c (A B C D : Tpoint) (h : Perp A B C D) :
    A ≠ B ∧ C ≠ D := by
  obtain ⟨X, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, _⟩ := H5
  exact ⟨((fun H6 => (let H7 := H1 H6; False_ind False H7))), ((fun H6 => (let H7 := H3 H6; False_ind False H7)))⟩

theorem l8_12_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X C D A B := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  exact ⟨H2, (⟨H0, (⟨H6, (⟨H4, (fun U V H8 H9 => l8_2_c V X U (H7 V U H9 H8))⟩)⟩)⟩)⟩

theorem per_col_c (A B C D : Tpoint)
    (hBC : B ≠ C) (h₁ : Per A B C) (hCol : Col B C D) : Per A B D := sorry

theorem l8_13_2_c (A B C D X : Tpoint)
    (hAB : A ≠ B) (hCD : C ≠ D) (hCol1 : Col X A B) (hCol2 : Col X C D)
    (h : ∃ U V : Tpoint, Col U A B ∧ Col V C D ∧ U ≠ X ∧ V ≠ X ∧ Per U X V) :
    Perp_at X A B C D := sorry

theorem l8_14_1_c (A B : Tpoint) : ¬ Perp A B A B := sorry

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
  exact l8_14_2_1b_bis_c A B C D X h₁ (ex_ind (fun Y H1 => and_ind (fun _ H2 => and_ind (fun _ H3 => and_ind (fun H4 H5 => and_ind (fun H6 H7 => (let H8 := H6; (let H9 := h₂ Y H4 H6; eq_ind X (fun Y0 => Col Y0 A B - > (forall U V) - > Col Y0 C D - > Col X A B) (fun H10 _ _ => H10) Y H9 H4 H7 H8))) H5) H3) H2) H1) h₁) (ex_ind (fun Y H1 => and_ind (fun _ H2 => and_ind (fun _ H3 => and_ind (fun H4 H5 => and_ind (fun H6 H7 => (let H8 := H6; (let H9 := h₂ Y H4 H6; eq_ind X (fun Y0 => Col Y0 A B - > (forall U V) - > Col Y0 C D - > Col X C D) (fun _ _ H10 => H10) Y H9 H4 H7 H8))) H5) H3) H2) H1) h₁)

theorem l8_14_3_c (A B C D X Y : Tpoint)
    (h₁ : Perp_at X A B C D) (h₂ : Perp_at Y A B C D) : X = Y := by
  exact l8_14_2_1b_c X A B C D Y h₁ (and_ind (fun _ H2 => and_ind (fun _ H3 => and_ind (fun H4 H5 => and_ind (fun _ _ => H4) H5) H3) H2) h₂) ((let H1 := l8_12_c A B C D Y h₂; and_ind (fun _ H2 => and_ind (fun _ H3 => and_ind (fun H4 H5 => and_ind (fun _ _ => H4) H5) H3) H2) H1))

theorem l8_15_1_c (A B C X : Tpoint) (hCol : Col A B X) (h : Perp A B C X) :
    Perp_at X A B C X := sorry

theorem l8_15_2_c (A B C X : Tpoint) (hCol : Col A B X) (h : Perp_at X A B C X) :
    Perp A B C X :=
  l8_14_2_1a_c X A B C X h

theorem perp_in_per_c (A B C : Tpoint) (h : Perp_at B A B B C) : Per A B C := sorry

theorem perp_sym_c (A B C D : Tpoint) (h : Perp A B C D) : Perp C D A B := by
  obtain ⟨X, H0⟩ := h
  exact ⟨X, (l8_12_c A B C D X H0)⟩

theorem perp_col0_c (A B C D X Y : Tpoint)
    (h₁ : Perp A B C D) (hXY : X ≠ Y) (hX : Col A B X) (hY : Col A B Y) :
    Perp C D X Y := sorry

theorem per_perp_in_c (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp_at B A B B C := sorry

theorem per_perp_c (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp A B B C :=
  (let H2 := per_perp_in_c A B C hAB hBC h; l8_14_2_1a_c B A B B C H2)

theorem perp_left_comm_c (A B C D : Tpoint) (h : Perp A B C D) :
    Perp B A C D := sorry

theorem perp_right_comm_c (A B C D : Tpoint) (h : Perp A B C D) :
    Perp A B D C := sorry

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
    Perp_at X B A C D := sorry

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
    Col A B X ∧ Col C D X := sorry

theorem perp_perp_in_c (A B C : Tpoint) (h : Perp A B C A) : Perp_at A A B C A := sorry

theorem perp_per_1_c (A B C : Tpoint) (h : Perp A B C A) : Per B A C := sorry

theorem perp_per_2_c (A B C : Tpoint) (h : Perp A B A C) : Per B A C :=
  (let H0 := perp_right_comm_c A B A C h; perp_per_1_c A B C H0)

theorem perp_col_c (A B C D E : Tpoint)
    (hAE : A ≠ E) (h₁ : Perp A B C D) (h₂ : Col A B E) : Perp A E C D := sorry

theorem perp_col2_c (A B C D X Y : Tpoint)
    (h₁ : Perp A B X Y) (hCD : C ≠ D) (hC : Col A B C) (hD : Col A B D) :
    Perp C D X Y := sorry

theorem perp_col4_c (A B C D P Q R S : Tpoint)
    (hPQ : P ≠ Q) (hRS : R ≠ S)
    (h₁ : Col A B P) (h₂ : Col A B Q) (h₃ : Col C D R) (h₄ : Col C D S)
    (h : Perp A B C D) : Perp P Q R S :=
  perp_col2_c A B P Q R S (perp_sym_c R S A B (perp_col2_c C D R S A B (perp_sym_c A B C D h) hRS h₃ h₄)) hPQ h₁ h₂

theorem perp_not_eq_1_c (A B C D : Tpoint) (h : Perp A B C D) : A ≠ B := by
  obtain ⟨X, H0⟩ := h
  exact fun H1 => and_ind (fun H2 H3 => and_ind (fun _ H4 => and_ind (fun _ H5 => and_ind (fun _ _ => (let H6 := H2 H1; False_ind False H6)) H5) H4) H3) H0

theorem perp_not_eq_2_c (A B C D : Tpoint) (h : Perp A B C D) : C ≠ D :=
  (let H0 := perp_sym_c A B C D h; perp_not_eq_1_c C D A B H0)

theorem diff_per_diff_c (A B P R : Tpoint)
    (hAB : A ≠ B) (h₁ : Cong A P B R) (h₂ : Per B A P) (h₃ : Per A B R) :
    P ≠ R := by
  exact fun H3 => eq_ind_r (fun P0 => Cong A P0 B R - > Per B A P0 - > False) (fun _ H4 => (let H5 := l8_7_c R A B (l8_2_c B A R H4) (l8_2_c A B R h₃); (let H6 := hAB H5; False_ind False H6))) H3 h₁ h₂

theorem per_not_colp_c (A B P R : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBR : B ≠ R)
    (h₁ : Per B A P) (h₂ : Per A B R) : ¬ Col P A R := sorry

theorem per_not_col_c (A B C : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) : ¬ Col A B C := sorry

theorem perp_not_col2_c (A B C D : Tpoint) (h : Perp A B C D) :
    ¬ Col A B C ∨ ¬ Col A B D := sorry

theorem perp_not_col_c (A B P : Tpoint) (h : Perp A B P A) : ¬ Col A B P := sorry

theorem perp_in_col_perp_in_c (A B C D E P : Tpoint)
    (hCE : C ≠ E) (hCol : Col C D E) (h : Perp_at P A B C D) :
    Perp_at P A B C E := sorry

theorem perp_col2_bis_c (A B C D P Q : Tpoint)
    (h₁ : Perp A B C D) (h₂ : Col C D P) (h₃ : Col C D Q) (hPQ : P ≠ Q) :
    Perp A B P Q :=
  perp_sym_c P Q A B (perp_col2_c C D P Q A B (perp_comm_c D C B A (perp_comm_c C D A B (perp_sym_c A B C D h₁))) hPQ h₂ h₃)

theorem perp_in_perp_bis_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp X B C D ∨ Perp A X C D := sorry

theorem col_per_perp_c (A B C D : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hDB : D ≠ B) (hDC : D ≠ C)
    (hCol : Col B C D) (h : Per A B C) : Perp C D A B := sorry

theorem per_cong_mid_c (A B C H : Tpoint)
    (hBC : B ≠ C) (h₁ : Bet A B C) (h₂ : Cong A H C H) (h₃ : Per H B C) :
    Midpoint B A C := sorry

theorem per_double_cong_c (A B C C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint B C C') : Cong A C A C' := sorry

theorem cong_perp_or_mid_c (A B M X : Tpoint)
    (hAB : A ≠ B) (hM : Midpoint M A B) (h : Cong A X B X) :
    X = M ∨ ¬ Col A B X ∧ Perp_at M X M A B := sorry

theorem col_per2_cases_c (A B C D B' : Tpoint)
    (hBC : B ≠ C) (hB'C : B' ≠ C) (hCD : C ≠ D)
    (hCol : Col B C D) (h₁ : Per A B C) (h₂ : Per A B' C) :
    B = B' ∨ ¬ Col B' C D := sorry

theorem l8_16_1_c (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (h : Perp A B C X) :
    ¬ Col A B C ∧ Per C X U := sorry

theorem l8_16_2_c (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (hUX : U ≠ X)
    (hNCol : ¬ Col A B C) (h : Per C X U) : Perp A B C X := sorry

theorem l8_18_uniqueness_c (A B C X Y : Tpoint)
    (hNCol : ¬ Col A B C)
    (h₁ : Col A B X) (h₂ : Perp A B C X)
    (h₃ : Col A B Y) (h₄ : Perp A B C Y) : X = Y := sorry

theorem midpoint_distinct_c (A B X C C' : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (h : Midpoint X C C') :
    C ≠ C' := by
  exact fun H2 => eq_ind C (fun C'0 => Midpoint X C C'0 - > False) (fun H3 => hNCol (and_ind (fun H4 H5 => (let H6 := between_identity C X H4; eq_ind C (fun X0 => Col A B X0 - > Cong C X0 X0 C - > Col A B C) (fun H7 _ => H7) X H6 hCol H5)) H3)) C' H2 h

theorem l8_20_1_c (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C) : Per B A P := sorry

theorem l8_20_2_c (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C)
    (hBC : B ≠ C) : A ≠ P := sorry

theorem perp_col1_c (A B C D X : Tpoint)
    (hCX : C ≠ X) (h₁ : Perp A B C D) (h₂ : Col C D X) : Perp A B C X := sorry

theorem l8_18_existence_c (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ X, Col A B X ∧ Perp A B C X := sorry

theorem l8_21_aux_c (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := sorry

theorem l8_21_c (A B C : Tpoint) (hAB : A ≠ B) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := sorry

theorem per_cong_c (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Per B A P) (h₂ : Per A B R) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) : Cong A R P B := sorry

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
    ∃ X : Tpoint, Midpoint X A B := sorry

theorem midpoint_existence_c (A B : Tpoint) : ∃ X, Midpoint X A B := sorry

theorem perp_in_id_c (A B C X : Tpoint) (h : Perp_at X A B C A) : X = A := sorry

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
    ∃ X, Col A B X ∧ Perp A X C D := sorry

theorem l8_24_c (A B P Q R T : Tpoint)
    (h₁ : Perp P A A B) (h₂ : Perp Q B A B)
    (h₃ : Col A B T) (h₄ : Bet P T Q) (h₅ : Bet B R Q) (h₆ : Cong A P B R) :
    ∃ X, Midpoint X A B ∧ Midpoint X P R := sorry

theorem col_per2__per_c (A B C P X : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Per A X P) (h₂ : Per B X P) : Per C X P := sorry

theorem perp_in_per_1_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X C := sorry

theorem perp_in_per_2_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X D := sorry

theorem perp_in_per_3_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X C := sorry

theorem perp_in_per_4_c (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X D := sorry

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