import GeocoqTranslate.Tarski_dev.Ch13b

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ang_exists_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA a ∧ a A B C :=
  fun b0 b1 b2 b3 b4 =>
  ⟨(fun D E F => CongA b0 b1 b2 D E F), (⟨(⟨b0, (⟨b1, (⟨b2, (⟨b3, (⟨b4, (fun X Y Z => ⟨(fun H1 => H1), (fun H1 => H1)⟩)⟩)⟩)⟩)⟩)⟩), (conga_refl_c b0 b1 b2 b3 b4)⟩)⟩

theorem ex_points_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA a → ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), a A B C := by
  intro b0 b1
  obtain ⟨A, H0⟩ := b1
  obtain ⟨B, H1⟩ := H0
  obtain ⟨C, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  have HH := H6 A B C
  obtain ⟨x, x0⟩ := HH
  exact ⟨A, (⟨B, (⟨C, (x (conga_refl_c A B C H3 H5))⟩)⟩)⟩

theorem ang_conga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' B' C' : Tpoint), Q_CongA a → a A B C → a A' B' C' → CongA A B C A' B' C' := sorry
theorem is_ang_conga_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang A B C a → Ang A' B' C' a → CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b8
  obtain ⟨_, H3⟩ := b7
  exact ang_conga_c b6 b0 b1 b2 b3 b4 b5 H1 H3 H2

theorem is_ang_conga_is_ang_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang A B C a → CongA A B C A' B' C' → Ang A' B' C' a := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b7
  exact ⟨H1, ((by
  obtain ⟨A0, H3⟩ := H1
  obtain ⟨B0, H4⟩ := H3
  obtain ⟨C0, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  have HH := H7 b0 b1 b2
  obtain ⟨x, x0⟩ := HH
  have HH1 := H7 b3 b4 b5
  obtain ⟨x1, x2⟩ := HH1
  have H10 := x0 H2
  exact x1 (conga_trans_c A0 B0 C0 b0 b1 b2 b3 b4 b5 H10 b8)))⟩

theorem not_conga_not_ang_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA a → ¬ (CongA A B C A' B' C') → a A B C → ¬ (a A' B' C') :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  (fun H2 => (let HH := ang_conga_c b6 b0 b1 b2 b3 b4 b5 b7 b9 H2; ((b8 HH)).elim))

theorem not_conga_is_ang_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), ¬ (CongA A B C A' B' C') → Ang A B C a → ¬ (a A' B' C') := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b8
  intro H3
  exact b7 (ang_conga_c b6 b0 b1 b2 b3 b4 b5 H1 H2 H3)

theorem not_cong_is_ang1_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), ¬ (CongA A B C A' B' C') → Ang A B C a → ¬ (Ang A' B' C' a) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  intro H1
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := b8
  exact b7 (ang_conga_c b6 b0 b1 b2 b3 b4 b5 H2 H4 H3)

theorem ex_eqa_c :
    ∀ (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), (∃ A , ∃ (B : Tpoint), ∃ (C : Tpoint), Ang A B C a1 ∧ Ang A B C a2) → EqA a1 a2 := by
  intro b0 b1 b2
  obtain ⟨A, H0⟩ := b2
  obtain ⟨B, H1⟩ := H0
  obtain ⟨C, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have HH := H3
  have HH0 := H4
  obtain ⟨H5, _⟩ := HH0
  obtain ⟨H6, _⟩ := HH
  intro A0 B0 C0
  exact ⟨(fun H7 => (let H8 := is_ang_conga_c A B C A0 B0 C0 b0 H3 (⟨H6, H7⟩); (let H9 := is_ang_conga_is_ang_c A B C A0 B0 C0 b1 H4 H8; (by
  obtain ⟨_, H10⟩ := H9
  exact H10)))), (fun H7 => (let H8 := is_ang_conga_c A B C A0 B0 C0 b1 H4 (⟨H5, H7⟩); (let H9 := is_ang_conga_is_ang_c A B C A0 B0 C0 b0 H3 H8; (by
  obtain ⟨_, H10⟩ := H9
  exact H10))))⟩

theorem all_eqa_c :
    ∀ (A B C : Tpoint) (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), Ang A B C a1 → Ang A B C a2 → EqA a1 a2 :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  ex_eqa_c b3 b4 (⟨b0, (⟨b1, (⟨b2, (⟨b5, b6⟩)⟩)⟩)⟩)

theorem is_ang_distinct_c :
    ∀ (A B C : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang A B C a → A ≠ B ∧ C ≠ B := by
  intro b0 b1 b2 b3 b4
  obtain ⟨H0, H1⟩ := b4
  obtain ⟨A0, H2⟩ := H0
  obtain ⟨B0, H3⟩ := H2
  obtain ⟨C0, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  have HH := H6 b0 b1 b2
  obtain ⟨x, x0⟩ := HH
  have H8 := x0 H1
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, _⟩ := H12
  exact ⟨((fun H14 => (let H15 := H11 H14; (H15).elim))), ((fun H14 => (let H15 := H13 H14; (H15).elim)))⟩
theorem null_ang_c :
    ∀ (A B C D : Tpoint) (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), Ang A B A a1 → Ang C D C a2 → EqA a1 a2 := sorry
theorem flat_ang_c :
    ∀ (A B C A' B' C' : Tpoint) (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), Bet A B C → Bet A' B' C' → Ang A B C a1 → Ang A' B' C' a2 → EqA a1 a2 := sorry
theorem ang_distinct_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → A ≠ B ∧ C ≠ B :=
  fun b0 b1 b2 b3 b4 b5 =>
  (let H1 := ⟨b4, b5⟩; is_ang_distinct_c b1 b2 b3 b0 H1)

theorem ex_ang_c :
    ∀ (A B C : Tpoint), B ≠ A → B ≠ C → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA a ∧ a A B C :=
  fun b0 b1 b2 b3 b4 =>
  ⟨(fun X Y Z => CongA b0 b1 b2 X Y Z), (⟨(⟨b0, (⟨b1, (⟨b2, (⟨(Ne.symm b3), (⟨(Ne.symm b4), (fun X Y Z => ⟨(fun H1 => H1), (fun H1 => H1)⟩)⟩)⟩)⟩)⟩)⟩), (conga_refl_c b0 b1 b2 (Ne.symm b3) (Ne.symm b4))⟩)⟩

theorem anga_exists_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → Acute A B C → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a ∧ a A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  ⟨(fun D E F => CongA b0 b1 b2 D E F), (⟨(⟨b0, (⟨b1, (⟨b2, (⟨b5, (fun X Y Z => ⟨(fun H2 => H2), (fun H2 => H2)⟩)⟩)⟩)⟩)⟩), (conga_refl_c b0 b1 b2 b3 b4)⟩)⟩

theorem anga_is_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_CongA a := sorry
theorem ex_points_anga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), a A B C := by
  intro b0 b1
  have HH := b1
  have H0 := anga_is_ang_c b0 b1
  have tempo_ang := ex_points_ang_c b0
  have tempo_H := H0
  have tempo_H0 := tempo_ang tempo_H
  obtain ⟨A, tempo_HP⟩ := tempo_H0
  obtain ⟨B, tempo_HQ⟩ := tempo_HP
  obtain ⟨C, H1⟩ := tempo_HQ
  exact ⟨A, (⟨B, (⟨C, H1⟩)⟩)⟩

theorem anga_conga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' B' C' : Tpoint), Q_CongA_Acute a → a A B C → a A' B' C' → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ang_conga_c b0 b1 b2 b3 b4 b5 b6 (anga_is_ang_c b0 b7) b8 b9

theorem is_anga_to_is_ang_c :
    ∀ (A B C : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B C a → Ang A B C a := by
  intro b0 b1 b2 b3 b4
  obtain ⟨H0, H1⟩ := b4
  exact ⟨(anga_is_ang_c b3 H0), H1⟩

theorem is_anga_conga_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B C a → Ang_Acute A' B' C' a → CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b8
  obtain ⟨_, H3⟩ := b7
  exact anga_conga_c b6 b0 b1 b2 b3 b4 b5 H1 H3 H2

theorem is_anga_conga_is_anga_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B C a → CongA A B C A' B' C' → Ang_Acute A' B' C' a := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b7
  exact ⟨H1, ((let H3 := anga_is_ang_c b6 H1; (by
  obtain ⟨A0, H4⟩ := H3
  obtain ⟨B0, H5⟩ := H4
  obtain ⟨C0, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  have HH := H8 b0 b1 b2
  obtain ⟨x, x0⟩ := HH
  have HH1 := H8 b3 b4 b5
  obtain ⟨x1, x2⟩ := HH1
  have H11 := x0 H2
  exact x1 (conga_trans_c A0 B0 C0 b0 b1 b2 b3 b4 b5 H11 b8))))⟩

theorem not_conga_is_anga_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), ¬ CongA A B C A' B' C' → Ang_Acute A B C a → ¬ (a A' B' C') := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b8
  intro H3
  exact b7 (anga_conga_c b6 b0 b1 b2 b3 b4 b5 H1 H2 H3)

theorem not_cong_is_anga1_c :
    ∀ (A B C A' B' C' : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), ¬ CongA A B C A' B' C' → Ang_Acute A B C a → ¬ Ang_Acute A' B' C' a := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  intro H1
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := b8
  exact b7 (anga_conga_c b6 b0 b1 b2 b3 b4 b5 H2 H4 H3)

theorem ex_eqaa_c :
    ∀ (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), (∃ A , ∃ (B : Tpoint), ∃ (C : Tpoint), Ang_Acute A B C a1 ∧ Ang_Acute A B C a2) → EqA a1 a2 := by
  intro b0 b1 b2
  exact ex_eqa_c b0 b1 ((by
  obtain ⟨A, H0⟩ := b2
  obtain ⟨B, H1⟩ := H0
  obtain ⟨C, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact ⟨A, (⟨B, (⟨C, (⟨(is_anga_to_is_ang_c A B C b0 H3), (is_anga_to_is_ang_c A B C b1 H4)⟩)⟩)⟩)⟩))

theorem all_eqaa_c :
    ∀ (A B C : Tpoint) (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B C a1 → Ang_Acute A B C a2 → EqA a1 a2 :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  ex_eqaa_c b3 b4 (⟨b0, (⟨b1, (⟨b2, (⟨b5, b6⟩)⟩)⟩)⟩)

theorem is_anga_distinct_c :
    ∀ (A B C : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B C a → A ≠ B ∧ C ≠ B :=
  fun b0 b1 b2 b3 b4 =>
  is_ang_distinct_c b0 b1 b2 b3 (is_anga_to_is_ang_c b0 b1 b2 b3 b4)

theorem null_anga_c :
    ∀ (A B C D : Tpoint) (a1 a2 : Tpoint → Tpoint → Tpoint → Prop), Ang_Acute A B A a1 → Ang_Acute C D C a2 → EqA a1 a2 := sorry

theorem anga_distinct_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → A ≠ B ∧ C ≠ B := sorry

theorem out_is_len_eq_c :
    ∀ (A B C : Tpoint) (l : Tpoint → Tpoint → Prop), Out A B C → Len A B l → Len A C l → B = C := sorry

theorem out_len_eq_c :
    ∀ (A B C : Tpoint) (l : Tpoint → Tpoint → Prop), Q_Cong l → Out A B C → l A B → l A C → B = C := sorry

theorem ex_anga_c :
    ∀ (A B C : Tpoint), Acute A B C → ∃ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a ∧ a A B C := sorry

theorem not_null_ang_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_nNull a → Q_CongA a := sorry

theorem not_null_ang_def_equiv_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_nNull a ↔ (Q_CongA a ∧ ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), a A B C ∧ ¬ Out B A C) := sorry

theorem not_flat_ang_def_equiv_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_nFlat a ↔ (Q_CongA a ∧ ∃ (A : Tpoint), ∃ (B : Tpoint), ∃ (C : Tpoint), a A B C ∧ ¬ Bet A B C) := sorry

theorem ang_const_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B : Tpoint), Q_CongA a → A ≠ B → ∃ (C : Tpoint), a A B C := sorry

theorem ang_sym_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → a C B A := sorry

theorem ang_not_null_lg_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (l : Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → Q_Cong l → a A B C → l A B → ¬ Q_Cong_Null l := sorry

theorem ang_distincts_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → A ≠ B ∧ C ≠ B := sorry

theorem anga_sym_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → a C B A := sorry

theorem anga_not_null_lg_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (l : Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → Q_Cong l → a A B C → l A B → ¬ Q_Cong_Null l := sorry

theorem anga_distincts_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → A ≠ B ∧ C ≠ B := sorry

theorem ang_const_o_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B P : Tpoint), ¬ Col A B P → Q_CongA a → Q_CongA_nNull a → Q_CongA_nFlat a → ∃ (C : Tpoint), a A B C ∧ OS A B C P := sorry

theorem anga_const_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B : Tpoint), Q_CongA_Acute a → A ≠ B → ∃ (C : Tpoint), a A B C := sorry

theorem is_null_anga_out_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → Q_CongA_Null_Acute a → Out B A C := sorry

theorem acute_not_bet_c :
    ∀ (A B C : Tpoint), Acute A B C → ¬ Bet A B C := sorry

theorem anga_acute_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → Acute A B C := sorry

theorem not_null_not_col_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → ¬ Q_CongA_Null_Acute a → a A B C → ¬ Col A B C := sorry

theorem ang_cong_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' B' C' : Tpoint), Q_CongA a → a A B C → CongA A B C A' B' C' → a A' B' C' := sorry

theorem is_null_ang_out_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → Q_CongA_Null a → Out B A C := sorry

theorem out_null_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → Out B A C → Q_CongA_Null a := sorry

theorem bet_flat_ang_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA a → a A B C → Bet A B C → Ang_Flat a := sorry

theorem out_null_anga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → Out B A C → Q_CongA_Null_Acute a := sorry

theorem anga_not_flat_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_CongA_nFlat a := sorry

theorem anga_const_o_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B P : Tpoint), ¬ Col A B P → ¬ Q_CongA_Null_Acute a → Q_CongA_Acute a → ∃ (C : Tpoint), a A B C ∧ OS A B C P := sorry

theorem anga_conga_anga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' B' C' : Tpoint), Q_CongA_Acute a → a A B C → CongA A B C A' B' C' → a A' B' C' := sorry

theorem anga_out_anga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' C' : Tpoint), Q_CongA_Acute a → a A B C → Out B A A' → Out B C C' → a A' B C' := sorry

theorem out_out_anga_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C A' B' C' : Tpoint), Q_CongA_Acute a → Out B A C → Out B' A' C' → a A B C → a A' B' C' := sorry

theorem is_null_all_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B : Tpoint), A ≠ B → Q_CongA_Null_Acute a → a A B A := sorry

theorem anga_col_out_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → Col A B C → Out B A C := sorry

theorem ang_not_lg_null_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (la lc : Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_Cong la → Q_Cong lc → Q_CongA a → la A B → lc C B → a A B C → ¬ Q_Cong_Null la ∧ ¬ Q_Cong_Null lc := sorry

theorem anga_not_lg_null_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (la lc : Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_Cong la → Q_Cong lc → Q_CongA_Acute a → la A B → lc C B → a A B C → ¬ Q_Cong_Null la ∧ ¬ Q_Cong_Null lc := sorry

theorem anga_col_null_c :
    ∀ (a : Tpoint → Tpoint → Tpoint → Prop) (A B C : Tpoint), Q_CongA_Acute a → a A B C → Col A B C → Out B A C ∧ Q_CongA_Null_Acute a := sorry

theorem eqA_preserves_ang_c :
    ∀ (a b : Tpoint → Tpoint → Tpoint → Prop), Q_CongA a → EqA a b → Q_CongA b := sorry

theorem eqA_preserves_anga_c :
    ∀ (a b : Tpoint → Tpoint → Tpoint → Prop), Q_CongA_Acute a → Q_CongA b → EqA a b → Q_CongA_Acute b := sorry

#print axioms GeocoqTranslate.Tarski.Base.ang_exists_c
#print axioms GeocoqTranslate.Tarski.Base.ex_points_ang_c
#print axioms GeocoqTranslate.Tarski.Base.ang_conga_c
#print axioms GeocoqTranslate.Tarski.Base.is_ang_conga_c
#print axioms GeocoqTranslate.Tarski.Base.is_ang_conga_is_ang_c
#print axioms GeocoqTranslate.Tarski.Base.not_conga_not_ang_c
#print axioms GeocoqTranslate.Tarski.Base.not_conga_is_ang_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_is_ang1_c
#print axioms GeocoqTranslate.Tarski.Base.ex_eqa_c
#print axioms GeocoqTranslate.Tarski.Base.all_eqa_c
#print axioms GeocoqTranslate.Tarski.Base.is_ang_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.null_ang_c
#print axioms GeocoqTranslate.Tarski.Base.flat_ang_c
#print axioms GeocoqTranslate.Tarski.Base.ang_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.ex_ang_c
#print axioms GeocoqTranslate.Tarski.Base.anga_exists_c
#print axioms GeocoqTranslate.Tarski.Base.anga_is_ang_c
#print axioms GeocoqTranslate.Tarski.Base.ex_points_anga_c
#print axioms GeocoqTranslate.Tarski.Base.anga_conga_c
#print axioms GeocoqTranslate.Tarski.Base.is_anga_to_is_ang_c
#print axioms GeocoqTranslate.Tarski.Base.is_anga_conga_c
#print axioms GeocoqTranslate.Tarski.Base.is_anga_conga_is_anga_c
#print axioms GeocoqTranslate.Tarski.Base.not_conga_is_anga_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_is_anga1_c
#print axioms GeocoqTranslate.Tarski.Base.ex_eqaa_c
#print axioms GeocoqTranslate.Tarski.Base.all_eqaa_c
#print axioms GeocoqTranslate.Tarski.Base.is_anga_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.null_anga_c
#print axioms GeocoqTranslate.Tarski.Base.anga_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.out_is_len_eq_c
#print axioms GeocoqTranslate.Tarski.Base.out_len_eq_c
#print axioms GeocoqTranslate.Tarski.Base.ex_anga_c
#print axioms GeocoqTranslate.Tarski.Base.not_null_ang_ang_c
#print axioms GeocoqTranslate.Tarski.Base.not_null_ang_def_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.not_flat_ang_def_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.ang_const_c
#print axioms GeocoqTranslate.Tarski.Base.ang_sym_c
#print axioms GeocoqTranslate.Tarski.Base.ang_not_null_lg_c
#print axioms GeocoqTranslate.Tarski.Base.ang_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.anga_sym_c
#print axioms GeocoqTranslate.Tarski.Base.anga_not_null_lg_c
#print axioms GeocoqTranslate.Tarski.Base.anga_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.ang_const_o_c
#print axioms GeocoqTranslate.Tarski.Base.anga_const_c
#print axioms GeocoqTranslate.Tarski.Base.is_null_anga_out_c
#print axioms GeocoqTranslate.Tarski.Base.acute_not_bet_c
#print axioms GeocoqTranslate.Tarski.Base.anga_acute_c
#print axioms GeocoqTranslate.Tarski.Base.not_null_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.ang_cong_ang_c
#print axioms GeocoqTranslate.Tarski.Base.is_null_ang_out_c
#print axioms GeocoqTranslate.Tarski.Base.out_null_ang_c
#print axioms GeocoqTranslate.Tarski.Base.bet_flat_ang_c
#print axioms GeocoqTranslate.Tarski.Base.out_null_anga_c
#print axioms GeocoqTranslate.Tarski.Base.anga_not_flat_c
#print axioms GeocoqTranslate.Tarski.Base.anga_const_o_c
#print axioms GeocoqTranslate.Tarski.Base.anga_conga_anga_c
#print axioms GeocoqTranslate.Tarski.Base.anga_out_anga_c
#print axioms GeocoqTranslate.Tarski.Base.out_out_anga_c
#print axioms GeocoqTranslate.Tarski.Base.is_null_all_c
#print axioms GeocoqTranslate.Tarski.Base.anga_col_out_c
#print axioms GeocoqTranslate.Tarski.Base.ang_not_lg_null_c
#print axioms GeocoqTranslate.Tarski.Base.anga_not_lg_null_c
#print axioms GeocoqTranslate.Tarski.Base.anga_col_null_c
#print axioms GeocoqTranslate.Tarski.Base.eqA_preserves_ang_c
#print axioms GeocoqTranslate.Tarski.Base.eqA_preserves_anga_c
end GeocoqTranslate.Tarski.Base