import GeocoqTranslate.Tarski_dev.Ch13a
import GeocoqTranslate.Tarski_dev.TarskiConA

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem lg_exists_c :
    ∀ (A B : Tpoint), ∃ (l : Tpoint → Tpoint → Prop), Q_Cong l ∧ l A B :=
  fun b0 b1 =>
  ⟨(fun x y => Cong b0 b1 x y), (⟨(⟨b0, (⟨b1, (fun X Y => ⟨(fun H => H), (fun H => H)⟩)⟩)⟩), (cong_reflexivity b0 b1)⟩)⟩
theorem lg_cong_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A B C D : Tpoint), Q_Cong l → l A B → l C D → Cong A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨X, H2⟩ := b5
  obtain ⟨Y, H3⟩ := H2
  have HH := H3 b1 b2
  obtain ⟨x, x0⟩ := HH
  have HH0 := H3 b3 b4
  obtain ⟨x1, x2⟩ := HH0
  have H6 := x0 b6
  have H7 := x2 b7
  exact cong_transitivity (cong_symmetry H6) H7
theorem lg_cong_lg_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A B C D : Tpoint), Q_Cong l → l A B → Cong A B C D → l C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨A0, H2⟩ := b5
  obtain ⟨B0, H3⟩ := H2
  have HP := H3 b1 b2
  have HQ := H3 b3 b4
  obtain ⟨x, x0⟩ := HP
  obtain ⟨x1, x2⟩ := HQ
  exact x1 (cong_transitivity (x0 b6) b7)
theorem lg_sym_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A B : Tpoint), Q_Cong l → l A B → l B A :=
  fun b0 b1 b2 b3 b4 =>
  lg_cong_lg_c b0 b1 b2 b2 b1 b3 b4 ((by cong_r))
theorem ex_points_lg_c :
    ∀ (l : Tpoint → Tpoint → Prop), Q_Cong l → ∃ (A : Tpoint), ∃ (B : Tpoint), l A B := by
  intro b0 b1
  obtain ⟨A, H0⟩ := b1
  obtain ⟨B, H1⟩ := H0
  have HH := H1 A B
  obtain ⟨x, x0⟩ := HH
  exact ⟨A, (⟨B, (x (x0 (x (cong_reflexivity A B))))⟩)⟩
theorem is_len_cong_c :
    ∀ (A B C D : Tpoint) (l : Tpoint → Tpoint → Prop), Len A B l → Len C D l → Cong A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H1, H2⟩ := b6
  obtain ⟨_, H3⟩ := b5
  exact lg_cong_c b4 b0 b1 b2 b3 H1 H3 H2
theorem is_len_cong_is_len_c :
    ∀ (A B C D : Tpoint) (l : Tpoint → Tpoint → Prop), Len A B l → Cong A B C D → Len C D l := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H1, H2⟩ := b5
  exact ⟨H1, ((by
  obtain ⟨a, H3⟩ := H1
  obtain ⟨b, H4⟩ := H3
  have HH := H4 b0 b1
  obtain ⟨x, x0⟩ := HH
  have HH1 := H4 b2 b3
  obtain ⟨x1, x2⟩ := HH1
  have H7 := x0 H2
  exact x1 ((by cong_r))))⟩
theorem not_cong_is_len_c :
    ∀ (A B C D : Tpoint) (l : Tpoint → Tpoint → Prop), ¬ (Cong A B C D) → Len A B l → ¬ (l C D) := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H1, H2⟩ := b6
  intro H3
  exact b5 (lg_cong_c b4 b0 b1 b2 b3 H1 H2 H3)
theorem not_cong_is_len1_c :
    ∀ (A B C D : Tpoint) (l : Tpoint → Tpoint → Prop), ¬ Cong A B C D → Len A B l → ¬ Len C D l := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro H1
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := b6
  exact b5 (lg_cong_c b4 b0 b1 b2 b3 H2 H4 H3)
theorem lg_null_instance_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong_Null l → l A A := by
  intro b0 b1 b2
  obtain ⟨H0, H1⟩ := b2
  obtain ⟨X, H2⟩ := H0
  obtain ⟨Y, H3⟩ := H2
  have HH := H3 b1 b1
  obtain ⟨x, x0⟩ := HH
  obtain ⟨P, H6⟩ := H1
  have HH0 := H3 P P
  obtain ⟨x1, x2⟩ := HH0
  have H9 := x2 H6
  exact x ((let H10 : Cong P P X Y := (by cong_r); (let H11 := cong_reverse_identity H10; (by
  rw [H11] at *
  exact cong_trivial_identity X b1))))
theorem lg_null_trivial_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong l → l A A → Q_Cong_Null l :=
  fun b0 b1 b2 b3 =>
  ⟨b2, (⟨b1, b3⟩)⟩
theorem lg_null_dec_c :
    ∀ (l : Tpoint → Tpoint → Prop), Q_Cong l → Q_Cong_Null l ∨ ¬ Q_Cong_Null l := by
  intro b0 b1
  TfinishA
theorem ex_point_lg_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong l → ∃ (B : Tpoint), l A B := by
  intro b0 b1 b2
  have o := lg_null_dec_c b0 b2
  rcases o with H0 | H0
  · exact ⟨b1, (lg_null_instance_c b0 b1 H0)⟩
  · have HH := b2
    obtain ⟨X, H1⟩ := HH
    obtain ⟨Y, H2⟩ := H1
    have HH0 := another_point_c b1
    obtain ⟨P, H3⟩ := HH0
    have HP := H2 X Y
    obtain ⟨x, x0⟩ := HP
    have H6 := x ((by cong_r))
    have H7 := (fun H7 => (by
  rw [H7] at *
  exact H0 (⟨b2, (⟨X, H6⟩)⟩)))
    have HH1 := segment_construction_3_c b1 P X Y H3 H7
    obtain ⟨B, H8⟩ := HH1
    obtain ⟨_, H9⟩ := H8
    exact ⟨B, ((let HH2 := H2 b1 B; (by
  obtain ⟨x1, x2⟩ := HH2
  exact x1 (x2 (x1 ((by cong_r)))))))⟩
theorem ex_point_lg_out_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A P : Tpoint), A ≠ P → Q_Cong l → ¬ Q_Cong_Null l → ∃ (B : Tpoint), l A B ∧ Out A B P := by
  intro b0 b1 b2 b3 b4 b5
  have HH := b4
  obtain ⟨X, H2⟩ := HH
  obtain ⟨Y, H3⟩ := H2
  have HP := H3 X Y
  obtain ⟨x, x0⟩ := HP
  have H6 := x ((by cong_r))
  have H7 := (fun H7 => (by
  rw [H7] at *
  exact b5 (⟨b4, (⟨X, H6⟩)⟩)))
  have HH0 := segment_construction_3_c b1 b2 X Y b3 H7
  obtain ⟨B, H8⟩ := HH0
  obtain ⟨H9, H10⟩ := H8
  exact ⟨B, (⟨((let HH1 := H3 b1 B; (by
  obtain ⟨x1, x2⟩ := HH1
  exact x1 (x2 (x1 ((by cong_r))))))), (l6_6 H9)⟩)⟩
theorem ex_point_lg_bet_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A M : Tpoint), Q_Cong l → ∃ B : Tpoint, l M B ∧ Bet A M B := by
  intro b0 b1 b2 b3
  have HH := b3
  obtain ⟨X, H0⟩ := HH
  obtain ⟨Y, H1⟩ := H0
  have HP := H1 X Y
  obtain ⟨x, x0⟩ := HP
  have H3 := x ((by cong_r))
  have sg := segment_construction b1 b2 X Y
  obtain ⟨B, H4⟩ := sg
  obtain ⟨H5, H6⟩ := H4
  exact ⟨B, (⟨(lg_cong_lg_c b0 X Y b2 B b3 H3 ((by cong_r))), H5⟩)⟩
theorem ex_points_lg_not_col_c :
    ∀ (l : Tpoint → Tpoint → Prop) (P : Tpoint), Q_Cong l → ¬ Q_Cong_Null l → ∃ (A : Tpoint), ∃ (B : Tpoint), l A B ∧ ¬ Col A B P := by
  intro b0 b1 b2 b3
  have HH := another_point_c b1
  obtain ⟨A, H1⟩ := HH
  have HH0 := not_col_exists_c b1 A H1
  obtain ⟨Q, H2⟩ := HH0
  exact ⟨A, ((let H3 := (fun H3 => (by
  rw [H3] at *
  exact H2 (col_trivial_2_c b1 A))); (let tempo_sg := ex_point_lg_out_c b0; (let tempo_HQ := b3; (let tempo_HQ0 := tempo_sg A Q H3 b2 tempo_HQ; (by
  obtain ⟨B, H4⟩ := tempo_HQ0
  obtain ⟨H5, H6⟩ := H4
  exact ⟨B, (⟨H5, ((fun H7 => H2 ((let H8 := (fun H8 => (by
  rw [H8] at *
  obtain ⟨H10, H11⟩ := H6
  obtain ⟨_, H12⟩ := H11
  rcases H12 with _ | _
  · have H13 := (let H13 := rfl; H10 H13)
    exact (H13).elim
  · have H13 := (let H13 := rfl; H10 H13)
    exact (H13).elim)); (let H9 := out_col H6; (let H10 := not_col_distincts_c b1 A Q H2; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, H14⟩ := H13
  have H15 := tarski_to_col_theory.Tarski_is_a_Col_theory
  exact ((let H16 := (((B , BinNums.xO (BinNums.xO BinNums.xH)))) % list; (let H17 := interp H16 B; fun H18 H19 H20 H21 => (let H22 := (by colr); fun H23 H24 => (let H25 := (by colr); (by colr)))))) H1 H3 H8 H14 H9 H7))))))))⟩)⟩))))))⟩
theorem ex_eql_c :
    ∀ (l1 l2 : Tpoint → Tpoint → Prop), (∃ A , ∃ (B : Tpoint), Len A B l1 ∧ Len A B l2) → EqL l1 l2 := by
  intro b0 b1 b2
  obtain ⟨A, H0⟩ := b2
  obtain ⟨B, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  have HH := H2
  have HH0 := H3
  obtain ⟨H4, _⟩ := HH0
  obtain ⟨H5, _⟩ := HH
  intro A0 B0
  exact ⟨(fun H6 => (let H7 := ⟨H5, H6⟩; (let H8 := is_len_cong_c A B A0 B0 b0 H2 H7; (let H9 := is_len_cong_is_len_c A B A0 B0 b1 H3 H8; (by
  obtain ⟨_, H10⟩ := H9
  exact H10))))), (fun H6 => (let H7 := ⟨H4, H6⟩; (let H8 := is_len_cong_c A B A0 B0 b1 H3 H7; (let H9 := is_len_cong_is_len_c A B A0 B0 b0 H2 H8; (by
  obtain ⟨_, H10⟩ := H9
  exact H10)))))⟩
theorem all_eql_c :
    ∀ (A B : Tpoint) (l1 l2 : Tpoint → Tpoint → Prop), Len A B l1 → Len A B l2 → EqL l1 l2 :=
  fun b0 b1 b2 b3 b4 b5 =>
  ex_eql_c b2 b3 (⟨b0, (⟨b1, (⟨b4, b5⟩)⟩)⟩)
theorem null_len_c :
    ∀ (A B : Tpoint) (la lb : Tpoint → Tpoint → Prop), Len A A la → Len B B lb → EqL la lb :=
  fun b0 b1 b2 b3 b4 b5 =>
  all_eql_c b0 b0 b2 b3 b4 (is_len_cong_is_len_c b1 b1 b0 b0 b3 b5 (cong_trivial_identity b1 b0))
theorem ex_lg_c :
    ∀ (A B : Tpoint), ∃ (l : Tpoint → Tpoint → Prop), Q_Cong l ∧ l A B := sorry

theorem lg_eql_lg_c :
    ∀ (l1 l2 : Tpoint → Tpoint → Prop), Q_Cong l1 → EqL l1 l2 → Q_Cong l2 := sorry

theorem ex_eqL_c :
    ∀ (l1 l2 : Tpoint → Tpoint → Prop), Q_Cong l1 → Q_Cong l2 → (∃ (A : Tpoint), ∃ (B : Tpoint), l1 A B ∧ l2 A B) → EqL l1 l2 := sorry

#print axioms GeocoqTranslate.Tarski.Base.lg_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lg_cong_c
#print axioms GeocoqTranslate.Tarski.Base.lg_cong_lg_c
#print axioms GeocoqTranslate.Tarski.Base.lg_sym_c
#print axioms GeocoqTranslate.Tarski.Base.ex_points_lg_c
#print axioms GeocoqTranslate.Tarski.Base.is_len_cong_c
#print axioms GeocoqTranslate.Tarski.Base.is_len_cong_is_len_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_is_len_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_is_len1_c
#print axioms GeocoqTranslate.Tarski.Base.lg_null_instance_c
#print axioms GeocoqTranslate.Tarski.Base.lg_null_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.lg_null_dec_c
#print axioms GeocoqTranslate.Tarski.Base.ex_point_lg_c
#print axioms GeocoqTranslate.Tarski.Base.ex_point_lg_out_c
#print axioms GeocoqTranslate.Tarski.Base.ex_point_lg_bet_c
#print axioms GeocoqTranslate.Tarski.Base.ex_points_lg_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.ex_eql_c
#print axioms GeocoqTranslate.Tarski.Base.all_eql_c
#print axioms GeocoqTranslate.Tarski.Base.null_len_c
#print axioms GeocoqTranslate.Tarski.Base.ex_lg_c
#print axioms GeocoqTranslate.Tarski.Base.lg_eql_lg_c
#print axioms GeocoqTranslate.Tarski.Base.ex_eqL_c
end GeocoqTranslate.Tarski.Base