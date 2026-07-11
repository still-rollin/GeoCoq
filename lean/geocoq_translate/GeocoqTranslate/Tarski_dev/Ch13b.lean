import GeocoqTranslate.Tarski_dev.Ch13a

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
    ∀ (l : Tpoint → Tpoint → Prop) (A B : Tpoint), Q_Cong l → l A B → l B A := sorry
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
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong_Null l → l A A := sorry
theorem lg_null_trivial_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong l → l A A → Q_Cong_Null l :=
  fun b0 b1 b2 b3 =>
  ⟨b2, (⟨b1, b3⟩)⟩
theorem lg_null_dec_c :
    ∀ (l : Tpoint → Tpoint → Prop), Q_Cong l → Q_Cong_Null l ∨ ¬ Q_Cong_Null l := sorry
theorem ex_point_lg_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A : Tpoint), Q_Cong l → ∃ (B : Tpoint), l A B := sorry
theorem ex_point_lg_out_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A P : Tpoint), A ≠ P → Q_Cong l → ¬ Q_Cong_Null l → ∃ (B : Tpoint), l A B ∧ Out A B P := sorry
theorem ex_point_lg_bet_c :
    ∀ (l : Tpoint → Tpoint → Prop) (A M : Tpoint), Q_Cong l → ∃ B : Tpoint, l M B ∧ Bet A M B := sorry
theorem ex_points_lg_not_col_c :
    ∀ (l : Tpoint → Tpoint → Prop) (P : Tpoint), Q_Cong l → ¬ Q_Cong_Null l → ∃ (A : Tpoint), ∃ (B : Tpoint), l A B ∧ ¬ Col A B P := sorry

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