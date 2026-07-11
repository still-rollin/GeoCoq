import GeocoqTranslate.Tarski_dev.Ch12

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_euclidean Tpoint]

theorem cop_npars__inter_exists_c :
    ∀ (A1 B1 A2 B2 : Tpoint), Coplanar A1 B1 A2 B2 → ¬ Par_strict A1 B1 A2 B2 → ∃ (X : Tpoint), Col X A1 B1 ∧ Col X A2 B2 := sorry

theorem cop_npar__inter_exists_c :
    ∀ (A1 B1 A2 B2 : Tpoint), Coplanar A1 B1 A2 B2 → ¬ Par A1 B1 A2 B2 → ∃ (X : Tpoint), Col X A1 B1 ∧ Col X A2 B2 :=
  fun b0 b1 b2 b3 b4 b5 =>
  cop_npars__inter_exists_c b0 b1 b2 b3 b4 ((fun H1 => b5 (Or.inl H1)))

theorem cop_npar__inter_c :
    ∀ (A1 B1 A2 B2 : Tpoint), A1 ≠ B1 → A2 ≠ B2 → Coplanar A1 B1 A2 B2 → ¬ Par A1 B1 A2 B2 → ∃ (X : Tpoint), Inter A1 B1 A2 B2 X := sorry

theorem parallel_uniqueness_c :
    ∀ (A1 A2 B1 B2 C1 C2 P : Tpoint), Par A1 A2 B1 B2 → Col P B1 B2 → Par A1 A2 C1 C2 → Col P C1 C2 → Col C1 B1 B2 ∧ Col C2 B1 B2 := sorry

theorem par_trans_c :
    ∀ (A1 A2 B1 B2 C1 C2 : Tpoint), Par A1 A2 B1 B2 → Par B1 B2 C1 C2 → Par A1 A2 C1 C2 := sorry

theorem inter__npar_c :
    ∀ (A1 A2 B1 B2 X : Tpoint), Inter A1 A2 B1 B2 X → ¬ Par A1 A2 B1 B2 := sorry
theorem l12_16_c :
    ∀ (A1 A2 B1 B2 C1 C2 X : Tpoint), Par A1 A2 B1 B2 → Coplanar B1 B2 C1 C2 → Inter A1 A2 C1 C2 X → ∃ (Y : Tpoint), Inter B1 B2 C1 C2 Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have H2 := par_neq1_c b0 b1 b2 b3 b7
  have H3 := par_neq2_c b0 b1 b2 b3 b7
  exact cop_npar__inter_c b2 b3 b4 b5 H3 (by
  obtain ⟨x, x0⟩ := b9
  exact x) b8 ((fun H4 => (let H5 := inter__npar_c b0 b1 b4 b5 b6 b9; H5 (par_trans_c b0 b1 b2 b3 b4 b5 b7 H4))))

theorem par_dec_c :
    ∀ (A B C D : Tpoint), Par A B C D ∨ ¬ Par A B C D := sorry

theorem par_not_par_c :
    ∀ (A B C D P Q : Tpoint), Par A B C D → ¬ Par A B P Q → ¬ Par C D P Q :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  (fun HNPar' => b7 (par_trans_c b0 b1 b2 b3 b4 b5 b6 HNPar'))

theorem cop_par__inter_c :
    ∀ (A B C D P Q : Tpoint), Par A B C D → ¬ Par A B P Q → Coplanar C D P Q → ∃ (Y : Tpoint), Col P Q Y ∧ Col C D Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have e := cop_npar__inter_exists_c b2 b3 b4 b5 b8 ((fun H => b7 (par_trans_c b0 b1 b2 b3 b4 b5 b6 H)))
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨x, (⟨((by colr)), ((by colr))⟩)⟩

theorem l12_19_c :
    ∀ (A B C D : Tpoint), ¬ Col A B C → Par A B C D → Par B C D A → Cong A B C D ∧ Cong B C D A ∧ TS B D A C ∧ TS A C B D := sorry
theorem l12_20_bis_c :
    ∀ (A B C D : Tpoint), Par A B C D → Cong A B C D → TS B D A C → Par B C D A ∧ Cong B C D A ∧ TS A C B D := sorry

theorem l12_20_c :
    ∀ (A B C D : Tpoint), Par A B C D → Cong A B C D → TS A C B D → Par B C D A ∧ Cong B C D A ∧ TS A C B D := by
  intro b0 b1 b2 b3 b4 b5 b6
  have H2 := par_two_sides_two_sides_c b1 b0 b3 b2 (par_comm_c b0 b1 b2 b3 b4) b6
  have HH := l12_20_bis_c b0 b1 b2 b3 b4 b5 H2
  obtain ⟨H3, H4⟩ := HH
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H3, (⟨H5, H6⟩)⟩

theorem l12_21_a_c :
    ∀ (A B C D : Tpoint), TS A C B D → (Par A B C D → CongA B A C D C A) := sorry

theorem l12_21_c :
    ∀ (A B C D : Tpoint), TS A C B D → (CongA B A C D C A ↔ Par A B C D) := sorry
theorem l12_22_a_c :
    ∀ (A B C D P : Tpoint), Out P A C → OS P A B D → Par A B C D → CongA B A P D C P := sorry

theorem l12_22_c :
    ∀ (A B C D P : Tpoint), Out P A C → OS P A B D → (CongA B A P D C P ↔ Par A B C D) :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  ⟨(fun H1 => l12_22_b_c b0 b1 b2 b3 b4 b5 b6 H1), (fun H1 => l12_22_a_c b0 b1 b2 b3 b4 b5 b6 H1)⟩

theorem l12_23_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → ∃ (B' : Tpoint), ∃ (C' : Tpoint), TS A C B B' ∧ TS A B C C' ∧ Bet B' A C' ∧ CongA A B C B A C' ∧ CongA A C B C A B' := sorry
theorem cop2_npar__inter_c :
    ∀ (A B A' B' X Y : Tpoint), Coplanar A B X Y → Coplanar A' B' X Y → ¬ Par A B A' B' → (∃ (P : Tpoint), Col P X Y ∧ (Col P A B ∨ Col P A' B')) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have o := par_dec_c b0 b1 b4 b5
  rcases o with H2 | H2
  · have H3 := (fun H3 => b8 (par_trans_c b0 b1 b4 b5 b2 b3 H2 (par_left_comm_c b5 b4 b2 b3 (par_left_comm_c b4 b5 b2 b3 (par_symmetry_c b2 b3 b4 b5 H3)))))
    have e := cop_npar__inter_exists_c b2 b3 b4 b5 b7 H3
    obtain ⟨x, x0⟩ := e
    obtain ⟨x1, x2⟩ := x0
    exact ⟨x, (⟨x2, (Or.inr x1)⟩)⟩
  · have e := cop_npar__inter_exists_c b0 b1 b4 b5 b6 H2
    obtain ⟨x, x0⟩ := e
    obtain ⟨x1, x2⟩ := x0
    exact ⟨x, (⟨x2, (Or.inl x1)⟩)⟩

theorem not_par_one_not_par_c :
    ∀ (A B A' B' X Y : Tpoint), ¬ Par A B A' B' → ¬ Par A B X Y ∨ ¬ Par A' B' X Y := by
  intro b0 b1 b2 b3 b4 b5 b6
  have o := par_dec_c b0 b1 b4 b5
  rcases o with x | x
  · exact Or.inr ((fun H1 => b6 (par_trans_c b0 b1 b4 b5 b2 b3 x (par_left_comm_c b5 b4 b2 b3 (par_left_comm_c b4 b5 b2 b3 (par_symmetry_c b2 b3 b4 b5 H1))))))
  · exact Or.inl x

theorem col_par_par_col_c :
    ∀ (A B C A' B' C' : Tpoint), Col A B C → Par A B A' B' → Par B C B' C' → Col A' B' C' := sorry
theorem cop_par_perp__perp_c :
    ∀ (A B C D P Q : Tpoint), Par A B C D → Perp A B P Q → Coplanar C D P Q → Perp C D P Q := sorry

theorem cop4_par_perp2__par_c :
    ∀ (A B C D E F G H : Tpoint), Par A B C D → Perp A B E F → Perp C D G H → Coplanar A B E G → Coplanar A B E H → Coplanar A B F G → Coplanar A B F H → Par E F G H := sorry

theorem not_par_strict_inter_exists_c :
    ∀ (A1 B1 A2 B2 : Tpoint), ¬ Par_strict A1 B1 A2 B2 → ∃ (X : Tpoint), Col X A1 B1 ∧ Col X A2 B2 := sorry

theorem not_par_inter_exists_c :
    ∀ (A1 B1 A2 B2 : Tpoint), ¬ Par A1 B1 A2 B2 → ∃ (X : Tpoint), Col X A1 B1 ∧ Col X A2 B2 := sorry

theorem l12_16_2D_c :
    ∀ (A1 A2 B1 B2 C1 C2 X : Tpoint), Par A1 A2 B1 B2 → Inter A1 A2 C1 C2 X → ∃ (Y : Tpoint), Inter B1 B2 C1 C2 Y := sorry

theorem par_inter_c :
    ∀ (A B C D P Q : Tpoint), Par A B C D → ¬ Par A B P Q → ∃ (Y : Tpoint), Col P Q Y ∧ Col C D Y := sorry

theorem not_par_inter_c :
    ∀ (A B A' B' X Y : Tpoint), ¬ Par A B A' B' → (∃ (P : Tpoint), Col P X Y ∧ (Col P A B ∨ Col P A' B')) := sorry
theorem par_perp__perp_c :
    ∀ (A B C D P Q : Tpoint), Par A B C D → Perp A B P Q → Perp C D P Q := sorry

theorem par_perp2__par_c :
    ∀ (A B C D E F G H : Tpoint), Par A B C D → Perp A B E F → Perp C D G H → Par E F G H := sorry

#print axioms GeocoqTranslate.Tarski.Base.cop_npars__inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.cop_npar__inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.cop_npar__inter_c
#print axioms GeocoqTranslate.Tarski.Base.parallel_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.par_trans_c
#print axioms GeocoqTranslate.Tarski.Base.inter__npar_c
#print axioms GeocoqTranslate.Tarski.Base.l12_16_c
#print axioms GeocoqTranslate.Tarski.Base.par_dec_c
#print axioms GeocoqTranslate.Tarski.Base.par_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.cop_par__inter_c
#print axioms GeocoqTranslate.Tarski.Base.l12_19_c
#print axioms GeocoqTranslate.Tarski.Base.l12_20_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l12_20_c
#print axioms GeocoqTranslate.Tarski.Base.l12_21_a_c
#print axioms GeocoqTranslate.Tarski.Base.l12_21_c
#print axioms GeocoqTranslate.Tarski.Base.l12_22_a_c
#print axioms GeocoqTranslate.Tarski.Base.l12_22_c
#print axioms GeocoqTranslate.Tarski.Base.l12_23_c
#print axioms GeocoqTranslate.Tarski.Base.cop2_npar__inter_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_one_not_par_c
#print axioms GeocoqTranslate.Tarski.Base.col_par_par_col_c
#print axioms GeocoqTranslate.Tarski.Base.cop_par_perp__perp_c
#print axioms GeocoqTranslate.Tarski.Base.cop4_par_perp2__par_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_strict_inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_inter_exists_c
#print axioms GeocoqTranslate.Tarski.Base.l12_16_2D_c
#print axioms GeocoqTranslate.Tarski.Base.par_inter_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_inter_c
#print axioms GeocoqTranslate.Tarski.Base.par_perp__perp_c
#print axioms GeocoqTranslate.Tarski.Base.par_perp2__par_c
end GeocoqTranslate.Tarski.Base