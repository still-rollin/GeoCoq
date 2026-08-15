import GeocoqTranslate.Tarski_dev.Ch15a
import GeocoqTranslate.Tarski_dev.TarskiConA

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

theorem Ps_Col_c :
    ∀ (O E A : Tpoint), Ps O E A → Col O E A :=
  fun b0 b1 b2 b3 =>
  (let H0 := out_col b3; (by colr))
theorem PythRel_exists_c :
    ∀ (O E E' : Tpoint), ¬ Col O E E' → ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), PythRel O E E' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have H2 := not_col_distincts_c b0 b1 b2 b3
  have H3 := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, H7⟩ := H6
  have o := point_equality_decidability b0 b5
  rcases o with x | x
  · rw [x] at *
    exact ⟨b4, (⟨(⟨b3, (⟨b6, (⟨b7, b6⟩)⟩)⟩), (Or.inl (⟨rfl, (Or.inl rfl)⟩))⟩)⟩
  · have e := perp_exists_c b0 b1 b0 (Ne.symm H5)
    obtain ⟨x0, x1⟩ := e
    have e0 := segment_construction_2_c x0 b0 b0 b5 ((let H9 := perp_distinct_c b0 x0 b1 b0 x1; (let H10 := H9; (by
  obtain ⟨H11, _⟩ := H10
  exact Ne.symm H11))))
    obtain ⟨x2, x3⟩ := e0
    obtain ⟨x4, x5⟩ := x3
    have e1 := segment_construction_2_c b1 b0 b4 x2 (Ne.symm H5)
    obtain ⟨x6, x7⟩ := e1
    obtain ⟨x8, x9⟩ := x7
    exact ⟨x6, (⟨(⟨b3, (⟨b6, (⟨b7, (by
  rcases x8 with x10 | x10
  · exact bet_col_c b0 b1 x6 x10
  · have H12 := bet_col_c b0 x6 b1 x10
    exact (by colr))⟩)⟩)⟩), (Or.inr (⟨x2, (⟨((let H11 := perp_col1_c b0 x0 b0 b1 b5 x (perp_comm_c x0 b0 b1 b0 (perp_comm_c b0 x0 b0 b1 (perp_comm_c x0 b0 b1 b0 (perp_left_comm_c b0 x0 b1 b0 x1)))) b7; (let H12 := perp_col1_c b0 b5 b0 x0 x2 ((fun H12 => (by
  rw [H12] at *
  have HB5 : Cong b0 b5 b0 b0 := (by cong_r)
  have HB6 := cong_identity b0 b5 b0 HB5
  rw [HB6] at *
  rcases x4 with _ | _
  · rcases x8 with _ | _
    · have H14 := (let H14 := rfl; x H14)
      exact (H14).elim
    · have H14 := (let H14 := rfl; x H14)
      exact (H14).elim
  · rcases x8 with _ | _
    · have H14 := (let H14 := rfl; x H14)
      exact (H14).elim
    · have H14 := (let H14 := rfl; x H14)
      exact (H14).elim))) (perp_comm_c b5 b0 x0 b0 (perp_comm_c b0 b5 b0 x0 (perp_sym_c b0 x0 b0 b5 H11))) (by
  rcases x4 with x10 | x10
  · have H13 := bet_col_c b0 x0 x2 x10
    exact H13
  · have H13 := bet_col_c b0 x2 x0 x10
    exact (by colr)); perp_comm_c x2 b0 b5 b0 (perp_comm_c b0 x2 b0 b5 (perp_sym_c b0 b5 b0 x2 H12))))), (⟨x5, x9⟩)⟩)⟩))⟩)⟩
theorem opp_same_square_c :
    ∀ (O E E' A B A2 : Tpoint), Opp O E E' A B → Prod O E E' A A A2 → Prod O E E' B B A2 := sorry

theorem PythOK_c :
    ∀ (O E E' A B C A2 B2 C2 : Tpoint), PythRel O E E' A B C → Prod O E E' A A A2 → Prod O E E' B B B2 → Prod O E E' C C C2 → Sum O E E' A2 B2 C2 := sorry

theorem PythRel_uniqueness_c :
    ∀ (O E E' A B C1 C2 : Tpoint), PythRel O E E' A B C1 → PythRel O E E' A B C2 → ((Ps O E C1 ∧ Ps O E C2) ∨ C1 = O) → C1 = C2 := sorry

#print axioms GeocoqTranslate.Tarski.Base.Ps_Col_c
#print axioms GeocoqTranslate.Tarski.Base.PythRel_exists_c
#print axioms GeocoqTranslate.Tarski.Base.opp_same_square_c
#print axioms GeocoqTranslate.Tarski.Base.PythOK_c
#print axioms GeocoqTranslate.Tarski.Base.PythRel_uniqueness_c
end GeocoqTranslate.Tarski.Base