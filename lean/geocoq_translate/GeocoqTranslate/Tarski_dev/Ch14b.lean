import GeocoqTranslate.Tarski_dev.Ch14a

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

variable (O E E' : Tpoint)
variable (grid_ok : ¬ Col O E E')

theorem prod_to_prodp_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prodp O E E' A B C := sorry

theorem project_pj_c :
    ∀ (P P' A B X Y : Tpoint), Proj P P' A B X Y → Pj X Y P P' := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H0⟩ := b6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  rcases H3 with H4 | H4
  · exact Or.inl (par_symmetry_c b0 b1 b4 b5 H4)
  · exact Or.inr H4
theorem prodp_to_prod_c :
    ∀ (O E E' A B C : Tpoint), Prodp O E E' A B C → Prod O E E' A B C := sorry

theorem prod_exists_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Prod O E E' A B C := sorry

theorem prod_uniqueness_c :
    ∀ (A B C1 C2 : Tpoint), Prod O E E' A B C1 → Prod O E E' A B C2 → C1 = C2 := sorry

theorem prod_0_l_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' O A O := sorry

theorem prod_0_r_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' A O O := sorry

theorem prod_1_l_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' E A A := sorry

theorem prod_1_r_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → Prod O E E' A E A := sorry

theorem inv_exists_c :
    ∀ (O E E' A : Tpoint), ¬ Col O E E' → Col O E A → A ≠ O → ∃ (IA : Tpoint), Prod O E E' IA A E := sorry

theorem prod_null_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B O → A = O ∨ B = O := sorry

theorem prod_y_axis_change_c :
    ∀ (O E E' E'' A B C : Tpoint), Prod O E E' A B C → ¬ Col O E E'' → Prod O E E'' A B C := sorry

theorem proj_preserves_prod_c :
    ∀ (O E E' A B C A' B' C' : Tpoint), Prod O E E' A B C → Ar1 O E' A' B' C' → Pj E E' A A' → Pj E E' B B' → Pj E E' C C' → Prod O E' E A' B' C' := sorry

theorem prod_assoc1_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' A BC ABC → Prod O E E' AB C ABC) := sorry

theorem prod_assoc2_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' AB C ABC → Prod O E E' A BC ABC) := sorry

theorem prod_assoc_c :
    ∀ (O E E' A B C AB BC ABC : Tpoint), Prod O E E' A B AB → Prod O E E' B C BC → (Prod O E E' A BC ABC ↔ Prod O E E' AB C ABC) :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨(fun H1 => prod_assoc1_c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1), (fun H1 => prod_assoc2_c b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 H1)⟩
theorem prod_comm_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prod O E E' B A C := sorry

theorem prod_O_l_eq_c :
    ∀ (O E E' B C : Tpoint), Prod O E E' O B C → C = O := sorry

theorem prod_O_r_eq_c :
    ∀ (O E E' A C : Tpoint), Prod O E E' A O C → C = O := sorry

theorem prod_uniquenessA_c :
    ∀ (O E E' A A' B C : Tpoint), B ≠ O → Prod O E E' A B C → Prod O E E' A' B C → A = A' := sorry

theorem prod_uniquenessB_c :
    ∀ (O E E' A B B' C : Tpoint), A ≠ O → Prod O E E' A B C → Prod O E E' A B' C → B = B' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  (let H2 := prod_comm_c b0 b1 b2 b3 b4 b6 b8; (let H3 := prod_comm_c b0 b1 b2 b3 b5 b6 b9; prod_uniquenessA_c b0 b1 b2 b4 b5 b3 b6 b7 H2 H3))
theorem distr_l_c :
    ∀ (O E E' A B C D AB AC AD : Tpoint), Sum O E E' B C D → Prod O E E' A B AB → Prod O E E' A C AC → (Prod O E E' A D AD → Sum O E E' AB AC AD) := sorry

theorem distr_r_c :
    ∀ (O E E' A B C D AC BC DC : Tpoint), Sum O E E' A B D → Prod O E E' A C AC → Prod O E E' B C BC → (Prod O E E' D C DC → Sum O E E' AC BC DC) := sorry

theorem prod_1_l_eq_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B B → A = E ∨ B = O := by
  intro b0 b1 b2 b3 b4 b5
  have HP := b5
  obtain ⟨H0, _⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, _⟩ := H3
  have HH := prod_1_l_c b0 b1 b2 b4 H1 H4
  have o := point_equality_decidability b4 b0
  rcases o with H5 | H5
  · exact Or.inr H5
  · exact Or.inl (prod_uniquenessA_c b0 b1 b2 b3 b1 b4 b4 H5 HP HH)
theorem prod_1_r_eq_c :
    ∀ (O E E' A B : Tpoint), Prod O E E' A B A → B = E ∨ A = O :=
  fun b0 b1 b2 b3 b4 b5 =>
  (let H0 := prod_comm_c b0 b1 b2 b3 b4 b3 b5; prod_1_l_eq_c b0 b1 b2 b4 b3 H0)
theorem change_grid_prod_l_O_c :
    ∀ (O E E' B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E O B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' O A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' O B C → Prod O' E' E A' B' C' := sorry

theorem change_grid_prod1_c :
    ∀ (O E E' B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E E B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' E A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' E B C → Prod O' E' E A' B' C' := sorry

theorem change_grid_prod_c :
    ∀ (O E E' A B C O' A' B' C' : Tpoint), Par_strict O E O' E' → Ar1 O E A B C → Ar1 O' E' A' B' C' → Pj O O' E E' → Pj O O' A A' → Pj O O' B B' → Pj O O' C C' → Prod O E E' A B C → Prod O' E' E A' B' C' := sorry

theorem prod_sym_c :
    ∀ (O E E' A B C : Tpoint), Prod O E E' A B C → Prod O E E' B A C :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  prod_comm_c b0 b1 b2 b3 b4 b5 b6
theorem l14_31_1_c :
    ∀ (O E E' A B C D : Tpoint), Ar2_4 O E E' A B C D → C ≠ O → (∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) → Prod O C E' A B D := sorry

theorem l14_31_2_c :
    ∀ (O E E' A B C D : Tpoint), Ar2_4 O E E' A B C D → C ≠ O → Prod O C E' A B D → (∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) := sorry

theorem prod_x_axis_unit_change_c :
    ∀ (O E E' A B C D U : Tpoint), Ar2_4 O E E' A B C D → Col O E U → U ≠ O → ( ∃ (X : Tpoint), Prod O E E' A B X ∧ Prod O E E' C D X) → ( ∃ (Y : Tpoint), Prod O U E' A B Y ∧ Prod O U E' C D Y) := sorry

theorem opp_prod_c :
    ∀ (O E E' ME X MX : Tpoint), Opp O E E' E ME → Opp O E E' X MX → Prod O E E' X ME MX := sorry

theorem distr_l_diff_c :
    ∀ (O E E' A B C BMC AB AC ABMC : Tpoint), Diff O E E' B C BMC → Prod O E E' A B AB → Prod O E E' A C AC → Prod O E E' A BMC ABMC → Diff O E E' AB AC ABMC := sorry

theorem diff_of_squares_c :
    ∀ (O E E' A B A2 B2 A2MB2 APB AMB F : Tpoint), Prod O E E' A A A2 → Prod O E E' B B B2 → Diff O E E' A2 B2 A2MB2 → Sum O E E' A B APB → Diff O E E' A B AMB → Prod O E E' APB AMB F → A2MB2 = F := sorry

theorem eq_squares_eq_or_opp_c :
    ∀ (O E E' A B A2 : Tpoint), Prod O E E' A A A2 → Prod O E E' B B A2 → A = B ∨ Opp O E E' A B := sorry

theorem diff_2_prod_c :
    ∀ (O E E' A B AMB BMA ME : Tpoint), Opp O E E' E ME → Diff O E E' A B AMB → Diff O E E' B A BMA → Prod O E E' AMB ME BMA :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  opp_prod_c b0 b1 b2 b7 b5 b6 b8 (diff_opp_c b0 b1 b2 b3 b4 b5 b6 b9 b10)
#print axioms GeocoqTranslate.Tarski.Base.prod_to_prodp_c
#print axioms GeocoqTranslate.Tarski.Base.project_pj_c
#print axioms GeocoqTranslate.Tarski.Base.prodp_to_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_0_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_c
#print axioms GeocoqTranslate.Tarski.Base.inv_exists_c
#print axioms GeocoqTranslate.Tarski.Base.prod_null_c
#print axioms GeocoqTranslate.Tarski.Base.prod_y_axis_change_c
#print axioms GeocoqTranslate.Tarski.Base.proj_preserves_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc1_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_assoc_c
#print axioms GeocoqTranslate.Tarski.Base.prod_comm_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_O_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessA_c
#print axioms GeocoqTranslate.Tarski.Base.prod_uniquenessB_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_c
#print axioms GeocoqTranslate.Tarski.Base.distr_r_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_l_eq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_1_r_eq_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_l_O_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod1_c
#print axioms GeocoqTranslate.Tarski.Base.change_grid_prod_c
#print axioms GeocoqTranslate.Tarski.Base.prod_sym_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_1_c
#print axioms GeocoqTranslate.Tarski.Base.l14_31_2_c
#print axioms GeocoqTranslate.Tarski.Base.prod_x_axis_unit_change_c
#print axioms GeocoqTranslate.Tarski.Base.opp_prod_c
#print axioms GeocoqTranslate.Tarski.Base.distr_l_diff_c
#print axioms GeocoqTranslate.Tarski.Base.diff_of_squares_c
#print axioms GeocoqTranslate.Tarski.Base.eq_squares_eq_or_opp_c
#print axioms GeocoqTranslate.Tarski.Base.diff_2_prod_c
end GeocoqTranslate.Tarski.Base