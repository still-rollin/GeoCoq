import GeocoqTranslate.Tarski_dev.Ch16a

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

def O : Tpoint := PA
def E : Tpoint := PB
def E' : Tpoint := PC
variable (SS U1 U2 : Tpoint)
variable (orthonormal_grid : Cs O E SS U1 U2)

theorem sum_col_c :
    ∀ (A B C : Tpoint), Sum O E E' A B C → Col O E C := by
  intro b0 b1 b2 b3
  obtain ⟨H0, _⟩ := b3
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  exact H3
theorem sum_f_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Sum O E E' A B C := sorry

theorem prod_f_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Prod O E E' A B C := sorry

theorem diff_col_c :
    ∀ (A B C : Tpoint), Diff O E E' A B C → Col O E C := by
  intro b0 b1 b2 b3
  obtain ⟨x, x0⟩ := b3
  obtain ⟨_, H0⟩ := x0
  exact sum_col_c b0 x b2 H0
theorem diff_f_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), Diff O E E' A B C := sorry

theorem opp_col_c :
    ∀ (A B : Tpoint), Opp O E E' A B → Col O E B := by
  intro b0 b1 b2
  obtain ⟨H0, _⟩ := b2
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact H2
theorem opp_f_c :
    ∀ (A : Tpoint), Col O E A → ∃ (B : Tpoint), Opp O E E' A B := sorry

theorem opp_pythrel_c :
    ∀ (O E E' A B C C' : Tpoint), Opp O E E' C C' → PythRel O E E' A B C → PythRel O E E' A B C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H1, H2⟩ := b8
  exact ⟨((by
  obtain ⟨H3, H4⟩ := H1
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, _⟩ := H6
  exact ⟨H3, (⟨H5, (⟨H7, ((by
  obtain ⟨H8, _⟩ := b7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, _⟩ := H11
  rcases H2 with H12 | _
  · obtain ⟨_, H13⟩ := H12
    rcases H13 with _ | _
    · exact H10
    · exact H10
  · exact H10))⟩)⟩)⟩)), ((by
  obtain ⟨H3, H4⟩ := H1
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, _⟩ := H6
  rcases H2 with H8 | H8
  · exact Or.inl ((by
  obtain ⟨H9, H10⟩ := H8
  rcases H10 with H11 | H11
  · subst H11
    exact ⟨H9, (Or.inr b7)⟩
  · exact ⟨H9, ((by
  subst H9
  exact Or.inl (sum_uniquenessA_c b5 b3 b6 b0 (sum_comm_c b5 b3 b0 H11) b7)))⟩))
  · obtain ⟨B', H9⟩ := H8
    obtain ⟨H10, H11⟩ := H9
    obtain ⟨H12, H13⟩ := H11
    exact Or.inr (⟨B', (⟨H10, (⟨H12, ((let H14 := opp_midpoint_c b0 b1 b2 b5 b6 b7; (by
  obtain ⟨_, H15⟩ := H14
  exact (by cong_r))))⟩)⟩)⟩)))⟩
theorem pythrel_null_c :
    ∀ (O E E' A B : Tpoint), PythRel O E E' A B O → A = O ∧ B = O := sorry

theorem pythrel_not_null_c :
    ∀ (O E E' A B C : Tpoint), C ≠ O → PythRel O E E' A B C → A ≠ O ∨ B ≠ O := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨_, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  rcases H2 with H8 | H8
  · obtain ⟨H9, H10⟩ := H8
    exact Or.inl ((fun H11 => (by
  subst H11
  rcases H10 with H13 | H13
  · subst H13
    have H15 := (let H15 := rfl; b6 H15)
    exact (H15).elim
  · subst H9
    have H14 := opp_midpoint_c b0 b1 b2 b0 b5 H13
    obtain ⟨H15, H16⟩ := H14
    have H17 := (by cong_r)
    have H18 := cong_identity b0 b5 b0 H17
    subst H18
    have H20 := (let H20 := rfl; b6 H20)
    exact (H20).elim)))
  · obtain ⟨B', H9⟩ := H8
    obtain ⟨H10, H11⟩ := H9
    obtain ⟨H12, _⟩ := H11
    exact Or.inr ((fun H13 => (by
  subst H13
  have H15 := perp_distinct_c b0 B' b0 b0 H10
  obtain ⟨_, H16⟩ := H15
  have H17 := (let H17 := rfl; H16 H17)
  exact (H17).elim)))
theorem pythrelOO_c :
    ∀ (O E E' C : Tpoint), PythRel O E E' O O C → C = O := by
  intro b0 b1 b2 b3 b4
  obtain ⟨_, H0⟩ := b4
  rcases H0 with H1 | H1
  · obtain ⟨_, H2⟩ := H1
    rcases H2 with H3 | H3
    · exact Eq.symm H3
    · have H4 := opp_midpoint_c b0 b1 b2 b0 b3 H3
      obtain ⟨_, H5⟩ := H4
      have H6 := (by cong_r)
      have H7 := cong_identity b0 b3 b0 H6
      exact Eq.symm H7
  · obtain ⟨B', H2⟩ := H1
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨_, _⟩ := H4
    have H5 := perp_distinct_c b0 B' b0 b0 H3
    obtain ⟨_, H6⟩ := H5
    have H7 := (let H7 := rfl; H6 H7)
    exact (H7).elim
theorem Pyth_f_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), PythRel O E E' A B C ∧ (Ps O E C ∨ C = O) := sorry

theorem inv_exists_with_notation_c :
    ∀ (A : Tpoint), Col O E A → ∃ (B : Tpoint), inv O E E' A B := by
  intro b0 b1
  have o := point_equality_decidability b0 O
  rcases o with H0 | H0
  · subst H0
    exact ⟨O, (Or.inr (⟨rfl, rfl⟩))⟩
  · have e := inv_exists_c O E E' b0 ncolOEE' b1 H0
    obtain ⟨x, x0⟩ := e
    exact ⟨x, (Or.inl (⟨H0, x0⟩))⟩
theorem inv_col_c :
    ∀ (A B : Tpoint), inv O E E' A B → Col O E B := by
  intro b0 b1 b2
  rcases (point_equality_decidability b0 O) with HNEq | HNEq
  · rcases b2 with H0 | H0
    · obtain ⟨H1, H2⟩ := H0
      subst HNEq
      have H4 := (let H4 := rfl; H1 H4)
      exact (H4).elim
    · obtain ⟨H1, H2⟩ := H0
      subst H1
      subst H2
      exact (by colr)
  · rcases b2 with H0 | H0
    · obtain ⟨x, x0⟩ := H0
      obtain ⟨x1, x2⟩ := x0
      obtain ⟨_, H2⟩ := x1
      obtain ⟨H3, H4⟩ := H2
      obtain ⟨_, _⟩ := H4
      exact H3
    · obtain ⟨H1, H2⟩ := H0
      subst H1
      subst H2
      have H3 := (let H3 := rfl; HNEq H3)
      exact (H3).elim
theorem inv_uniqueness_c :
    ∀ (A B1 B2 : Tpoint), inv O E E' A B1 → inv O E E' A B2 → B1 = B2 := by
  intro b0 b1 b2 b3 b4
  rcases (point_equality_decidability b0 O) with HNEq | HNEq
  · rcases b3 with H | H
    · rcases b4 with H0 | H0
      · obtain ⟨H1, _⟩ := H0
        obtain ⟨H2, _⟩ := H
        have H3 := H2 HNEq
        have H4 := H1 HNEq
        exact (H3).elim
      · obtain ⟨H1, _⟩ := H0
        obtain ⟨H2, _⟩ := H
        have H3 := H2 H1
        exact (H3).elim
    · rcases b4 with H0 | H0
      · obtain ⟨H1, _⟩ := H0
        obtain ⟨H2, _⟩ := H
        have H3 := H1 H2
        exact (H3).elim
      · obtain ⟨H1, H2⟩ := H0
        obtain ⟨H3, H4⟩ := H
        subst H3
        subst H4
        subst H2
        exact HNEq
  · rcases b3 with HB3 | HB3
    · rcases b4 with HB4 | HB4
      · obtain ⟨x, x0⟩ := HB3
        obtain ⟨x1, x2⟩ := HB4
        exact prod_uniquenessA_c O E E' b1 b2 b0 E x x0 x2
      · obtain ⟨H, H0⟩ := HB4
        obtain ⟨H1, H2⟩ := HB3
        subst H
        subst H0
        have H4 := (let H4 := rfl; H1 H4)
        exact (H4).elim
    · obtain ⟨H, H0⟩ := HB3
      subst H
      subst H0
      have H1 := (let H1 := rfl; HNEq H1)
      exact (H1).elim
theorem inv_f_c :
    ∀ (A : Tpoint), Col O E A → ∃ (B : Tpoint), inv O E E' A B := sorry

theorem div_exists_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), div O E E' A B C := by
  intro b0 b1 b2 b3
  have e := inv_exists_with_notation_c b1 b3
  obtain ⟨x, x0⟩ := e
  have e0 := prod_exists_c b0 x b2 (inv_col_c b1 x x0)
  obtain ⟨x1, x2⟩ := e0
  exact ⟨x1, (⟨x, (⟨x0, x2⟩)⟩)⟩
theorem div_uniqueness_c :
    ∀ (A B C1 C2 : Tpoint), div O E E' A B C1 → div O E E' A B C2 → C1 = C2 := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := b5
  obtain ⟨x5, x6⟩ := x4
  have HIB'0 := inv_uniqueness_c b1 x x3 x1 x5
  subst HIB'0
  exact prod_uniqueness_c b0 x b2 b3 x2 x6
theorem div_col_c :
    ∀ (A B C : Tpoint), div O E E' A B C → Col O E C := by
  intro b0 b1 b2 b3
  obtain ⟨x, x0⟩ := b3
  obtain ⟨x1, x2⟩ := x0
  exact prod_col_c b0 x b2 x2
theorem div_f_c :
    ∀ (A B : Tpoint), Col O E A → Col O E B → ∃ (C : Tpoint), div O E E' A B C := sorry

theorem eq_dec_F_c :
    ∀ (A B : @F Tpoint _), EqF A B ∨ ¬ EqF A B := sorry

theorem neg_and_eqF_c :
    ∀ (A B C D : @F Tpoint _), ¬ (EqF A B ∧ EqF C D) ↔ ¬ EqF A B ∨ ¬ EqF C D := by
  intro b0 b1 b2 b3
  exact ⟨(fun H => (let o := eq_dec_F_c b0 b1; (by
  rcases o with H0 | H0
  · have o0 := eq_dec_F_c b2 b3
    rcases o0 with H1 | H1
    · have H2 := fun H2 H3 => H (⟨H2, H3⟩)
      have H3 := H2 H0
      have H4 := H3 H1
      exact (H4).elim
    · have H2 := fun H2 H3 => H (⟨H2, H3⟩)
      have H3 := H2 H0
      exact Or.inr ((fun H4 => (let H5 := H1 H4; (let H6 := H3 H4; (H5).elim))))
  · have o0 := eq_dec_F_c b2 b3
    rcases o0 with H1 | _
    · have H2 := fun H2 H3 => H (⟨H2, H3⟩)
      exact Or.inl ((fun H3 => (let H4 := H0 H3; (let H5 := H2 H3; (let H6 := H5 H1; (H4).elim)))))
    · have H2 := fun H2 H3 => H (⟨H2, H3⟩)
      exact Or.inl ((fun H1 => (let H3 := H0 H1; (let H4 := H2 H1; (H3).elim))))))), (fun H => (let o := eq_dec_F_c b0 b1; (by
  rcases o with H0 | H0
  · have o0 := eq_dec_F_c b2 b3
    rcases o0 with H1 | H1
    · intro H2
      obtain ⟨_, _⟩ := H2
      rcases H with H3 | H3
      · have H4 := H3 H0
        exact (H4).elim
      · have H4 := H3 H1
        exact (H4).elim
    · intro H2
      obtain ⟨_, H4⟩ := H2
      rcases H with H3 | H3
      · have H5 := H3 H0
        have H6 := H1 H4
        exact (H5).elim
      · have H5 := H1 H4
        have H6 := H3 H4
        exact (H5).elim
  · have o0 := eq_dec_F_c b2 b3
    rcases o0 with H1 | H1
    · intro H2
      obtain ⟨H3, _⟩ := H2
      rcases H with H4 | H4
      · have H5 := H0 H3
        have H6 := H4 H3
        exact (H5).elim
      · have H5 := H4 H1
        have H6 := H0 H3
        exact (H5).elim
    · intro H2
      obtain ⟨H3, H4⟩ := H2
      rcases H with H5 | H5
      · have H6 := H0 H3
        have H7 := H5 H3
        have H8 := H1 H4
        exact (H6).elim
      · have H6 := H0 H3
        have H7 := H1 H4
        have H8 := H5 H4
        exact (H6).elim)))⟩
theorem neq20_c :
    ∀ (_tp : Tpoint), ¬ EqF (AddF OneF OneF) OF := sorry

theorem ringF_c :
    ∀ (_tp : Tpoint), (ring_theory OF OneF AddF MulF SubF OppF EqF) := sorry

theorem fieldF_c :
    ∀ (_tp : Tpoint), field_theory OF OneF AddF MulF SubF OppF DivF InvF EqF := sorry

theorem Fmult_integral_c :
    ∀ (A B : @F Tpoint _), A * B = 0 → A = 0 ∨ B = 0 := sorry

theorem PythFOk_c :
    ∀ (A B : @F Tpoint _), (PythF A B) * (PythF A B) = A * A + B * B := sorry

theorem subF__eq0_c :
    ∀ (x y : @F Tpoint _), x - y = 0 ↔ x = y :=
  fun b0 b1 =>
  ⟨(fun H => psos_r1b b0 b1 ((((let B := _ - _ (b0 - b1) 0; (let B0 := zero; (let B1 := _ - _ b0 b1; (let B2 := zero; fun H0 => (let p21 := PEsub (PEX Z 1) (PEX Z 2); (let lp21 := PEsub (PEsub (PEX Z 1) (PEX Z 2)) (PEc 0 % Z); (let lci := nil; (let lq := PEc 1 % Z; (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b0) lp21 q (lci , lq) Hg) (⟨H0, I⟩); Rintegral_domain_pow (interpret3 (PEc 1 % Z) (b0)) (interpret3 (PEsub (PEX Z (Pos.of_succ_nat 0)) (PEX Z (Pos.of_succ_nat 1))) (b0)) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))) (psos_r1 (b0 - b1) 0 H))), (fun H => psos_r1b (b0 - b1) 0 ((((let B := _ - _ b0 b1; (let B0 := zero; (let B1 := _ - _ (b0 - b1) 0; (let B2 := zero; fun H0 => (let p21 := PEsub (PEsub (PEX Z 1) (PEX Z 2)) (PEc 0 % Z); (let lp21 := PEsub (PEX Z 1) (PEX Z 2); (let lci := nil; (let lq := PEc 1 % Z; (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b0) lp21 q (lci , lq) Hg) (⟨H0, I⟩); Rintegral_domain_pow (interpret3 (PEc 1 % Z) (b0)) (interpret3 (PEsub (PEsub (PEX Z (Pos.of_succ_nat 0)) (PEX Z (Pos.of_succ_nat 1))) (PEc 0 % Z)) (b0)) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))) (psos_r1 b0 b1 H)))⟩
theorem mulF__eq0_c :
    ∀ (x y z t : @F Tpoint _), (x - y) * (z - t) = 0 ↔ x = y ∨ z = t := by
  intro b0 b1 b2 b3
  exact ⟨(fun H => (let H0 := symmetry (subF__eq0_c b0 b1); subrelation_proper Morphisms_Prop.or_iff_morphism tt (subrelation_respectful (subrelation_refl iff) (subrelation_respectful (subrelation_refl iff) iff_flip_impl_subrelation)) (b0 = F = b1) (b0 - b1 = F = 0) H0 (b2 = F = b3) (b2 = F = b3) (reflexive_proper_proxy (reflexive_reflexive_proxy iff_Reflexive) (b2 = F = b3)) ((let H1 := symmetry (subF__eq0_c b2 b3); Reflexive_partial_app_morphism (subrelation_proper Morphisms_Prop.or_iff_morphism tt (subrelation_respectful (subrelation_refl iff) (subrelation_respectful (subrelation_refl iff) iff_flip_impl_subrelation))) (reflexive_proper_proxy (reflexive_reflexive_proxy iff_Reflexive) (b0 - b1 = F = 0)) (b2 = F = b3) (b2 - b3 = F = 0) H1 (Fmult_integral_c (b0 - b1) (b2 - b3) H))))), (fun H => (by
  rcases H with x0 | x0
  · exact psos_r1b (((b0 - b1)) * (b2 - b3)) 0 ((((let B := _ - _ b0 b1; (let B0 := zero; (let B1 := _ - _ (((b0 - b1)) * (b2 - b3)) 0; (let B2 := zero; fun H1 => (let p21 := PEsub (PEmul (PEsub (PEX Z 1) (PEX Z 2)) (PEsub (PEX Z 3) (PEX Z 4))) (PEc 0 % Z); (let lp21 := PEsub (PEX Z 1) (PEX Z 2); (let lci := nil; (let lq := PEadd (PEmul (PEX Z 4) (PEc (- 1) % Z)) (PEX Z 3); (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b0) lp21 q (lci , lq) Hg) (⟨H1, I⟩); Rintegral_domain_pow (interpret3 (PEc 1 % Z) (b0)) (interpret3 (PEsub (PEmul (PEsub (PEX Z (Pos.of_succ_nat 0)) (PEX Z (Pos.of_succ_nat 1))) (PEsub (PEX Z (Pos.of_succ_nat 2)) (PEX Z (Pos.of_succ_nat 3)))) (PEc 0 % Z)) (b0)) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))) (psos_r1 b0 b1 x0))
  · exact psos_r1b (((b0 - b1)) * (b2 - b3)) 0 ((((let B := _ - _ b2 b3; (let B0 := zero; (let B1 := _ - _ (((b0 - b1)) * (b2 - b3)) 0; (let B2 := zero; fun H1 => (let p21 := PEsub (PEmul (PEsub (PEX Z 3) (PEX Z 4)) (PEsub (PEX Z 1) (PEX Z 2))) (PEc 0 % Z); (let lp21 := PEsub (PEX Z 1) (PEX Z 2); (let lci := nil; (let lq := PEadd (PEmul (PEX Z 4) (PEc (- 1) % Z)) (PEX Z 3); (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b2) lp21 q (lci , lq) Hg) (⟨H1, I⟩); Rintegral_domain_pow (interpret3 (PEc 1 % Z) (b2)) (interpret3 (PEsub (PEmul (PEsub (PEX Z (Pos.of_succ_nat 2)) (PEX Z (Pos.of_succ_nat 3))) (PEsub (PEX Z (Pos.of_succ_nat 0)) (PEX Z (Pos.of_succ_nat 1)))) (PEc 0 % Z)) (b2)) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))) (psos_r1 b2 b3 x0))))⟩
theorem neqO_mul_neqO_c :
    ∀ (x y : @F Tpoint _), ¬ x = 0 → ¬ y = 0 → ¬ x * y = 0 := by
  intro b0 b1 b2 b3
  intro Hxy
  have Hxy0 := Fmult_integral_c b0 b1 Hxy
  rcases Hxy0 with H | H
  · have H0 := b2 H
    exact (H0).elim
  · have H0 := b3 H
    exact (H0).elim
theorem oppF_neq0_c :
    ∀ (f : @F Tpoint _), ¬ f = 0 ↔ ¬ - f = 0 :=
  fun b0 =>
  ⟨(fun HF => (fun H => HF (psos_r1b b0 0 ((((let B := _ - _ (- b0) 0; (let B0 := zero; (let B1 := _ - _ b0 0; (let B2 := zero; fun H0 => (let p21 := PEsub (PEX Z 1) (PEc 0 % Z); (let lp21 := PEsub (PEopp (PEX Z 1)) (PEc 0 % Z); (let lci := nil; (let lq := PEc 1 % Z; (let q := PEmul (PEc (- 1) % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b0) lp21 q (lci , lq) Hg) (⟨H0, I⟩); Rintegral_domain_pow (interpret3 (PEc (- 1) % Z) (b0)) (interpret3 (PEsub (PEX Z (Pos.of_succ_nat 0)) (PEc 0 % Z)) (b0)) (N.to_nat 1) integral_domain_minus_one_zero Hg0))))))))))))) (psos_r1 (- b0) 0 H))))), (fun HF => (fun H => HF (psos_r1b (- b0) 0 ((((let B := _ - _ b0 0; (let B0 := zero; (let B1 := _ - _ (- b0) 0; (let B2 := zero; fun H0 => (let p21 := PEsub (PEopp (PEX Z 1)) (PEc 0 % Z); (let lp21 := PEsub (PEX Z 1) (PEc 0 % Z); (let lci := nil; (let lq := PEc (- 1) % Z; (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct (b0) lp21 q (lci , lq) Hg) (⟨H0, I⟩); Rintegral_domain_pow (interpret3 (PEc 1 % Z) (b0)) (interpret3 (PEsub (PEopp (PEX Z (Pos.of_succ_nat 0))) (PEc 0 % Z)) (b0)) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))) (psos_r1 b0 0 H)))))⟩
theorem Ps_One_c :
    ∀ (_tp : Tpoint), Ps O E E := by
  have T := ncolOEE'
  have H := not_col_distincts_c O E E' T
  have H0 := H
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact ⟨(Ne.symm H2), (⟨(Ne.symm H2), (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 E O)))))⟩)⟩
theorem Cd_Cd_EqF_c :
    ∀ (P : Tpoint) (Px1 Py1 Px2 Py2 : @F Tpoint _), Cd O E SS U1 U2 P (Px1.1) (Py1.1) → Cd O E SS U1 U2 P (Px2.1) (Py2.1) → Px1 = Px2 ∧ Py1 = Py2 := sorry

theorem sqrt3_square_c :
    ∀ (_tp : Tpoint), sqrt3 * sqrt3 = 1 + 2 :=
  (trans_co_eq_inv_impl_morphism eqF_Transitive (PythF 1 (PythF 1 1) * PythF 1 (PythF 1 1)) (1 * 1 + PythF 1 1 * PythF 1 1) (PythFOk_c 1 (PythF 1 1)) (1 + 2) (1 + 2) (eq_proper_proxy (1 + 2))) ((trans_co_eq_inv_impl_morphism eqF_Transitive (1 * 1 + PythF 1 1 * PythF 1 1) (1 * 1 + (1 * 1 + 1 * 1)) (Reflexive_partial_app_morphism addF_morphism (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) (1 * 1)) (PythF 1 1 * PythF 1 1) (1 * 1 + 1 * 1) (PythFOk_c 1 1)) (1 + 2) (1 + 2) (eq_proper_proxy (1 + 2))) (psos_r1b (1 * 1 + (1 * 1 + 1 * 1)) (1 + (1 + 1)) ((let B := _ - _ (1 * 1 + (1 * 1 + 1 * 1)) (1 + (1 + 1)); (let B0 := zero; (let p21 := PEsub (PEadd (PEmul (PEc 1 % Z) (PEc 1 % Z)) (PEadd (PEmul (PEc 1 % Z) (PEc 1 % Z)) (PEmul (PEc 1 % Z) (PEc 1 % Z)))) (PEadd (PEc 1 % Z) (PEadd (PEc 1 % Z) (PEc 1 % Z))); (let lp21 := nil; (let lci := nil; (let lq := nil; (let q := PEmul (PEc 1 % Z) (PEpow p21 1); (let Hg := rfl; (let Hg0 := (check_correct nil lp21 q (lci , lq) Hg) I; Rintegral_domain_pow (interpret3 (PEc 1 % Z) nil) (interpret3 p21 nil) (N.to_nat 1) integral_domain_one_zero Hg0))))))))))))
theorem characterization_of_congruence_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Cong A B C D ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; let (Dx, Dy) := coordinates_of_point_F SS U1 U2 orthonormal_grid D; (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) - ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy)) = 0 := sorry

theorem characterization_of_betweenness_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), Bet A B C ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; ∃ (T : Tpoint), 0 <= T ∧ T <= 1 ∧ T * (Cx - Ax) = Bx - Ax ∧ T * (Cy - Ay) = By - Ay := sorry

theorem characterization_of_collinearity_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), Col A B C ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; (Ax - Bx) * (By - Cy) - (Ay - By) * (Bx - Cx) = 0 := sorry

theorem characterization_of_equality_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), A = B ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; Ax = Bx ∧ Ay = By := sorry

theorem characterization_of_neq_F_bis_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), A ≠ B ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; ¬ (Ax = Bx) ∨ ¬ (Ay = By) := sorry

theorem characterization_of_equality_F_aux_c :
    ∀ (Ax Ay Bx By : @F Tpoint _), Ax = Bx ∧ Ay = By ↔ (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) = OF := sorry

theorem characterization_of_equality_F_bis_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), A = B ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) = OF := sorry

theorem characterization_of_neq_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), A ≠ B ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; ¬ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) = OF) := sorry

theorem characterization_of_midpoint_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B I : Tpoint), Midpoint I A B ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Ix, Iy) := coordinates_of_point_F SS U1 U2 orthonormal_grid I; Ix * 2 - (Ax + Bx) = 0 ∧ Iy * 2 - (Ay + By) = 0 := sorry

theorem characterization_of_right_triangle_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), Per A B C ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; (Ax - Bx) * (Bx - Cx) + (Ay - By) * (By - Cy) = 0 := sorry

theorem characterization_of_parallelism_F_aux_c :
    ∀ (A B C D : Tpoint), Par A B C D ↔ A ≠ B ∧ C ≠ D ∧ ∃ (P : Tpoint), Midpoint C A P ∧ ∃ (Q : Tpoint), Midpoint Q B P ∧ Col C D Q := by
  intro b0 b1 b2 b3
  exact ⟨(fun H => ⟨((let H0 := par_distincts_c b0 b1 b2 b3 H; (let H1 := H0; (by
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact H3)))), (⟨((let H0 := par_distincts_c b0 b1 b2 b3 H; (let H1 := H0; (by
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H4⟩ := H2
  exact H4)))), ((let e := symmetric_point_construction_c b0 b2; (by
  obtain ⟨x, x0⟩ := e
  exact ⟨x, (⟨x0, ((let e0 := midpoint_existence_c b1 x; (by
  obtain ⟨x1, x2⟩ := e0
  exact ⟨x1, (⟨x2, ((let H0 := (let H0 := par_distincts_c b0 b1 b2 b3 H; (let H1 := H0; (by
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact triangle_mid_par_c b1 b0 x b2 x1 (Ne.symm H3) x0 x2))); (let a := parallel_uniqueness_c b0 b1 b2 b3 b2 x1 b2 H ((by colr)) (par_left_comm_c b1 b0 b2 x1 (par_left_comm_c b0 b1 b2 x1 (par_comm_c b1 b0 x1 b2 H0))) ((by colr)); (by
  obtain ⟨x3, x4⟩ := a
  exact (by colr)))))⟩)⟩)))⟩)⟩)))⟩)⟩), (fun H => (by
  obtain ⟨x, x0⟩ := H
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  obtain ⟨x7, x8⟩ := x6
  obtain ⟨x9, x10⟩ := x8
  have H5 := triangle_mid_par_c b1 b0 x3 b2 x7 (Ne.symm x) x5 x9
  exact par_col_par_c b0 b1 b2 x7 b3 x1 (par_left_comm_c b1 b0 b2 x7 (par_left_comm_c b0 b1 b2 x7 (par_comm_c b1 b0 x7 b2 H5))) ((by colr))))⟩
theorem put_neg_in_goal_c :
    ∀ (_tp : Tpoint), ∀ (A B : Prop), A ∨ B → (¬ A → B) := by
  intro b0 b1 b2 b3
  rcases b2 with H1 | H1
  · have H2 := b3 H1
    exact (H2).elim
  · exact H1
theorem characterization_of_parallelism_F_bis_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Par A B C D ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; let (Dx, Dy) := coordinates_of_point_F SS U1 U2 orthonormal_grid D; (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) = 0 ∧ (¬ (Ax = Bx) ∨ ¬ (Ay = By)) ∧ (¬ (Cx = Dx) ∨ ¬ (Cy = Dy)) := sorry

theorem characterization_of_parallelism_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Par A B C D ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; let (Dx, Dy) := coordinates_of_point_F SS U1 U2 orthonormal_grid D; (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) = 0 ∧ ¬ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) = OF) ∧ ¬ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) = OF) := sorry

theorem characterization_of_perpendicularity_F_bis_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Perp A B C D ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; let (Dx, Dy) := coordinates_of_point_F SS U1 U2 orthonormal_grid D; (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) = OF ∧ (¬ (Ax = Bx) ∨ ¬ (Ay = By)) ∧ (¬ (Cx = Dx) ∨ ¬ (Cy = Dy)) := sorry

theorem characterization_of_perpendicularity_F_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Perp A B C D ↔ let (Ax, Ay) := coordinates_of_point_F SS U1 U2 orthonormal_grid A; let (Bx, By) := coordinates_of_point_F SS U1 U2 orthonormal_grid B; let (Cx, Cy) := coordinates_of_point_F SS U1 U2 orthonormal_grid C; let (Dx, Dy) := coordinates_of_point_F SS U1 U2 orthonormal_grid D; (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) = OF ∧ ¬ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) = OF) ∧ ¬ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) = OF) := sorry

theorem field_prop_c :
    ∀ (a b c d : @F Tpoint _), ¬ b = 0 → ¬ d = 0 → a*d = b*c → a/b = c/d := sorry

theorem field_prop_zero_c :
    ∀ (a b : @F Tpoint _), ¬ b = 0 → a/b = 0 → a = 0 := sorry

theorem field_prop_1_c :
    ∀ (a b c : @F Tpoint _), ¬ b = 0 → a/b = c → a = c*b := sorry

theorem centroid_theorem_c :
    ∀ (A B C A1 B1 C1 G : Tpoint), Midpoint A1 B C → Midpoint B1 A C → Midpoint C1 A B → Col A A1 G → Col B B1 G → Col C C1 G ∨ Col A B C := sorry

theorem signed_area_cyclic_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), signed_area SS U1 U2 orthonormal_grid A B C = signed_area SS U1 U2 orthonormal_grid B C A := sorry

theorem signed_area_perm_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), signed_area SS U1 U2 orthonormal_grid A B C = - signed_area SS U1 U2 orthonormal_grid B A C := sorry

theorem signed_area_sum_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), signed_area SS U1 U2 orthonormal_grid A B C = signed_area SS U1 U2 orthonormal_grid A B D + signed_area SS U1 U2 orthonormal_grid A D C + signed_area SS U1 U2 orthonormal_grid D B C := sorry

theorem co_side_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C P : Tpoint), A ≠ C → ¬ twice_signed_area SS U1 U2 orthonormal_grid P A C = 0 → twice_signed_area SS U1 U2 orthonormal_grid A B C = 0 → ratio SS U1 U2 orthonormal_grid A B A C = twice_signed_area SS U1 U2 orthonormal_grid P A B / twice_signed_area SS U1 U2 orthonormal_grid P A C := sorry

theorem Cong_AM_Cong_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), AM_Cong SS U1 U2 orthonormal_grid A B C D ↔ Cong A B C D := sorry

theorem Col_AM_Col_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), AM_Col SS U1 U2 orthonormal_grid A B C ↔ Col A B C := sorry

theorem Per_AM_Per_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), AM_Per SS U1 U2 orthonormal_grid A B C ↔ Per A B C := sorry

theorem Perp_AM_Perp_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), (AM_Perp SS U1 U2 orthonormal_grid A B C D ∧ A ≠ B ∧ C ≠ D) ↔ Perp A B C D := sorry

theorem AM_Par_ratio_AM_Par_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (P Q C D : Tpoint), AM_Par SS U1 U2 orthonormal_grid P Q C D → ratio SS U1 U2 orthonormal_grid P Q C D = 1 → C ≠ D → AM_Par SS U1 U2 orthonormal_grid D Q P C := sorry

theorem Par_AM_Par_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), (A ≠ B ∧ C ≠ D ∧ AM_Par SS U1 U2 orthonormal_grid A B C D) ↔ Par A B C D := sorry

theorem AM_lower_dim_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∃ (A B C : Tpoint), ¬ AM_Col SS U1 U2 orthonormal_grid A B C :=
  ⟨O, (⟨E, (⟨E', ((subrelation_proper Morphisms_Prop.not_iff_morphism tt (subrelation_respectful (subrelation_refl iff) iff_flip_impl_subrelation) (AM_Col O E E') (Col O E E') (Col_AM_Col_c O E E')) ncolOEE')⟩)⟩)⟩
theorem signed_area_AAB_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), signed_area SS U1 U2 orthonormal_grid A A B = 0 := sorry

theorem signed_area_ABA_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), signed_area SS U1 U2 orthonormal_grid A B A = 0 := sorry

theorem signed_area_ABB_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), signed_area SS U1 U2 orthonormal_grid A B B = 0 := sorry

theorem twice_signed_area_AAB_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), twice_signed_area SS U1 U2 orthonormal_grid A A B = 0 := sorry

theorem twice_signed_area_ABA_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), twice_signed_area SS U1 U2 orthonormal_grid A B A = 0 := sorry

theorem twice_signed_area_ABB_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), twice_signed_area SS U1 U2 orthonormal_grid A B B = 0 := sorry

theorem twice_signed_area_cyclic_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), twice_signed_area SS U1 U2 orthonormal_grid A B C = twice_signed_area SS U1 U2 orthonormal_grid B C A := sorry

theorem twice_signed_area_perm_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), twice_signed_area SS U1 U2 orthonormal_grid A B C = - twice_signed_area SS U1 U2 orthonormal_grid B A C := sorry

theorem AM_Perp_AM_Perp_AM_Par_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D U V : Tpoint), C ≠ D → AM_Perp SS U1 U2 orthonormal_grid A B C D → AM_Perp SS U1 U2 orthonormal_grid U V C D → AM_Par SS U1 U2 orthonormal_grid A B U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have o := point_equality_decidability b0 b1
  rcases o with x | x
  · subst x
    exact (trans_co_eq_inv_impl_morphism eqF_Transitive (twice_signed_area b1 b4 b1 + twice_signed_area b1 b1 b5) (twice_signed_area b1 b4 b1 + 0) (Reflexive_partial_app_morphism addF_morphism (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) (twice_signed_area b1 b4 b1)) (twice_signed_area b1 b1 b5) 0 (twice_signed_area_AAB_c b1 b5)) 0 0 (eq_proper_proxy 0)) ((trans_co_eq_inv_impl_morphism eqF_Transitive (twice_signed_area b1 b4 b1 + 0) (0 + 0) (addF_morphism (twice_signed_area b1 b4 b1) 0 (twice_signed_area_ABA_c b1 b4) 0 0 (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) 0)) 0 0 (eq_proper_proxy 0)) ((let hyp_list := nil; (let fv_list := nil; GeometricField_ring_lemma1 ring_subst_niter fv_list hyp_list (PEadd PEO PEO) PEO I (rfl)))))
  · have H3 := (let H3 := fun A0 B0 C0 D0 => (by
  obtain ⟨x0, _⟩ := Perp_AM_Perp_c A0 B0 C0 D0
  exact x0); H3 b0 b1 b2 b3 (⟨b7, (⟨x, b6⟩)⟩))
    have o0 := point_equality_decidability b4 b5
    rcases o0 with x0 | x0
    · subst x0
      exact (trans_co_eq_inv_impl_morphism eqF_Transitive (twice_signed_area b0 b5 b1 + twice_signed_area b0 b1 b5) (- twice_signed_area b5 b0 b1 + twice_signed_area b0 b1 b5) (addF_morphism (twice_signed_area b0 b5 b1) (- twice_signed_area b5 b0 b1) (twice_signed_area_perm_c b0 b5 b1) (twice_signed_area b0 b1 b5) (twice_signed_area b0 b1 b5) (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) (twice_signed_area b0 b1 b5))) 0 0 (eq_proper_proxy 0)) ((trans_co_eq_inv_impl_morphism eqF_Transitive (- twice_signed_area b5 b0 b1 + twice_signed_area b0 b1 b5) (- twice_signed_area b0 b1 b5 + twice_signed_area b0 b1 b5) (addF_morphism (- twice_signed_area b5 b0 b1) (- twice_signed_area b0 b1 b5) (oppF_morphism (twice_signed_area b5 b0 b1) (twice_signed_area b0 b1 b5) (twice_signed_area_cyclic_c b5 b0 b1)) (twice_signed_area b0 b1 b5) (twice_signed_area b0 b1 b5) (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) (twice_signed_area b0 b1 b5))) 0 0 (eq_proper_proxy 0)) ((let hyp_list := nil; (let fv_list := twice_signed_area b0 b1 b5; GeometricField_ring_lemma1 ring_subst_niter fv_list hyp_list (PEadd (PEopp (PEX Z 1)) (PEX Z 1)) PEO I (rfl)))))
    · have H5 := (let H5 := fun A0 B0 C0 D0 => (by
  obtain ⟨x1, _⟩ := Perp_AM_Perp_c A0 B0 C0 D0
  exact x1); H5 b4 b5 b2 b3 (⟨b8, (⟨x0, b6⟩)⟩))
      have H6 := par_perp2__par_c b2 b3 b2 b3 b0 b1 b4 b5 (par_left_comm_c b3 b2 b2 b3 (par_left_comm_c b2 b3 b2 b3 (par_reflexivity_c b3 b6))) (perp_comm_c b3 b2 b1 b0 (perp_comm_c b2 b3 b0 b1 (perp_sym_c b0 b1 b2 b3 H3))) (perp_comm_c b3 b2 b5 b4 (perp_comm_c b2 b3 b4 b5 (perp_sym_c b4 b5 b2 b3 H5)))
      have H7 := fun A0 B0 C0 D0 => (by
  obtain ⟨_, x2⟩ := Par_AM_Par_c A0 B0 C0 D0
  exact x2)
      have H8 := fun A0 B0 C0 D0 H8 => (by
  obtain ⟨_, x2⟩ := H7 A0 B0 C0 D0 H8
  exact x2)
      have H9 := fun A0 B0 C0 D0 H9 => (by
  obtain ⟨_, x2⟩ := H8 A0 B0 C0 D0 H9
  exact x2)
      exact H9 b0 b1 b4 b5 H6
theorem Py_triv_ABB_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B : Tpoint), Py SS U1 U2 orthonormal_grid A B B = 0 := sorry

theorem AM_Perp_triv1_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), AM_Perp SS U1 U2 orthonormal_grid A B C C :=
  fun b0 b1 b2 =>
  (trans_co_eq_inv_impl_morphism eqF_Transitive (Py b0 b2 b2 - Py b1 b2 b2) (0 - Py b1 b2 b2) (subF_morphism (Py b0 b2 b2) 0 (Py_triv_ABB_c b0 b2) (Py b1 b2 b2) (Py b1 b2 b2) (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) (Py b1 b2 b2))) 0 0 (eq_proper_proxy 0)) ((trans_co_eq_inv_impl_morphism eqF_Transitive (0 - Py b1 b2 b2) (0 - 0) (Reflexive_partial_app_morphism subF_morphism (reflexive_proper_proxy (reflexive_reflexive_proxy eqF_Reflexive) 0) (Py b1 b2 b2) 0 (Py_triv_ABB_c b1 b2)) 0 0 (eq_proper_proxy 0)) ((let hyp_list := nil; (let fv_list := nil; GeometricField_ring_lemma1 ring_subst_niter fv_list hyp_list (PEsub PEO PEO) PEO I (rfl)))))
theorem AM_Perp_triv2_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), AM_Perp SS U1 U2 orthonormal_grid A A B C :=
  fun b0 b1 b2 =>
  ((let hyp_list := nil; (let fv_list := Py b0 b1 b2; GeometricField_ring_lemma1 ring_subst_niter fv_list hyp_list (PEsub (PEX Z 1) (PEX Z 1)) PEO I (rfl))))
theorem AM_perp_AM_Par_AM_perp_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D U V : Tpoint), A ≠ B → AM_Perp SS U1 U2 orthonormal_grid A B C D → AM_Par SS U1 U2 orthonormal_grid A B U V → AM_Perp SS U1 U2 orthonormal_grid U V C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have o := point_equality_decidability b2 b3
  rcases o with x | x
  · subst x
    exact AM_Perp_triv1_c b4 b5 b3
  · have o0 := point_equality_decidability b4 b5
    rcases o0 with x0 | x0
    · subst x0
      exact AM_Perp_triv2_c b5 b2 b3
    · have H4 := (let H4 := fun A0 B0 C0 D0 => (by
  obtain ⟨x1, _⟩ := Perp_AM_Perp_c A0 B0 C0 D0
  exact x1); H4 b0 b1 b2 b3 (⟨b7, (⟨b6, x⟩)⟩))
      have H5 := (let H5 := fun A0 B0 C0 D0 => (by
  obtain ⟨x1, _⟩ := Par_AM_Par_c A0 B0 C0 D0
  exact x1); H5 b0 b1 b4 b5 (⟨b6, (⟨x0, b8⟩)⟩))
      have H6 := par_perp__perp_c b0 b1 b4 b5 b2 b3 H5 H4
      have H7 := fun A0 B0 C0 D0 => (by
  obtain ⟨_, x2⟩ := Perp_AM_Perp_c A0 B0 C0 D0
  exact x2)
      have H8 := fun A0 B0 C0 D0 H8 => (by
  obtain ⟨x1, _⟩ := H7 A0 B0 C0 D0 H8
  exact x1)
      exact H8 b4 b5 b2 b3 H6
theorem perp_triangle_area_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C : Tpoint), A ≠ C → AM_Per SS U1 U2 orthonormal_grid A B C → twice_signed_area SS U1 U2 orthonormal_grid A B C * twice_signed_area SS U1 U2 orthonormal_grid A B C = square_dist SS U1 U2 orthonormal_grid A B * square_dist SS U1 U2 orthonormal_grid B C := sorry

theorem triangle_area_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C H : Tpoint), AM_on_foot SS U1 U2 orthonormal_grid H A B C → twice_signed_area SS U1 U2 orthonormal_grid A B C * twice_signed_area SS U1 U2 orthonormal_grid A B C = square_dist SS U1 U2 orthonormal_grid A H * square_dist SS U1 U2 orthonormal_grid B C := sorry

theorem chasles_ratios_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C P Q : Tpoint), P ≠ Q → ratio SS U1 U2 orthonormal_grid A B P Q + ratio SS U1 U2 orthonormal_grid B C P Q = ratio SS U1 U2 orthonormal_grid A C P Q := sorry

theorem ratio_zero_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), C ≠ D → AM_Par SS U1 U2 orthonormal_grid A B C D → (ratio SS U1 U2 orthonormal_grid A B C D = 0 → A = B) := sorry

theorem axiom_A2b_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B P P' r : Tpoint), A ≠ B → Col A B P → ratio SS U1 U2 orthonormal_grid A P A B = r → Col A B P' → ratio SS U1 U2 orthonormal_grid A P' A B = r → P = P' := sorry

theorem axiom_A2a_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B r : Tpoint), A ≠ B → ∃ (P : Tpoint), AM_Col SS U1 U2 orthonormal_grid A B P ∧ ratio SS U1 U2 orthonormal_grid A P A B = r := sorry

theorem supplement_AM_CongA_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B M C : Tpoint), Midpoint M A B → AM_CongAL SS U1 U2 orthonormal_grid A M C B M C := sorry

theorem exists_equilateral_triangle_c :
    ∀ (A B : Tpoint), ∃ (C : Tpoint), Cong A B A C ∧ Cong A B B C := sorry

theorem triangles_same_base_c :
    ∀ (SS U1 U2 : Tpoint) (orthonormal_grid : Cs O E SS U1 U2), ∀ (A B C D : Tpoint), Par A D B C → signed_area SS U1 U2 orthonormal_grid A B C = signed_area SS U1 U2 orthonormal_grid D B C := sorry

#print axioms GeocoqTranslate.Tarski.Base.sum_col_c
#print axioms GeocoqTranslate.Tarski.Base.sum_f_c
#print axioms GeocoqTranslate.Tarski.Base.prod_f_c
#print axioms GeocoqTranslate.Tarski.Base.diff_col_c
#print axioms GeocoqTranslate.Tarski.Base.diff_f_c
#print axioms GeocoqTranslate.Tarski.Base.opp_col_c
#print axioms GeocoqTranslate.Tarski.Base.opp_f_c
#print axioms GeocoqTranslate.Tarski.Base.opp_pythrel_c
#print axioms GeocoqTranslate.Tarski.Base.pythrel_null_c
#print axioms GeocoqTranslate.Tarski.Base.pythrel_not_null_c
#print axioms GeocoqTranslate.Tarski.Base.pythrelOO_c
#print axioms GeocoqTranslate.Tarski.Base.Pyth_f_c
#print axioms GeocoqTranslate.Tarski.Base.inv_exists_with_notation_c
#print axioms GeocoqTranslate.Tarski.Base.inv_col_c
#print axioms GeocoqTranslate.Tarski.Base.inv_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.inv_f_c
#print axioms GeocoqTranslate.Tarski.Base.div_exists_c
#print axioms GeocoqTranslate.Tarski.Base.div_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.div_col_c
#print axioms GeocoqTranslate.Tarski.Base.div_f_c
#print axioms GeocoqTranslate.Tarski.Base.eq_dec_F_c
#print axioms GeocoqTranslate.Tarski.Base.neg_and_eqF_c
#print axioms GeocoqTranslate.Tarski.Base.neq20_c
#print axioms GeocoqTranslate.Tarski.Base.ringF_c
#print axioms GeocoqTranslate.Tarski.Base.fieldF_c
#print axioms GeocoqTranslate.Tarski.Base.Fmult_integral_c
#print axioms GeocoqTranslate.Tarski.Base.PythFOk_c
#print axioms GeocoqTranslate.Tarski.Base.subF__eq0_c
#print axioms GeocoqTranslate.Tarski.Base.mulF__eq0_c
#print axioms GeocoqTranslate.Tarski.Base.neqO_mul_neqO_c
#print axioms GeocoqTranslate.Tarski.Base.oppF_neq0_c
#print axioms GeocoqTranslate.Tarski.Base.Ps_One_c
#print axioms GeocoqTranslate.Tarski.Base.Cd_Cd_EqF_c
#print axioms GeocoqTranslate.Tarski.Base.sqrt3_square_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_congruence_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_betweenness_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_collinearity_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_equality_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_neq_F_bis_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_equality_F_aux_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_equality_F_bis_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_neq_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_midpoint_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_right_triangle_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_parallelism_F_aux_c
#print axioms GeocoqTranslate.Tarski.Base.put_neg_in_goal_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_parallelism_F_bis_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_parallelism_F_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_perpendicularity_F_bis_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_perpendicularity_F_c
#print axioms GeocoqTranslate.Tarski.Base.field_prop_c
#print axioms GeocoqTranslate.Tarski.Base.field_prop_zero_c
#print axioms GeocoqTranslate.Tarski.Base.field_prop_1_c
#print axioms GeocoqTranslate.Tarski.Base.centroid_theorem_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_cyclic_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_perm_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_sum_c
#print axioms GeocoqTranslate.Tarski.Base.co_side_c
#print axioms GeocoqTranslate.Tarski.Base.Cong_AM_Cong_c
#print axioms GeocoqTranslate.Tarski.Base.Col_AM_Col_c
#print axioms GeocoqTranslate.Tarski.Base.Per_AM_Per_c
#print axioms GeocoqTranslate.Tarski.Base.Perp_AM_Perp_c
#print axioms GeocoqTranslate.Tarski.Base.AM_Par_ratio_AM_Par_c
#print axioms GeocoqTranslate.Tarski.Base.Par_AM_Par_c
#print axioms GeocoqTranslate.Tarski.Base.AM_lower_dim_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_AAB_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_ABA_c
#print axioms GeocoqTranslate.Tarski.Base.signed_area_ABB_c
#print axioms GeocoqTranslate.Tarski.Base.twice_signed_area_AAB_c
#print axioms GeocoqTranslate.Tarski.Base.twice_signed_area_ABA_c
#print axioms GeocoqTranslate.Tarski.Base.twice_signed_area_ABB_c
#print axioms GeocoqTranslate.Tarski.Base.twice_signed_area_cyclic_c
#print axioms GeocoqTranslate.Tarski.Base.twice_signed_area_perm_c
#print axioms GeocoqTranslate.Tarski.Base.AM_Perp_AM_Perp_AM_Par_c
#print axioms GeocoqTranslate.Tarski.Base.Py_triv_ABB_c
#print axioms GeocoqTranslate.Tarski.Base.AM_Perp_triv1_c
#print axioms GeocoqTranslate.Tarski.Base.AM_Perp_triv2_c
#print axioms GeocoqTranslate.Tarski.Base.AM_perp_AM_Par_AM_perp_c
#print axioms GeocoqTranslate.Tarski.Base.perp_triangle_area_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_area_c
#print axioms GeocoqTranslate.Tarski.Base.chasles_ratios_c
#print axioms GeocoqTranslate.Tarski.Base.ratio_zero_c
#print axioms GeocoqTranslate.Tarski.Base.axiom_A2b_c
#print axioms GeocoqTranslate.Tarski.Base.axiom_A2a_c
#print axioms GeocoqTranslate.Tarski.Base.supplement_AM_CongA_c
#print axioms GeocoqTranslate.Tarski.Base.exists_equilateral_triangle_c
#print axioms GeocoqTranslate.Tarski.Base.triangles_same_base_c
end GeocoqTranslate.Tarski.Base