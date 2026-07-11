import GeocoqTranslate.Tarski_dev.Ch10Line2Extra

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l11_3_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → ∃ (A' : Tpoint), ∃ (C' : Tpoint), ∃ (D' : Tpoint), ∃ (F' : Tpoint), Out B A' A ∧ Out B C C' ∧ Out E D' D ∧ Out E F F' ∧ Cong_3 A' B C' D' E F' := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨A', H8⟩ := H7
  obtain ⟨C', H9⟩ := H8
  obtain ⟨D', H10⟩ := H9
  obtain ⟨F', H11⟩ := H10
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, H21⟩ := H19
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨H24, H25⟩ := H23
  obtain ⟨H26, H27⟩ := H25
  exact ⟨A', (⟨C', (⟨D', (⟨F', ((let H28 := bet_neq21__neq H24 H6; (let H29 := bet_neq21__neq H20 H4; (let H30 := bet_neq21__neq H16 H2; (let H31 := bet_neq21__neq H12 H0; (let H32 := cong_diff_4_c b2 C' b4 b5 H6 H18; (let H33 := cong_diff_4_c b0 A' b4 b3 H4 H14; (let H34 := cong_diff_4_c b5 F' b1 b2 H2 H26; (let H35 := cong_diff_4_c b3 D' b1 b0 H0 H22; ⟨(⟨(Ne.symm H31), (⟨H0, (Or.inr H12)⟩)⟩), (⟨(⟨H2, (⟨(Ne.symm H30), (Or.inl H16)⟩)⟩), (⟨(⟨(Ne.symm H29), (⟨H4, (Or.inr H20)⟩)⟩), (⟨(⟨H6, (⟨(Ne.symm H28), (Or.inl H24)⟩)⟩), (⟨(cong_left_commutativity (l2_11 H12 (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_3421_c b3 D' b1 b0 H22))) (cong_symmetry (cong_symmetry (cong_right_commutativity H14))))), (⟨H27, (cong_left_commutativity (l2_11 (between_symmetry H16) H24 (cong_symmetry (cong_symmetry (cong_left_commutativity H18))) (cong_symmetry (cong_symmetry (cong_4312_c b5 F' b1 b2 H26)))))⟩)⟩)⟩)⟩)⟩)⟩)))))))))⟩)⟩)⟩)⟩
theorem l11_aux_c :
    ∀ (B A A' A0 E D D' D0 : Tpoint), Out B A A' → Out E D D' → Cong B A' E D' → Bet B A A0 → Bet E D D0 → Cong A A0 E D → Cong D D0 B A → Cong B A0 E D0 ∧ Cong A' A0 D' D0 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  have H6 := (by
  obtain ⟨H6, H7⟩ := b8
  obtain ⟨_, _⟩ := H7
  exact H6)
  have H7 := cong_right_commutativity (l2_11 b11 (between_symmetry b12) (cong_symmetry (cong_symmetry (cong_3421_c b5 b7 b0 b1 b14))) (cong_symmetry (cong_symmetry (cong_right_commutativity b13))))
  exact ⟨H7, ((by
  obtain ⟨H8, H9⟩ := b9
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := b8
  obtain ⟨H14, H15⟩ := H13
  rcases H11 with H16 | H16
  · rcases H15 with H17 | H17
    · have H18 := l5_1 (Ne.symm H6) H17 b11
      rcases H18 with H19 | H19
      · have H20 := cong_preserves_bet_c b0 b2 b3 b4 b6 b7 H19 b10 H7 (⟨H10, (⟨((let H20 := bet_neq21__neq b11 H6; (let H21 := bet_neq21__neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H21))))), (l5_1 (Ne.symm H8) H16 b12)⟩)⟩)
        exact cong_commutativity (l4_3 (between_symmetry H19) (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
      · have H20 := cong_preserves_bet_c b0 b3 b2 b4 b7 b6 H19 H7 b10 (⟨((let H20 := bet_neq21__neq b11 H6; (let H21 := bet_neq21__neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H21))))), (⟨((let H20 := bet_neq21__neq b11 H6; (let H21 := bet_neq21__neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; H10))))), (l5_1 (Ne.symm H8) b12 H16)⟩)⟩)
        exact l4_3 (between_symmetry H19) (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_commutativity b10))) (cong_symmetry (cong_symmetry (cong_commutativity H7)))
    · exact cong_commutativity (l4_3 (between_symmetry (between_exchange4 H17 b11)) (between_symmetry (cong_preserves_bet_c b0 b2 b3 b4 b6 b7 (between_exchange4 H17 b11) b10 H7 (⟨H10, (⟨((let H18 := bet_neq21__neq b11 H6; (let H19 := bet_neq21__neq b12 H8; (let H20 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H21 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H19))))), (l5_1 (Ne.symm H8) H16 b12)⟩)⟩))) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
  · rcases H15 with H17 | H17
    · exact cong_commutativity (l4_3 (between_symmetry (cong_preserves_bet_c b4 b6 b7 b0 b2 b3 (between_exchange4 H16 b12) (cong_symmetry b10) (cong_symmetry H7) (⟨H14, (⟨((let H18 := bet_neq21__neq b11 H6; (let H19 := bet_neq21__neq b12 H8; (let H20 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H21 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H18))))), (l5_1 (Ne.symm H6) H17 b11)⟩)⟩))) (between_symmetry (between_exchange4 H16 b12)) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
    · exact cong_commutativity (l4_3 (between_symmetry (between_exchange4 H17 b11)) (between_symmetry (between_exchange4 H16 b12)) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))))⟩
theorem l11_3_bis_c :
    ∀ (A B C D E F : Tpoint), (∃ (A' : Tpoint), ∃ (C' : Tpoint), ∃ (D' : Tpoint), ∃ (F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong_3 A' B C' D' E F') → CongA A B C D E F := sorry
theorem l11_4_1_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ (∀ (A' C' D' F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F') := by
  intro b0 b1 b2 b3 b4 b5 b6
  have HH := b6
  have HH0 := l11_3_c b0 b1 b2 b3 b4 b5 HH
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, _⟩ := H5
  exact ⟨H0, (⟨H2, (⟨H4, (⟨H6, (fun A' C' D' F' H7 => (by
  obtain ⟨A0, H8⟩ := HH0
  obtain ⟨H9, H10⟩ := H7
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨C0, H19⟩ := H8
  obtain ⟨D0, H20⟩ := H19
  obtain ⟨F0, H21⟩ := H20
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨H24, H25⟩ := H23
  obtain ⟨H26, H27⟩ := H25
  obtain ⟨H28, H29⟩ := H27
  obtain ⟨H30, H31⟩ := H29
  obtain ⟨H32, H33⟩ := H31
  have H34 := l6_7_c b1 A' b0 A0 H9 (l6_6 H22)
  have H35 := l6_7_c b4 D' b3 D0 H13 (l6_6 H26)
  have H36 := out_cong_cong_c b1 A' A0 b4 D' D0 H34 H35 H17 (cong_symmetry (cong_symmetry (cong_commutativity H30)))
  have H37 := l4_16 (⟨(col_permutation_5_c b1 A' A0 (out_col H34)), (⟨(⟨(cong_symmetry (cong_symmetry (cong_commutativity H30))), (⟨H17, (cong_symmetry (cong_symmetry (cong_commutativity H36)))⟩)⟩), (⟨H33, H32⟩)⟩)⟩) ((fun H37 => (by
  subst H37
  obtain ⟨H39, H40⟩ := H22
  obtain ⟨_, _⟩ := H40
  exact ((H39 rfl)).elim)))
  have H38 := l6_7_c b1 C' b2 C0 H11 H24
  have H39 := l6_7_c b4 F' b5 F0 H15 H28
  have H40 := out_cong_cong_c b1 C' C0 b4 F' F0 H38 H39 H18 H33
  exact cong_commutativity (l4_16 (⟨(col_permutation_5_c b1 C' C0 (out_col H38)), (⟨(⟨H33, (⟨H18, (cong_symmetry (cong_symmetry (cong_commutativity H40)))⟩)⟩), (⟨H17, (cong_symmetry (cong_symmetry (cong_commutativity H37)))⟩)⟩)⟩) ((let H41 := out_distinct_c b4 F' F0 H39; (let H42 := H41; (by
  obtain ⟨H43, H44⟩ := H42
  have H45 := cong_diff_4_c b1 C0 b4 F0 H44 H33
  have H46 := cong_diff_4_c b1 C' b4 F' H43 H18
  have H47 := out_distinct_c b4 D' D0 H35
  have H48 := H47
  obtain ⟨H49, H50⟩ := H48
  have H51 := cong_diff_3_c A0 b1 D0 b4 H50 H30
  have H52 := cong_diff_4_c b1 A' b4 D' H49 H17
  exact H45)))))))⟩)⟩)⟩)⟩
theorem l11_4_2_c :
    ∀ (A B C D E F : Tpoint), (A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ (∀ (A' C' D' F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F')) → CongA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  exact l11_3_bis_c b0 b1 b2 b3 b4 b5 ((let sg := segment_construction b1 b0 b4 b3; (by
  obtain ⟨A', H8⟩ := sg
  obtain ⟨H9, H10⟩ := H8
  have sg0 := segment_construction b1 b2 b4 b5
  obtain ⟨C', H11⟩ := sg0
  obtain ⟨H12, H13⟩ := H11
  have sg1 := segment_construction b4 b3 b1 b0
  obtain ⟨D', H14⟩ := sg1
  obtain ⟨H15, H16⟩ := H14
  have sg2 := segment_construction b4 b5 b1 b2
  obtain ⟨F', H17⟩ := sg2
  obtain ⟨H18, H19⟩ := H17
  exact ⟨A', (⟨C', (⟨D', (⟨F', ((let H20 := cong_right_commutativity (l2_11 (between_symmetry H9) H15 (cong_symmetry (cong_symmetry (cong_left_commutativity H10))) (cong_symmetry (cong_symmetry (cong_4312_c b3 D' b1 b0 H16)))); (let H21 := cong_right_commutativity (l2_11 H12 (between_symmetry H18) (cong_symmetry (cong_symmetry (cong_3421_c b5 F' b1 b2 H19))) (cong_symmetry (cong_symmetry (cong_right_commutativity H13)))); (let H22 := bet_neq21__neq H18 H6; (let H23 := bet_neq21__neq H15 H4; (let H24 := bet_neq21__neq H12 H2; (let H25 := bet_neq21__neq H9 H0; (let H26 := cong_diff_4_c b2 C' b4 b5 H6 H13; (let H27 := cong_diff_4_c b0 A' b4 b3 H4 H10; (let H28 := cong_diff_4_c b5 F' b1 b2 H2 H19; (let H29 := cong_diff_4_c b3 D' b1 b0 H0 H16; ⟨(⟨(Ne.symm H25), (⟨H0, (Or.inr H9)⟩)⟩), (⟨(⟨(Ne.symm H24), (⟨H2, (Or.inr H12)⟩)⟩), (⟨(⟨(Ne.symm H23), (⟨H4, (Or.inr H15)⟩)⟩), (⟨(⟨(Ne.symm H22), (⟨H6, (Or.inr H18)⟩)⟩), (⟨H20, (⟨(H7 A' C' D' F' (⟨(⟨(Ne.symm H25), (⟨H0, (Or.inr H9)⟩)⟩), (⟨(⟨(Ne.symm H24), (⟨H2, (Or.inr H12)⟩)⟩), (⟨(⟨(Ne.symm H23), (⟨H4, (Or.inr H15)⟩)⟩), (⟨(⟨(Ne.symm H22), (⟨H6, (Or.inr H18)⟩)⟩), (⟨(cong_symmetry (cong_symmetry (cong_commutativity H20))), H21⟩)⟩)⟩)⟩)⟩)), H21⟩)⟩)⟩)⟩)⟩)⟩)))))))))))⟩)⟩)⟩)⟩)))
theorem conga_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → CongA A B C A B C :=
  fun b0 b1 b2 b3 b4 =>
  l11_3_bis_c b0 b1 b2 b0 b1 b2 (⟨b0, (⟨b2, (⟨b0, (⟨b2, (⟨(⟨b3, (⟨b3, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b1)))))⟩)⟩), (⟨(⟨b4, (⟨b4, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b2 b1)))))⟩)⟩), (⟨(⟨b3, (⟨b3, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b1)))))⟩)⟩), (⟨(⟨b4, (⟨b4, (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b2 b1)))))⟩)⟩), (⟨(cong_reflexivity b0 b1), (⟨(cong_reflexivity b0 b2), (cong_reflexivity b1 b2)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem conga_sym_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → CongA A' B' C' A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨A0, H8⟩ := H7
  obtain ⟨C0, H9⟩ := H8
  obtain ⟨D0, H10⟩ := H9
  obtain ⟨F0, H11⟩ := H10
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, H21⟩ := H19
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨H24, H25⟩ := H23
  obtain ⟨H26, H27⟩ := H25
  exact ⟨H4, (⟨H6, (⟨H0, (⟨H2, (⟨D0, (⟨F0, (⟨A0, (⟨C0, (⟨H20, (⟨H22, (⟨H24, (⟨H26, (⟨H12, (⟨H14, (⟨H16, (⟨H18, (cong_symmetry H27)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem l11_10_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), CongA A B C D E F → Out B A' A → Out B C' C → Out E D' D → Out E F' F → CongA A' B C' D' E F' := sorry
theorem out2__conga_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → CongA A B C A' B C' := by
  intro b0 b1 b2 b3 b4 b5 b6
  have H := out_distinct_c b1 b4 b2 b6
  have H0 := H
  obtain ⟨_, H1⟩ := H0
  have H2 := out_distinct_c b1 b3 b0 b5
  have H3 := H2
  obtain ⟨_, H4⟩ := H3
  exact l11_10_c b0 b1 b2 b0 b1 b2 b0 b2 b3 b4 (conga_refl_c b0 b1 b2 H4 H1) (l6_6 (l6_6 (out_trivial H4))) (l6_6 (l6_6 (out_trivial H1))) b5 b6
theorem cong3_diff_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → Cong_3 A B C A' B' C' → A' ≠ B' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨_, _⟩ := H2
  have H3 := cong_diff b6 H1
  exact H3
theorem cong3_diff2_c :
    ∀ (A B C A' B' C' : Tpoint), B ≠ C → Cong_3 A B C A' B' C' → B' ≠ C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨_, H2⟩ := H1
  have H3 := cong_diff b6 H2
  exact H3
theorem cong3_conga_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → C ≠ B → Cong_3 A B C A' B' C' → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  (let H2 := cong3_diff_c b0 b1 b2 b3 b4 b5 b6 b8; (let H3 := cong3_diff2_c b0 b1 b2 b3 b4 b5 ((fun H3 => b7 (Eq.symm H3))) b8; l11_3_bis_c b0 b1 b2 b3 b4 b5 (⟨b0, (⟨b2, (⟨b3, (⟨b5, (⟨(l6_6 (l6_6 (out_trivial b6))), (⟨(l6_6 (l6_6 (out_trivial b7))), (⟨(l6_6 (l6_6 (out_trivial H2))), (⟨(l6_6 (l6_6 (out_trivial (Ne.symm H3)))), b8⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)))
theorem cong3_conga2_c :
    ∀ (A B C A' B' C' A'' B'' C'' : Tpoint), Cong_3 A B C A' B' C' → CongA A B C A'' B'' C'' → CongA A' B' C' A'' B'' C'' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  obtain ⟨H1, H2⟩ := b10
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨A0, H9⟩ := H8
  obtain ⟨C0, H10⟩ := H9
  obtain ⟨A2, H11⟩ := H10
  obtain ⟨C2, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H20
  obtain ⟨H23, H24⟩ := H22
  obtain ⟨H25, H26⟩ := H24
  obtain ⟨H27, H28⟩ := H26
  obtain ⟨H29, H30⟩ := b9
  obtain ⟨H31, H32⟩ := H30
  have H33 := bet_neq21__neq H25 H7
  have H34 := bet_neq21__neq H21 H5
  have H35 := bet_neq21__neq H17 H3
  have H36 := bet_neq21__neq H13 H1
  have H37 := cong_diff H1 H29
  have H38 := cong_diff_2_c b1 b2 b4 b5 H3 H32
  have H39 := cong_diff_4_c b2 C0 b7 b8 H7 H19
  have H40 := cong_diff_4_c b0 A0 b7 b6 H5 H15
  have H41 := cong_diff_4_c b8 C2 b1 b2 H3 H27
  have H42 := cong_diff_4_c b6 A2 b1 b0 H1 H23
  exact ⟨H37, (⟨(Ne.symm H38), (⟨H5, (⟨H7, ((let sg := segment_construction b4 b3 b7 b6; (by
  obtain ⟨A1, H43⟩ := sg
  obtain ⟨H44, H45⟩ := H43
  have sg0 := segment_construction b4 b5 b7 b8
  obtain ⟨C1, H46⟩ := sg0
  obtain ⟨H47, H48⟩ := H46
  exact ⟨A1, (⟨C1, (⟨A2, (⟨C2, (⟨H44, (⟨H45, (⟨H47, (⟨H48, (⟨H21, (⟨(cong_transitivity H23 (cong_symmetry (cong_symmetry (cong_commutativity H29)))), (⟨H25, (⟨(cong_transitivity H27 H32), ((let H49 := cong_transitivity H15 (cong_symmetry H45); (let H50 := l2_11 H13 H44 (cong_symmetry (cong_symmetry (cong_commutativity H29))) H49; (let H51 := cong_transitivity H19 (cong_symmetry H48); (let H52 := l2_11 H17 H47 H32 H51; (let H53 := ((let H53 := bet_col_c b4 b5 C1 H47; (let H54 := bet_col_c b4 b3 A1 H44; (let H55 := bet_col_c b7 b8 C2 H25; (let H56 := bet_col_c b7 b6 A2 H21; (let H57 := bet_col_c b1 b2 C0 H17; (let H58 := bet_col_c b1 b0 A0 H13; ⟨H58, (⟨(⟨(cong_symmetry (cong_symmetry (cong_commutativity H29))), (⟨H50, H49⟩)⟩), (⟨H32, H31⟩)⟩)⟩))))))); (let H54 := l4_16 H53 (Ne.symm H1); cong_commutativity ((let H55 := l4_16 (((let H55 := bet_col_c b4 b5 C1 H47; (let H56 := bet_col_c b4 b3 A1 H44; (let H57 := bet_col_c b7 b8 C2 H25; (let H58 := bet_col_c b7 b6 A2 H21; (let H59 := bet_col_c b1 b2 C0 H17; (let H60 := bet_col_c b1 b0 A0 H13; ⟨H59, (⟨(⟨H32, (⟨H52, H51⟩)⟩), (⟨H50, (cong_symmetry (cong_symmetry (cong_commutativity H54)))⟩)⟩)⟩)))))))) (Ne.symm H3); cong_transitivity (cong_symmetry (cong_symmetry (cong_3421_c C0 A0 C1 A1 H55))) (cong_symmetry (cong_symmetry (cong_right_commutativity H28))))))))))))⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)))⟩)⟩)⟩)⟩
theorem conga_diff1_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → A ≠ B := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  exact H0
theorem conga_diff2_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → C ≠ B := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H0⟩ := b6
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  exact H1
theorem conga_diff45_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → A' ≠ B' :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga_diff1_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b6)
theorem conga_diff56_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → C' ≠ B' :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga_diff2_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b6)
theorem conga_trans_c :
    ∀ (A B C A' B' C' A'' B'' C'' : Tpoint), CongA A B C A' B' C' → CongA A' B' C' A'' B'' C'' → CongA A B C A'' B'' C'' := sorry
theorem conga_pseudo_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → CongA A B C C B A := sorry
theorem conga_trivial_1_c :
    ∀ (A B C D : Tpoint), A ≠ B → C ≠ D → CongA A B A C D C := by
  intro b0 b1 b2 b3 b4 b5
  exact ⟨b4, (⟨b4, (⟨b5, (⟨b5, ((let sg := segment_construction b1 b0 b3 b2; (by
  obtain ⟨A', H1⟩ := sg
  obtain ⟨H2, H3⟩ := H1
  have sg0 := segment_construction b3 b2 b1 b0
  obtain ⟨C', H4⟩ := sg0
  obtain ⟨H5, H6⟩ := H4
  exact ⟨A', (⟨A', (⟨C', (⟨C', (⟨H2, (⟨H3, (⟨H2, (⟨H3, (⟨H5, (⟨H6, (⟨H5, (⟨H6, (cong_trivial_identity A' C')⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)))⟩)⟩)⟩)⟩
theorem l11_13_c :
    ∀ (A B C D E F A' D' : Tpoint), CongA A B C D E F → Bet A B A' → A' ≠ B → Bet D E D' → D' ≠ E → CongA A' B C D' E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  obtain ⟨H4, H5⟩ := b8
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨A'', H12⟩ := H11
  obtain ⟨C'', H13⟩ := H12
  obtain ⟨D'', H14⟩ := H13
  obtain ⟨F'', H15⟩ := H14
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, H21⟩ := H19
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨H24, H25⟩ := H23
  obtain ⟨H26, H27⟩ := H25
  obtain ⟨H28, H29⟩ := H27
  obtain ⟨H30, H31⟩ := H29
  have sg := segment_construction b1 b6 b4 b7
  obtain ⟨A0, H32⟩ := sg
  obtain ⟨H33, H34⟩ := H32
  have sg0 := segment_construction b4 b7 b1 b6
  obtain ⟨D0, H35⟩ := sg0
  obtain ⟨H36, H37⟩ := H35
  exact ⟨b10, (⟨H6, (⟨b12, (⟨H10, (⟨A0, (⟨C'', (⟨D0, (⟨F'', (⟨H33, (⟨H34, (⟨H20, (⟨H22, (⟨H36, (⟨H37, (⟨H28, (⟨H30, (five_segment_with_def (⟨(outer_transitivity_between2 (between_symmetry H16) (outer_transitivity_between b9 H33 (Ne.symm b10)) H4), (⟨(outer_transitivity_between2 (between_symmetry H24) (outer_transitivity_between b11 H36 (Ne.symm b12)) H8), (⟨(cong_left_commutativity (l2_11 H16 (between_symmetry H24) (cong_symmetry (cong_symmetry (cong_3421_c b3 D'' b1 b0 H26))) (cong_symmetry (cong_symmetry (cong_right_commutativity H18))))), (⟨(cong_right_commutativity (l2_11 H33 (between_symmetry H36) (cong_symmetry (cong_symmetry (cong_symmetry (cong_left_commutativity H37)))) (cong_symmetry (cong_symmetry (cong_right_commutativity H34))))), (⟨H31, (cong_right_commutativity (l2_11 H20 (between_symmetry H28) (cong_symmetry (cong_symmetry (cong_3421_c b5 F'' b1 b2 H30))) (cong_symmetry (cong_symmetry (cong_right_commutativity H22)))))⟩)⟩)⟩)⟩)⟩) ((let H38 := bet_neq12__neq b11 H8; (let H39 := bet_neq12__neq b9 H4; (let H40 := bet_neq21__neq H36 b12; (let H41 := bet_neq21__neq H33 b10; (let H42 := bet_neq21__neq H28 H10; (let H43 := bet_neq21__neq H24 H8; (let H44 := bet_neq21__neq H20 H6; (let H45 := bet_neq21__neq H16 H4; (let H46 := cong_diff_4_c b6 A0 b4 b7 b12 H34; (let H47 := cong_diff_4_c b7 D0 b1 b6 b10 H37; (let H48 := cong_diff_4_c b2 C'' b4 b5 H10 H22; (let H49 := cong_diff_4_c b0 A'' b4 b3 H8 H18; (let H50 := cong_diff_4_c b5 F'' b1 b2 H6 H30; (let H51 := cong_diff_4_c b3 D'' b1 b0 H4 H26; Ne.symm H45))))))))))))))))⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem conga_right_comm_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA A B C F E D := by
  intro b0 b1 b2 b3 b4 b5 b6
  exact conga_trans_c b0 b1 b2 b3 b4 b5 b5 b4 b3 b6 ((by
  obtain ⟨_, H0⟩ := b6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, _⟩ := H3
  exact conga_pseudo_refl_c b3 b4 b5 H2 H4))
theorem conga_left_comm_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA C B A D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga_sym_c b3 b4 b5 b2 b1 b0 (conga_right_comm_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b6))
theorem conga_comm_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA C B A F E D :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga_left_comm_c b0 b1 b2 b5 b4 b3 (conga_right_comm_c b0 b1 b2 b3 b4 b5 b6)
theorem conga_line_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → B ≠ C → A' ≠ B' → B' ≠ C' → Bet A B C → Bet A' B' C' → CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have H5 := bet_neq12__neq b11 b8
  have H6 := bet_neq12__neq b10 b6
  have sg := segment_construction b1 b2 b4 b5
  obtain ⟨C0, H7⟩ := sg
  obtain ⟨H8, H9⟩ := H7
  have sg0 := segment_construction b4 b5 b1 b2
  obtain ⟨C1, H10⟩ := sg0
  obtain ⟨H11, H12⟩ := H10
  have sg1 := segment_construction b1 b0 b4 b3
  obtain ⟨A0, H13⟩ := sg1
  obtain ⟨H14, H15⟩ := H13
  have sg2 := segment_construction b4 b3 b1 b0
  obtain ⟨A1, H16⟩ := sg2
  obtain ⟨H17, H18⟩ := H16
  exact ⟨b6, (⟨(Ne.symm b7), (⟨b8, (⟨(Ne.symm b9), (⟨A0, (⟨C0, (⟨A1, (⟨C1, (⟨H14, (⟨H15, (⟨H8, (⟨H9, (⟨H17, (⟨H18, (⟨H11, (⟨H12, (l2_11 (outer_transitivity_between2 (between_symmetry H14) (outer_transitivity_between b10 H8 b7) b6) (outer_transitivity_between2 (between_symmetry H17) (outer_transitivity_between b11 H11 b9) b8) (cong_right_commutativity (l2_11 (between_symmetry H14) H17 (cong_left_commutativity H15) (cong_symmetry (cong_right_commutativity H18)))) (cong_right_commutativity (l2_11 H8 (between_symmetry H11) (cong_symmetry (cong_left_commutativity H12)) (cong_right_commutativity H9))))⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem l11_14_c :
    ∀ (A B C A' C' : Tpoint), Bet A B A' → A ≠ B → A' ≠ B → Bet C B C' → B ≠ C → B ≠ C' → CongA A B C A' B C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  (let H5 := bet_neq12__neq b5 b6; (let H6 := bet_neq21__neq b8 b9; (let H7 := l11_13_c b0 b1 b2 b2 b1 b0 b3 b4 (conga_pseudo_refl_c b0 b1 b2 b6 (Ne.symm b9)) b5 b7 b8 (Ne.symm b10); l11_13_c b3 b1 b2 b0 b1 b4 b0 b3 (conga_right_comm_c b3 b1 b2 b4 b1 b0 H7) (between_symmetry b5) b6 b5 b7)))
theorem l11_16_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → A ≠ B → C ≠ B → Per A' B' C' → A' ≠ B' → C' ≠ B' → CongA A B C A' B' C' := sorry
theorem l11_17_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → CongA A B C A' B' C' → Per A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨A0, H9⟩ := H8
  obtain ⟨C0, H10⟩ := H9
  obtain ⟨A1, H11⟩ := H10
  obtain ⟨C1, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H20
  obtain ⟨H23, H24⟩ := H22
  obtain ⟨H25, H26⟩ := H24
  obtain ⟨H27, H28⟩ := H26
  have H29 := per_col_c A0 b1 b2 C0 (Ne.symm H3) (l8_2_c b2 b1 A0 (per_col_c b2 b1 b0 A0 (Ne.symm H1) (l8_2_c b0 b1 b2 b6) (Or.inl H13))) (Or.inl H17)
  have H30 := l8_10_c A0 b1 C0 A1 b4 C1 H29 (⟨(cong_right_commutativity (l2_11 (between_symmetry H13) H21 (cong_left_commutativity H15) (cong_symmetry (cong_right_commutativity H23)))), (⟨H28, (cong_right_commutativity (l2_11 H17 (between_symmetry H25) (cong_left_commutativity (cong_symmetry (cong_commutativity H27))) (cong_right_commutativity H19)))⟩)⟩)
  exact per_col_c b3 b4 C1 b5 ((fun H31 => (by
  subst H31
  have H34 := between_identity b4 b5 H25
  subst H34
  exact ((H7 rfl)).elim))) (l8_2_c C1 b4 b3 (per_col_c C1 b4 A1 b3 ((fun H31 => (by
  subst H31
  have H34 := between_identity b4 b3 H21
  subst H34
  exact ((H5 rfl)).elim))) (l8_2_c A1 b4 C1 H30) (Or.inr (Or.inl (between_symmetry H21))))) (Or.inr (Or.inl (between_symmetry H25)))
theorem l11_18_1_c :
    ∀ (A B C D : Tpoint), Bet C B D → B ≠ C → B ≠ D → A ≠ B → Per A B C → CongA A B C A B D :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  (let H4 := per_col_c b0 b1 b2 b3 b5 b8 (Or.inr (Or.inr (between_symmetry b4))); l11_16_c b0 b1 b2 b0 b1 b3 b8 b7 (Ne.symm b5) H4 b7 (Ne.symm b6))
theorem l11_18_2_c :
    ∀ (A B C D : Tpoint), Bet C B D → CongA A B C A B D → Per A B C := sorry
theorem cong3_preserves_out_c :
    ∀ (A B C A' B' C' : Tpoint), Out A B C → Cong_3 A B C A' B' C' → Out A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b6
  obtain ⟨H3, H4⟩ := H2
  have HH := b7
  obtain ⟨H5, H6⟩ := b7
  obtain ⟨H7, H8⟩ := H6
  exact ⟨((fun H9 => (by
  subst H9
  have H12 := cong_identity b0 b1 b4 H5
  subst H12
  exact ((H1 rfl)).elim))), (⟨((fun H9 => (by
  subst H9
  have H12 := cong_identity b0 b2 b5 H7
  subst H12
  exact ((H3 rfl)).elim))), ((by
  rcases H4 with H9 | H9
  · exact Or.inl (l4_6 H9 HH)
  · exact Or.inr (l4_6 H9 (⟨H7, (⟨H5, (cong_symmetry (cong_symmetry (cong_commutativity H8)))⟩)⟩))))⟩)⟩
theorem l11_21_a_c :
    ∀ (A B C A' B' C' : Tpoint), Out B A C → CongA A B C A' B' C' → Out B' A' C' := sorry
theorem l11_21_b_c :
    ∀ (A B C A' B' C' : Tpoint), Out B A C → Out B' A' C' → CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have sg := segment_construction b0 b1 b0 b1
  obtain ⟨A0, H1⟩ := sg
  obtain ⟨H2, H3⟩ := H1
  have sg0 := segment_construction b2 b1 b1 b2
  obtain ⟨C0, H4⟩ := sg0
  obtain ⟨H5, H6⟩ := H4
  have sg1 := segment_construction b3 b4 b3 b4
  obtain ⟨A1, H7⟩ := sg1
  obtain ⟨H8, H9⟩ := H7
  have sg2 := segment_construction b5 b4 b4 b5
  obtain ⟨C1, H10⟩ := sg2
  obtain ⟨H11, H12⟩ := H10
  exact l11_13_c C0 b1 b2 C1 b4 b5 b0 b3 (conga_line_c C0 b1 b2 C1 b4 b5 ((fun H13 => (by
  subst H13
  have H16 := cong_symmetry H6
  have H17 := cong_identity C0 b2 C0 H16
  subst H17
  obtain ⟨_, H19⟩ := b6
  obtain ⟨H20, _⟩ := H19
  exact ((H20 rfl)).elim))) ((by
  obtain ⟨_, H13⟩ := b6
  obtain ⟨H14, _⟩ := H13
  exact Ne.symm H14)) ((fun H13 => (by
  subst H13
  have H16 := cong_symmetry H12
  have H17 := cong_identity C1 b5 C1 H16
  subst H17
  obtain ⟨_, H19⟩ := b7
  obtain ⟨H20, _⟩ := H19
  exact ((H20 rfl)).elim))) ((fun H13 => (by
  obtain ⟨_, H14⟩ := b7
  obtain ⟨H15, _⟩ := H14
  exact H15 (Eq.symm H13)))) (between_symmetry H5) (between_symmetry H11)) ((by
  obtain ⟨_, H13⟩ := b6
  obtain ⟨H14, H15⟩ := H13
  rcases H15 with H16 | H16
  · exact between_inner_transitivity (between_symmetry H5) H16
  · exact outer_transitivity_between (between_symmetry H5) H16 (Ne.symm H14))) ((by
  obtain ⟨H13, H14⟩ := b6
  obtain ⟨_, _⟩ := H14
  exact H13)) ((by
  obtain ⟨_, H13⟩ := b7
  obtain ⟨H14, H15⟩ := H13
  rcases H15 with H16 | H16
  · exact between_inner_transitivity (between_symmetry H11) H16
  · exact outer_transitivity_between (between_symmetry H11) H16 (Ne.symm H14))) ((by
  obtain ⟨H13, H14⟩ := b7
  obtain ⟨_, _⟩ := H14
  exact H13))
theorem conga_cop__or_out_ts_c :
    ∀ (A B C C' : Tpoint), Coplanar A B C C' → CongA A B C A B C' → Out B C C' ∨ TS A B C C' := sorry
theorem conga_os__out_c :
    ∀ (A B C C' : Tpoint), CongA A B C A B C' → OS A B C C' → Out B C C' := sorry
theorem cong2_conga_cong_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → Cong A B A' B' → Cong B C B' C' → Cong A C A' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨_, H2⟩ := b6
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨A0, H6⟩ := H5
  obtain ⟨C0, H7⟩ := H6
  obtain ⟨A1, H8⟩ := H7
  obtain ⟨C1, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, H21⟩ := H19
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨H24, H25⟩ := H23
  have H26 := l4_2 (⟨H10, (⟨H18, (⟨(l2_11 H10 H18 (cong_commutativity b7) (cong_transitivity H12 (cong_commutativity (cong_symmetry (cong_transitivity (cong_symmetry (cong_symmetry (cong_commutativity H20))) b7))))), (⟨(cong_transitivity H12 (cong_commutativity (cong_symmetry (cong_transitivity (cong_symmetry (cong_symmetry (cong_commutativity H20))) b7)))), (⟨(cong_transitivity (l2_11 H14 H22 b8 (cong_transitivity H16 (cong_symmetry (cong_transitivity H24 b8)))) (cong_reflexivity b4 C1)), H25⟩)⟩)⟩)⟩)⟩)
  exact cong_commutativity (l4_2 (⟨H14, (⟨H22, (⟨(l2_11 H14 H22 b8 (cong_transitivity H16 (cong_transitivity (cong_symmetry b8) (cong_symmetry H24)))), (⟨(cong_transitivity H16 (cong_transitivity (cong_symmetry b8) (cong_symmetry H24))), (⟨(cong_commutativity b7), (cong_commutativity H26)⟩)⟩)⟩)⟩)⟩))
theorem angle_construction_1_c :
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ OS A' B' C' P := sorry
theorem angle_construction_2_c :
    ∀ (A B C A' B' P : Tpoint), A ≠ B → A ≠ C → B ≠ C → A' ≠ B' → ¬ Col A' B' P → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ (OS A' B' C' P ∨ Col A' B' C') := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have o := col_dec_c b0 b1 b2
  rcases o with H4 | H4
  · have o0 := out_dec_c b1 b0 b2
    rcases o0 with H5 | H5
    · exact ⟨b3, (⟨((let H6 := out2__conga_c b0 b1 b0 b0 b2 (out_trivial b6) (l6_6 H5); (let H7 := conga_trivial_1_c b0 b1 b3 b4 b6 b9; conga_sym_c b3 b4 b3 b0 b1 b2 (conga_trans_c b3 b4 b3 b0 b1 b0 b0 b1 b2 (conga_sym_c b0 b1 b0 b3 b4 b3 H7) H6)))), (Or.inr (col_trivial_3_c b3 b4))⟩)⟩
    · have H6 := not_out_bet_c b0 b1 b2 H4 H5
      have sg := segment_construction b3 b4 b3 b4
      obtain ⟨C', H3⟩ := sg
      obtain ⟨H7, H8⟩ := H3
      exact ⟨C', (⟨(conga_line_c b0 b1 b2 b3 b4 C' b6 b8 b9 ((fun H9 => (by
  subst H9
  have H12 := cong_symmetry H8
  have H13 := cong_identity b3 b4 b4 H12
  subst H13
  exact ((b9 rfl)).elim))) H6 H7), (Or.inr (Or.inl H7))⟩)⟩
  · have H5 := angle_construction_1_c b0 b1 b2 b3 b4 b5 H4 b10
    obtain ⟨C', H3⟩ := H5
    obtain ⟨H6, H7⟩ := H3
    exact ⟨C', (⟨H6, (Or.inl H7)⟩)⟩
theorem ex_conga_ts_c :
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → ∃ C' : Tpoint, CongA A B C A' B' C' ∧ TS A' B' C' P := sorry
theorem l11_15_c :
    ∀ (A B C D E P : Tpoint), ¬ Col A B C → ¬ Col D E P → ∃ (F : Tpoint), CongA A B C D E F ∧ OS E D F P ∧ (∀ (F1 F2 : Tpoint), ((CongA A B C D E F1 ∧ OS E D F1 P) ∧ (CongA A B C D E F2 ∧ OS E D F2 P)) → Out E F1 F2) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have H1 := angle_construction_1_c b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨F, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact ⟨F, (⟨H3, (⟨(invert_one_side_c b3 b4 F b5 H4), (fun F1 F2 H5 => (by
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H6
  exact conga_os__out_c b3 b4 F1 F2 (conga_trans_c b3 b4 F1 b0 b1 b2 b3 b4 F2 (conga_sym_c b0 b1 b2 b3 b4 F1 H10) H8) (invert_one_side_c b4 b3 F1 F2 (one_side_transitivity_c b4 b3 F1 b5 F2 H11 (one_side_symmetry_c b4 b3 F2 b5 H9)))))⟩)⟩)⟩
theorem l11_19_c :
    ∀ (A B P1 P2 : Tpoint), Per A B P1 → Per A B P2 → OS A B P1 P2 → Out B P1 P2 := sorry
theorem l11_22_bet_c :
    ∀ (A B C P A' B' C' P' : Tpoint), Bet A B C → TS P' B' A' C' → CongA A B P A' B' P' ∧ CongA P B C P' B' C' → Bet A' B' C' := sorry
theorem l11_22a_c :
    ∀ (A B C P A' B' C' P' : Tpoint), TS B P A C ∧ TS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := sorry
theorem l11_22b_c :
    ∀ (A B C P A' B' C' P' : Tpoint), OS B P A C ∧ OS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := sorry
theorem l11_22_c :
    ∀ (A B C P A' B' C' P' : Tpoint), ((TS B P A C ∧ TS B' P' A' C') ∨ (OS B P A C ∧ OS B' P' A' C')) ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨H0, H1⟩ := b8
  obtain ⟨H2, H3⟩ := H1
  rcases H0 with H4 | H4
  · exact l11_22a_c b0 b1 b2 b3 b4 b5 b6 b7 ((by
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H5, (⟨H6, (⟨H2, H3⟩)⟩)⟩))
  · exact l11_22b_c b0 b1 b2 b3 b4 b5 b6 b7 ((by
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H5, (⟨H6, (⟨H2, H3⟩)⟩)⟩))
theorem l11_24_c :
    ∀ (P A B C : Tpoint), InAngle P A B C → InAngle P C B A := by
  intro b0 b1 b2 b3 b4
  obtain ⟨H0, H1⟩ := b4
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨X, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  exact ⟨H2, (⟨H0, (⟨H4, (⟨X, (⟨(between_symmetry H7), H8⟩)⟩)⟩)⟩)⟩
theorem col_in_angle_c :
    ∀ (A B C P : Tpoint), A ≠ B → C ≠ B → P ≠ B → Out B A P ∨ Out B C P → InAngle P A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b7 with H3 | H3
  · exact ⟨b4, (⟨b5, (⟨b6, (⟨b0, (⟨(between_symmetry (between_trivial b2 b0)), (Or.inr H3)⟩)⟩)⟩)⟩)⟩
  · exact ⟨b4, (⟨b5, (⟨b6, (⟨b2, (⟨(between_trivial b0 b2), (Or.inr H3)⟩)⟩)⟩)⟩)⟩
theorem out321__inangle_c :
    ∀ (A B C P : Tpoint), C ≠ B → Out B A P → InAngle P A B C := by
  intro b0 b1 b2 b3 b4 b5
  have H1 := out_distinct_c b1 b0 b3 b5
  have H2 := H1
  obtain ⟨H3, H4⟩ := H2
  exact col_in_angle_c b0 b1 b2 b3 H3 b4 H4 (Or.inl b5)
theorem inangle1123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle A A B C :=
  fun b0 b1 b2 b3 b4 =>
  out321__inangle_c b0 b1 b2 b0 b4 (out_trivial b3)
theorem out341__inangle_c :
    ∀ (A B C P : Tpoint), A ≠ B → Out B C P → InAngle P A B C := by
  intro b0 b1 b2 b3 b4 b5
  have H1 := out_distinct_c b1 b2 b3 b5
  have H2 := H1
  obtain ⟨H3, H4⟩ := H2
  exact col_in_angle_c b0 b1 b2 b3 b4 H3 H4 (Or.inr b5)
theorem inangle3123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle C A B C :=
  fun b0 b1 b2 b3 b4 =>
  out341__inangle_c b0 b1 b2 b2 b3 (out_trivial b4)
theorem in_angle_two_sides_c :
    ∀ (A B C P : Tpoint), ¬ Col B A P → ¬ Col B C P → InAngle P A B C → TS P B A C := sorry
theorem in_angle_out_c :
    ∀ (A B C P : Tpoint), Out B A C → InAngle P A B C → Out B A P := sorry
theorem col_in_angle_out_c :
    ∀ (A B C P : Tpoint), Col B A P → ¬ Bet A B C → InAngle P A B C → Out B A P := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H2⟩ := b6
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨X, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  rcases H8 with H9 | H9
  · subst H9
    exact ((b5 H7)).elim
  · have o := point_equality_decidability b0 X
    rcases o with H10 | H10
    · subst H10
      exact H9
    · have H11 := not_bet_out_c b0 b1 b2 ((let H11 := col_transitivity_1_c b1 b3 b0 X (Ne.symm H4) (col_permutation_5_c b1 b0 b3 b4) (col_permutation_5_c b1 X b3 (out_col H9)); col_transitivity_2_c X b0 b1 b2 (Ne.symm H10) (col_permutation_5_c X b1 b0 (col_permutation_2_c b1 b0 X H11)) (col_permutation_4_c b0 X b2 (bet_col_c b0 X b2 H7)))) b5
      have H12 := out2_bet_out_c b0 b1 b2 X b3 H11 H9 H7
      obtain ⟨H13, _⟩ := H12
      exact H13
theorem l11_25_aux_c :
    ∀ (P A B C A' : Tpoint), InAngle P A B C → ¬ Bet A B C → Out B A' A → InAngle P A' B C := sorry
theorem l11_25_c :
    ∀ (P A B C A' C' P' : Tpoint), InAngle P A B C → Out B A' A → Out B C' C → Out B P' P → InAngle P' A' B C' := sorry
theorem inangle_distincts_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → A ≠ B ∧ C ≠ B ∧ P ≠ B := by
  intro b0 b1 b2 b3 b4
  obtain ⟨H0, H1⟩ := b4
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, _⟩ := H3
  exact ⟨H0, (⟨H2, H4⟩)⟩
theorem segment_construction_0_c :
    ∀ (A B A' : Tpoint), ∃ (B' : Tpoint), Cong A' B' A B := by
  intro b0 b1 b2
  have o := point_equality_decidability b0 b1
  rcases o with H | H
  · exact ⟨b2, ((by
  subst H
  exact cong_trivial_identity b2 b0))⟩
  · have H0 := another_point_c b2
    obtain ⟨X, H1⟩ := H0
    have HH := segment_construction_3_c b2 X b0 b1 H1 H
    obtain ⟨B', H2⟩ := HH
    obtain ⟨_, H3⟩ := H2
    exact ⟨B', H3⟩
theorem angle_construction_3_c :
    ∀ (A B C A' B' : Tpoint), A ≠ B → C ≠ B → A' ≠ B' → ∃ (C' : Tpoint), CongA A B C A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have H2 := not_col_exists_c b3 b4 b7
  obtain ⟨P, H3⟩ := H2
  have o := point_equality_decidability b0 b2
  rcases o with H4 | H4
  · subst H4
    exact ⟨b3, (conga_trivial_1_c b0 b1 b3 b4 b6 b7)⟩
  · have H5 := angle_construction_2_c b0 b1 b2 b3 b4 P b5 H4 (Ne.symm b6) b7 H3
    obtain ⟨C', H6⟩ := H5
    obtain ⟨H7, _⟩ := H6
    exact ⟨C', H7⟩
theorem l11_28_c :
    ∀ (A B C D A' B' C' : Tpoint), Cong_3 A B C A' B' C' → Col A C D → ∃ (D' : Tpoint), Cong A D A' D' ∧ Cong B D B' D' ∧ Cong C D C' D' := sorry
theorem bet_conga__bet_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A B C → CongA A B C A' B' C' → Bet A' B' C' := sorry
theorem in_angle_one_side_c :
    ∀ (A B C P : Tpoint), ¬ Col A B C → ¬ Col B A P → InAngle P A B C → OS A B P C := sorry
theorem inangle_one_side_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q := sorry
theorem inangle_one_side2_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → ¬ Col C B P → ¬ Col C B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q ∧ OS C B P Q :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
  ⟨(inangle_one_side_c b0 b1 b2 b3 b4 b5 b6 b7 b10 b11), (inangle_one_side_c b2 b1 b0 b3 b4 (not_col_permutation_5_c b2 b0 b1 (not_col_permutation_2_c b0 b1 b2 b5)) b8 b9 (l11_24_c b3 b0 b1 b2 b10) (l11_24_c b4 b0 b1 b2 b11))⟩
theorem col_conga_col_c :
    ∀ (A B C D E F : Tpoint), Col A B C → CongA A B C D E F → Col D E F := sorry
theorem ncol_conga_ncol_c :
    ∀ (A B C D E F : Tpoint), ¬ Col A B C → CongA A B C D E F → ¬ Col D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  (fun H1 => b6 (col_conga_col_c b3 b4 b5 b0 b1 b2 H1 (conga_sym_c b0 b1 b2 b3 b4 b5 b7)))
theorem angle_construction_4_c :
    ∀ (A B C A' B' P : Tpoint), A ≠ B → C ≠ B → A' ≠ B' → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ Coplanar A' B' C' P := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have o := col_dec_c b3 b4 b5
  rcases o with x | x
  · have e := angle_construction_3_c b0 b1 b2 b3 b4 b6 b7 b8
    obtain ⟨x0, x1⟩ := e
    exact ⟨x0, (⟨x1, (coplanar_perm_1_c b3 b4 b5 x0 (col__coplanar_c b3 b4 b5 x0 x))⟩)⟩
  · have o0 := col_dec_c b0 b1 b2
    rcases o0 with x0 | x0
    · have e := angle_construction_3_c b0 b1 b2 b3 b4 b6 b7 b8
      obtain ⟨x1, x2⟩ := e
      exact ⟨x1, (⟨x2, (⟨x1, (Or.inl (⟨(col_conga_col_c b0 b1 b2 b3 b4 x1 x0 x2), (col_trivial_3_c x1 b5)⟩))⟩)⟩)⟩
    · have e := angle_construction_1_c b0 b1 b2 b3 b4 b5 x0 x
      obtain ⟨x1, x2⟩ := e
      obtain ⟨x3, x4⟩ := x2
      exact ⟨x1, (⟨x3, ((let H7 := os__coplanar_c b3 b4 x1 b5 x4; H7))⟩)⟩
theorem lea_distincts_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨x, x0⟩ := b6
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x1
  obtain ⟨x5, x6⟩ := x4
  exact ⟨(conga_diff1_c b0 b1 b2 b3 b4 x x2), (⟨(conga_diff2_c b0 b1 b2 b3 b4 x x2), (⟨x3, x5⟩)⟩)⟩
theorem l11_29_a_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F := sorry
theorem in_angle_line_c :
    ∀ (A B C P : Tpoint), P ≠ B → A ≠ B → C ≠ B → Bet A B C → InAngle P A B C :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b5, (⟨b6, (⟨b4, (⟨b1, (⟨b7, (Or.inl rfl)⟩)⟩)⟩)⟩)⟩
theorem l11_29_b_c :
    ∀ (A B C D E F : Tpoint), (∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F) → LeA A B C D E F := sorry
theorem bet_in_angle_bet_c :
    ∀ (A B C P : Tpoint), Bet A B P → InAngle P A B C → Bet A B C := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨_, H1⟩ := b5
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨X, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  rcases H6 with H7 | H7
  · subst H7
    exact H5
  · obtain ⟨H8, H9⟩ := H7
    obtain ⟨H10, H11⟩ := H9
    rcases H11 with H12 | H12
    · have H13 := between_exchange2 b4 H12
      have H14 := l5_1 ((fun H14 => (by
  subst H14
  have H17 := between_equality b4 H12
  exact ((H8 H17)).elim))) H13 H5
      rcases H14 with H15 | _
      · exact between_exchange4 b4 H15
      · have H15 := between_inner_transitivity b4 H12
        exact between_exchange4 H15 H5
    · have H13 := outer_transitivity_between b4 H12 (Ne.symm H10)
      exact between_exchange4 H13 H5
theorem lea_line_c :
    ∀ (A B C P : Tpoint), Bet A B P → LeA A B P A B C → Bet A B C := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨PP, H1⟩ := b5
  obtain ⟨H2, H3⟩ := H1
  have HH := H2
  obtain ⟨_, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨X, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  rcases H9 with H10 | _
  · subst H10
    exact H8
  · have H10 := bet_conga__bet_c b0 b1 b3 b0 b1 PP b4 H3
    exact bet_in_angle_bet_c b0 b1 b2 PP H10 HH
theorem eq_conga_out_c :
    ∀ (A B D E F : Tpoint), CongA A B A D E F → Out E D F := sorry
theorem conga_ex_cong3_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → ∃ (AA : Tpoint), ∃ (CC : Tpoint), Out B A AA → Out B C CC → Cong_3 AA B CC A' B' C' := sorry
theorem conga_preserves_in_angle_c :
    ∀ (A B C I A' B' C' I' : Tpoint), CongA A B C A' B' C' → CongA A B I A' B' I' → InAngle I A B C → OS A' B' I' C' → InAngle I' A' B' C' := sorry
theorem l11_30_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), LeA A B C D E F → CongA A B C A' B' C' → CongA D E F D' E' F' → LeA A' B' C' D' E' F' := sorry
theorem l11_31_1_c :
    ∀ (A B C D E F : Tpoint), Out B A C → D ≠ E → F ≠ E → LeA A B C D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  ⟨b3, (⟨(inangle1123_c b3 b4 b5 b7 b8), (l11_21_b_c b0 b1 b2 b3 b4 b3 b6 (out_trivial b7))⟩)⟩
theorem l11_31_2_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → C ≠ B → D ≠ E → F ≠ E → Bet D E F → LeA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have e := angle_construction_3_c b0 b1 b2 b3 b4 b6 b7 b8
  obtain ⟨x, x0⟩ := e
  exact ⟨x, (⟨(in_angle_line_c b3 b4 b5 x ((by
  obtain ⟨_, H5⟩ := x0
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  exact H8)) ((by
  obtain ⟨_, H5⟩ := x0
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact H7)) ((by
  obtain ⟨_, H5⟩ := x0
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact b9)) ((by
  obtain ⟨_, H5⟩ := x0
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, _⟩ := H7
  exact b10))), ((by
  obtain ⟨H4, H5⟩ := x0
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  exact ⟨H4, (⟨H6, (⟨H8, (⟨H10, H11⟩)⟩)⟩)⟩))⟩)⟩
theorem lea_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → LeA A B C A B C :=
  fun b0 b1 b2 b3 b4 =>
  ⟨b2, (⟨(inangle3123_c b0 b1 b2 b3 b4), (conga_refl_c b0 b1 b2 b3 b4)⟩)⟩
theorem conga__lea_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA A B C D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  ⟨b5, (⟨(inangle3123_c b3 b4 b5 (conga_diff45_c b0 b1 b2 b3 b4 b5 b6) (conga_diff56_c b0 b1 b2 b3 b4 b5 b6)), b6⟩)⟩
theorem conga__lea456123_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA D E F A B C :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga__lea_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b6)
theorem lea_left_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA C B A D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨P, H0⟩ := b6
  obtain ⟨H1, H2⟩ := H0
  exact ⟨P, (⟨H1, (conga_left_comm_c b0 b1 b2 b3 b4 P H2)⟩)⟩
theorem lea_right_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA A B C F E D := by
  intro b0 b1 b2 b3 b4 b5 b6
  exact l11_29_b_c b0 b1 b2 b5 b4 b3 ((let H0 := l11_29_a_c b0 b1 b2 b3 b4 b5 b6; (by
  obtain ⟨P, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  exact ⟨P, (⟨H2, (conga_right_comm_c b0 b1 P b3 b4 b5 H3)⟩)⟩)))
theorem lea_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA C B A F E D :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  lea_left_comm_c b0 b1 b2 b5 b4 b3 (lea_right_comm_c b0 b1 b2 b3 b4 b5 b6)
theorem lta_left_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA C B A D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  exact ⟨(lea_left_comm_c b0 b1 b2 b3 b4 b5 H0), ((fun H2 => H1 (conga_left_comm_c b2 b1 b0 b3 b4 b5 H2)))⟩
theorem lta_right_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA A B C F E D := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  exact ⟨(lea_right_comm_c b0 b1 b2 b3 b4 b5 H0), ((fun H2 => H1 (conga_right_comm_c b0 b1 b2 b5 b4 b3 H2)))⟩
theorem lta_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA C B A F E D :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  lta_left_comm_c b0 b1 b2 b5 b4 b3 (lta_right_comm_c b0 b1 b2 b3 b4 b5 b6)
theorem lea_out4__lea_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), LeA A B C D E F → Out B A A' → Out B C C' → Out E D D' → Out E F F' → LeA A' B C' D' E F' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 =>
  l11_30_c b0 b1 b2 b3 b4 b5 b6 b1 b7 b8 b4 b9 b10 (out2__conga_c b0 b1 b2 b6 b7 (l6_6 b11) (l6_6 b12)) (out2__conga_c b3 b4 b5 b8 b9 (l6_6 b13) (l6_6 b14))
theorem lea121345_c :
    ∀ (A B C D E : Tpoint), A ≠ B → C ≠ D → D ≠ E → LeA A B A C D E := sorry
theorem inangle__lea_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA A B P A B C := by
  intro b0 b1 b2 b3 b4
  exact ⟨b3, (⟨b4, ((by
  obtain ⟨H, H0⟩ := b4
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, _⟩ := H1
  exact conga_refl_c b0 b1 b3 H H2))⟩)⟩
theorem inangle__lea_1_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA P B C A B C :=
  fun b0 b1 b2 b3 b4 =>
  lea_comm_c b2 b1 b3 b2 b1 b0 (inangle__lea_c b2 b1 b0 b3 (l11_24_c b3 b0 b1 b2 b4))
theorem inangle__lta_c :
    ∀ (A B C P : Tpoint), ¬ Col P B C → InAngle P A B C → LtA A B P A B C := sorry
theorem in_angle_trans_c :
    ∀ (A B C D E : Tpoint), InAngle C A B D → InAngle D A B E → InAngle C A B E := sorry
theorem lea_trans_c :
    ∀ (A B C A1 B1 C1 A2 B2 C2 : Tpoint), LeA A B C A1 B1 C1 → LeA A1 B1 C1 A2 B2 C2 → LeA A B C A2 B2 C2 := sorry
theorem in_angle_asym_c :
    ∀ (A B C D : Tpoint), InAngle D A B C → InAngle C A B D → CongA A B C A B D := sorry
theorem lea_asym_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA D E F A B C → CongA A B C D E F := sorry
theorem col_lta__bet_c :
    ∀ (A B C X Y Z : Tpoint), Col X Y Z → LtA A B C X Y Z → Bet X Y Z := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨x, x0⟩ := b7
  have Hd := x
  exact not_out_bet_c b3 b4 b5 b6 ((fun H3 => x0 (lea_asym_c b0 b1 b2 b3 b4 b5 Hd ((let H4 := lea_distincts_c b0 b1 b2 b3 b4 b5 x; (by
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact l11_31_1_c b3 b4 b5 b0 b1 b2 H3 H5 H7))))))
theorem col_lta__out_c :
    ∀ (A B C X Y Z : Tpoint), Col A B C → LtA A B C X Y Z → Out B A C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  exact not_bet_out_c b0 b1 b2 b6 ((fun H1 => (by
  obtain ⟨x, x0⟩ := b7
  exact x0 (lea_asym_c b0 b1 b2 b3 b4 b5 x ((let H4 := lea_distincts_c b0 b1 b2 b3 b4 b5 x; (by
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  exact l11_31_2_c b3 b4 b5 b0 b1 b2 H9 H10 H5 H7 H1)))))))
theorem lta_distincts_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ D ≠ F := by
  intro b0 b1 b2 b3 b4 b5 b6
  have Hlea := (by
  obtain ⟨x, x0⟩ := b6
  exact x)
  have Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 Hlea
  obtain ⟨H, H0⟩ := Hlea0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  exact ⟨H, (⟨H1, (⟨H3, (⟨H4, ((fun H5 => (by
  subst H5
  have H7 := col_lta__bet_c b0 b1 b2 b3 b4 b3 (col_trivial_3_c b3 b4) b6
  have H8 := between_identity b3 b4 H7
  subst H8
  exact H4 rfl)))⟩)⟩)⟩)⟩
theorem gta_distincts_c :
    ∀ (A B C D E F : Tpoint), GtA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ A ≠ C := by
  intro b0 b1 b2 b3 b4 b5 b6
  have Hgta0 := lta_distincts_c b3 b4 b5 b0 b1 b2 b6
  obtain ⟨H, H0⟩ := Hgta0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H3, (⟨H5, (⟨H, (⟨H1, H6⟩)⟩)⟩)⟩
theorem acute_distincts_c :
    ∀ (A B C : Tpoint), Acute A B C → A ≠ B ∧ C ≠ B := by
  intro b0 b1 b2 b3
  obtain ⟨x, x0⟩ := b3
  obtain ⟨x2, x3⟩ := x0
  obtain ⟨x4, x5⟩ := x3
  obtain ⟨x6, x7⟩ := x5
  have Hlta0 := lta_distincts_c b0 b1 b2 x x2 x4 x7
  obtain ⟨H2, H3⟩ := Hlta0
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, _⟩ := H6
  exact ⟨H2, H4⟩
theorem obtuse_distincts_c :
    ∀ (A B C : Tpoint), Obtuse A B C → A ≠ B ∧ C ≠ B ∧ A ≠ C := by
  intro b0 b1 b2 b3
  obtain ⟨x, x0⟩ := b3
  obtain ⟨x2, x3⟩ := x0
  obtain ⟨x4, x5⟩ := x3
  obtain ⟨x6, x7⟩ := x5
  have Hgta0 := gta_distincts_c b0 b1 b2 x x2 x4 x7
  obtain ⟨H2, H3⟩ := Hgta0
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  exact ⟨H2, (⟨H4, H7⟩)⟩
theorem two_sides_in_angle_c :
    ∀ (A B C P P' : Tpoint), B ≠ P' → TS B P A C → Bet P B P' → InAngle P A B C ∨ InAngle P' A B C := sorry
theorem in_angle_reverse_c :
    ∀ (A B A' C D : Tpoint), A' ≠ B → Bet A B A' → InAngle C A B D → InAngle D A' B C := sorry
theorem in_angle_trans2_c :
    ∀ (A B C D E : Tpoint), InAngle C A B D → InAngle D A B E → InAngle D C B E := by
  intro b0 b1 b2 b3 b4 b5 b6
  have e := segment_construction b4 b1 b4 b1
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  have Hd := b6
  have Hd0 := inangle_distincts_c b0 b1 b4 b3 Hd
  obtain ⟨_, H0⟩ := Hd0
  obtain ⟨H1, _⟩ := H0
  have H2 := bet_neq12__neq x1 H1
  have H3 := cong_diff_3_c b1 x b4 b1 H1 x2
  exact l11_24_c b3 b4 b1 b2 (in_angle_reverse_c x b1 b4 b2 b3 H1 (between_symmetry x1) (l11_24_c b2 b3 b1 x (in_angle_trans_c b3 b1 b2 b0 x (l11_24_c b2 b0 b1 b3 b5) (l11_24_c b0 x b1 b3 (in_angle_reverse_c b4 b1 x b3 b0 (Ne.symm H3) x1 (l11_24_c b3 b0 b1 b4 b6))))))
theorem l11_36_c :
    ∀ (A B C D E F A' D' : Tpoint), A ≠ B → A' ≠ B → D ≠ E → D' ≠ E → Bet A B A' → Bet D E D' → (LeA A B C D E F ↔ LeA D' E F A' B C) := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  exact ⟨(fun H5 => (let HH := H5; (let H6 := l11_29_a_c b0 b1 b2 b3 b4 b5 H5; (by
  obtain ⟨P, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  exact ⟨P, (⟨(in_angle_reverse_c b0 b1 b6 b2 P b9 b12 H8), (l11_13_c b3 b4 b5 b0 b1 P b7 b6 (conga_sym_c b0 b1 P b3 b4 b5 H9) b13 b11 b12 b9)⟩)⟩)))), (fun H5 => (let HH := H5; l11_29_b_c b0 b1 b2 b3 b4 b5 ((by
  obtain ⟨P, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  exact ⟨P, (⟨(in_angle_reverse_c b6 b1 b0 P b2 b8 (between_symmetry b12) H7), (l11_13_c b6 b1 P b7 b4 b5 b0 b3 (conga_sym_c b7 b4 b5 b6 b1 P H8) (between_symmetry b12) b8 (between_symmetry b13) b10)⟩)⟩))))⟩
theorem l11_41_aux_c :
    ∀ (A B C D : Tpoint), ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D := sorry
theorem l11_41_c :
    ∀ (A B C D : Tpoint), ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D ∧ LtA A B C C A D := by
  intro b0 b1 b2 b3 b4 b5 b6
  exact ⟨(l11_41_aux_c b0 b1 b2 b3 b4 b5 b6), ((let sg := segment_construction b2 b0 b2 b0; (by
  obtain ⟨E, H2⟩ := sg
  obtain ⟨H3, H4⟩ := H2
  have H5 := l11_41_aux_c b0 b2 b1 E ((fun H5 => b4 (col_permutation_5_c b0 b2 b1 H5))) H3 ((let H5 := not_col_distincts_c b0 b1 b2 b4; (let H6 := H5; (by
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  have H11 := bet_neq21__neq H3 H10
  have H12 := bet_neq21__neq b5 H8
  have H13 := cong_diff_4_c b0 E b2 b0 H10 H4
  exact H13))))
  have H6 := conga_left_comm_c b2 b0 b1 b2 b0 b1 (conga_refl_c b2 b0 b1 ((let H6 := not_col_distincts_c b0 b1 b2 b4; (let H7 := H6; (by
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  have H12 := bet_neq21__neq H3 H11
  have H13 := bet_neq21__neq b5 H9
  have H14 := cong_diff_4_c b0 E b2 b0 H11 H4
  exact Ne.symm H11)))) ((let H6 := not_col_distincts_c b0 b1 b2 b4; (let H7 := H6; (by
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  have H12 := bet_neq21__neq H3 H11
  have H13 := bet_neq21__neq b5 H9
  have H14 := cong_diff_4_c b0 E b2 b0 H11 H4
  exact Ne.symm H9)))))
  have H7 := l11_13_c b1 b0 b2 b2 b0 b1 b3 E ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21__neq H3 H12
  have H14 := bet_neq21__neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact H6)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21__neq H3 H12
  have H14 := bet_neq21__neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact b5)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21__neq H3 H12
  have H14 := bet_neq21__neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact Ne.symm b6)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21__neq H3 H12
  have H14 := bet_neq21__neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact H3)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21__neq H3 H12
  have H14 := bet_neq21__neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact Ne.symm H15))))
  obtain ⟨H8, H9⟩ := H5
  exact ⟨(l11_30_c b0 b1 b2 b1 b0 E b0 b1 b2 b2 b0 b3 H8 (conga_refl_c b0 b1 b2 ((let H10 := not_col_distincts_c b0 b1 b2 b4; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨_, H15⟩ := H14
  have H16 := bet_neq21__neq H3 H15
  have H17 := bet_neq21__neq b5 H13
  have H18 := cong_diff_4_c b0 E b2 b0 H15 H4
  exact H13)))) ((let H10 := not_col_distincts_c b0 b1 b2 b4; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  have H17 := bet_neq21__neq H3 H16
  have H18 := bet_neq21__neq b5 H13
  have H19 := cong_diff_4_c b0 E b2 b0 H16 H4
  exact Ne.symm H15))))) (conga_sym_c b2 b0 b3 b1 b0 E (conga_comm_c b3 b0 b2 E b0 b1 H7))), ((fun H10 => H9 (conga_trans_c b0 b1 b2 b2 b0 b3 b1 b0 E H10 (conga_comm_c b3 b0 b2 E b0 b1 H7))))⟩)))⟩
theorem not_conga_c :
    ∀ (A B C A' B' C' D E F : Tpoint), CongA A B C A' B' C' → ¬ CongA A B C D E F → ¬ CongA A' B' C' D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  (fun H1 => b10 (conga_trans_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 H1))
theorem not_conga_sym_c :
    ∀ (A B C D E F : Tpoint), ¬ CongA A B C D E F → ¬ CongA D E F A B C :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  (fun H0 => b6 (conga_sym_c b3 b4 b5 b0 b1 b2 H0))
theorem not_and_lta_c :
    ∀ (A B C D E F : Tpoint), ¬ (LtA A B C D E F ∧ LtA D E F A B C) := by
  intro b0 b1 b2 b3 b4 b5
  intro H
  obtain ⟨H0, H1⟩ := H
  obtain ⟨H2, _⟩ := H1
  obtain ⟨H3, H4⟩ := H0
  have H5 := lea_asym_c b0 b1 b2 b3 b4 b5 H3 H2
  exact ((H4 H5)).elim
theorem conga_preserves_lta_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), CongA A B C A' B' C' → CongA D E F D' E' F' → LtA A B C D E F → LtA A' B' C' D' E' F' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  obtain ⟨H2, H3⟩ := b14
  exact ⟨(l11_30_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 H2 b12 b13), ((fun H4 => H3 (conga_trans_c b0 b1 b2 b6 b7 b8 b3 b4 b5 b12 (conga_trans_c b6 b7 b8 b9 b10 b11 b3 b4 b5 H4 (conga_sym_c b3 b4 b5 b9 b10 b11 b13)))))⟩
theorem lta_trans_c :
    ∀ (A B C A1 B1 C1 A2 B2 C2 : Tpoint), LtA A B C A1 B1 C1 → LtA A1 B1 C1 A2 B2 C2 → LtA A B C A2 B2 C2 := sorry
theorem obtuse_sym_c :
    ∀ (A B C : Tpoint), Obtuse A B C → Obtuse C B A := by
  intro b0 b1 b2 b3
  obtain ⟨A', H0⟩ := b3
  obtain ⟨B', H1⟩ := H0
  obtain ⟨C', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact ⟨A', (⟨B', (⟨C', (⟨H3, (lta_right_comm_c A' B' C' b0 b1 b2 H4)⟩)⟩)⟩)⟩
theorem acute_sym_c :
    ∀ (A B C : Tpoint), Acute A B C → Acute C B A := by
  intro b0 b1 b2 b3
  obtain ⟨A', H0⟩ := b3
  obtain ⟨B', H1⟩ := H0
  obtain ⟨C', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact ⟨A', (⟨B', (⟨C', (⟨H3, (lta_left_comm_c b0 b1 b2 A' B' C' H4)⟩)⟩)⟩)⟩
theorem acute_col__out_c :
    ∀ (A B C : Tpoint), Col A B C → Acute A B C → Out B A C := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact col_lta__out_c b0 b1 b2 x x1 x3 b3 x6
theorem col_obtuse__bet_c :
    ∀ (A B C : Tpoint), Col A B C → Obtuse A B C → Bet A B C := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact col_lta__bet_c x x1 x3 b0 b1 b2 b3 x6
theorem out__acute_c :
    ∀ (A B C : Tpoint), Out B A C → Acute A B C := by
  intro b0 b1 b2 b3
  have H := out_distinct_c b1 b0 b2 b3
  have H0 := H
  obtain ⟨H1, _⟩ := H0
  have HD := perp_exists_c b1 b0 b1
  have e := HD H1
  obtain ⟨x, x0⟩ := e
  have H3 := perp_distinct_c b1 x b0 b1 x0
  have H4 := H3
  obtain ⟨H5, _⟩ := H4
  exact ⟨b0, (⟨b1, (⟨x, (⟨(perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))), (⟨(l11_31_1_c b0 b1 b2 b0 b1 x b3 H1 (Ne.symm H5)), ((fun H6 => (let HNCol := per_not_col_c b0 b1 x H1 H5 (perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))); HNCol (col_permutation_4_c b1 b0 x (out_col (l11_21_a_c b0 b1 b2 b0 b1 x b3 H6))))))⟩)⟩)⟩)⟩)⟩
theorem bet__obtuse_c :
    ∀ (A B C : Tpoint), Bet A B C → A ≠ B → B ≠ C → Obtuse A B C := by
  intro b0 b1 b2 b3 b4 b5
  have HD := perp_exists_c b1 b0 b1
  have e := HD b4
  obtain ⟨x, x0⟩ := e
  have H0 := bet_neq12__neq b3 b4
  have H1 := perp_distinct_c b1 x b0 b1 x0
  have H2 := H1
  obtain ⟨H3, _⟩ := H2
  exact ⟨b0, (⟨b1, (⟨x, (⟨(perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))), (⟨(l11_31_2_c b0 b1 x b0 b1 b2 b4 (Ne.symm H3) b4 (Ne.symm b5) b3), ((fun H4 => (let HNCol := per_not_col_c b0 b1 x b4 H3 (perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))); HNCol (bet_col_c b0 b1 x (bet_conga__bet_c b0 b1 b2 b0 b1 x b3 (conga_sym_c b0 b1 x b0 b1 b2 H4))))))⟩)⟩)⟩)⟩)⟩
theorem l11_43_aux_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → (Per B A C ∨ Obtuse B A C) → Acute A B C := sorry
theorem l11_43_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → (Per B A C ∨ Obtuse B A C) → Acute A B C ∧ Acute A C B := by
  intro b0 b1 b2 b3 b4 b5
  exact ⟨(l11_43_aux_c b0 b1 b2 b3 b4 b5), (l11_43_aux_c b0 b2 b1 b4 b3 ((by
  rcases b5 with H2 | H2
  · exact Or.inl (perp_in_per_c b2 b0 b1 (perp_in_sym_c b0 b1 b2 b0 b0 (perp_in_comm_c b1 b0 b0 b2 b0 (per_perp_in_c b1 b0 b2 (Ne.symm b3) b4 H2))))
  · exact Or.inr (obtuse_sym_c b1 b0 b2 H2))))⟩
theorem acute_lea_acute_c :
    ∀ (A B C D E F : Tpoint), Acute D E F → LeA A B C D E F → Acute A B C := sorry
theorem lea_obtuse_obtuse_c :
    ∀ (A B C D E F : Tpoint), Obtuse D E F → LeA D E F A B C → Obtuse A B C := sorry
theorem l11_44_1_a_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → Cong B A B C → CongA B A C B C A := by
  intro b0 b1 b2 b3 b4 b5
  have e := midpoint_existence_c b0 b2
  obtain ⟨x, x0⟩ := e
  have H2 := cong_diff_2_c b1 b0 b1 b2 b3 b5
  have H3 := midpoint_distinct_1_c x b0 b2 b4 x0
  have H4 := H3
  obtain ⟨H5, _⟩ := H4
  have H6 := cong3_conga_c b1 b0 x b1 b2 x (Ne.symm b3) H5 (⟨b5, (⟨(cong_reflexivity b1 x), (cong_symmetry (cong_4312_c b0 x x b2 (midpoint_cong_c b0 x b2 x0)))⟩)⟩)
  exact l11_10_c b1 b0 x b1 b2 x b1 b2 b1 b0 H6 (l6_6 (l6_6 (out_trivial (Ne.symm b3)))) (l6_6 (midpoint_out_c b0 x b2 b4 x0)) (l6_6 (l6_6 (out_trivial H2))) (l6_6 (l6_6 (midpoint_out_1_c b0 x b2 b4 x0)))
theorem l11_44_2_a_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → Lt B A B C → LtA B C A B A C := sorry
theorem not_lta_and_conga_c :
    ∀ (A B C D E F : Tpoint), ¬ (LtA A B C D E F ∧ CongA A B C D E F) := by
  intro b0 b1 b2 b3 b4 b5
  intro H
  obtain ⟨H0, H1⟩ := H
  obtain ⟨_, H2⟩ := H0
  exact ((H2 H1)).elim
theorem conga_sym_equiv_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' ↔ CongA A' B' C' A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  ⟨(conga_sym_c b0 b1 b2 b3 b4 b5), (conga_sym_c b3 b4 b5 b0 b1 b2)⟩
theorem conga_dec_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F ∨ ¬ CongA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b0 b1
  rcases o with H | H
  · subst H
    exact Or.inr ((fun H0 => (by
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, _⟩ := H4
  have H5 := (let H5 := rfl; H1 H5)
  exact (H5).elim)))
  · have o0 := point_equality_decidability b2 b1
    rcases o0 with H0 | H0
    · subst H0
      exact Or.inr ((fun H1 => (by
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, _⟩ := H5
  have H6 := (let H6 := rfl; H3 H6)
  exact (H6).elim)))
    · have o1 := point_equality_decidability b3 b4
      rcases o1 with H1 | H1
      · subst H1
        exact Or.inr ((fun H2 => (by
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, _⟩ := H6
  have H7 := (let H7 := rfl; H5 H7)
  exact (H7).elim)))
      · have o2 := point_equality_decidability b5 b4
        rcases o2 with H2 | H2
        · subst H2
          exact Or.inr ((fun H3 => (by
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, _⟩ := H6
  have H8 := (let H8 := rfl; H7 H8)
  exact (H8).elim)))
        · have H3 := segment_construction b1 b0 b4 b3
          have H4 := H3
          obtain ⟨x, H5⟩ := H4
          obtain ⟨H6, H7⟩ := H5
          have H8 := segment_construction b1 b2 b4 b5
          have H9 := H8
          obtain ⟨x0, H10⟩ := H9
          obtain ⟨H11, H12⟩ := H10
          have H13 := segment_construction b4 b3 b1 b0
          have H14 := H13
          obtain ⟨x1, H15⟩ := H14
          obtain ⟨H16, H17⟩ := H15
          have H18 := segment_construction b4 b5 b1 b2
          have H19 := H18
          obtain ⟨x2, H20⟩ := H19
          obtain ⟨H21, H22⟩ := H20
          have o3 := cong_dec_c x x0 x1 x2
          rcases o3 with H23 | H23
          · exact Or.inl (⟨H, (⟨H0, (⟨H1, (⟨H2, (⟨x, (⟨x0, (⟨x1, (⟨x2, (⟨H6, (⟨H7, (⟨H11, (⟨H12, (⟨H16, (⟨H17, (⟨H21, (⟨H22, H23⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
          · exact Or.inr (((fun H24 => (let H25 := H24; (by
  obtain ⟨H26, H27⟩ := H25
  obtain ⟨H28, H29⟩ := H27
  obtain ⟨H30, H31⟩ := H29
  obtain ⟨H32, H33⟩ := H31
  obtain ⟨x3, H34⟩ := H33
  obtain ⟨x4, H35⟩ := H34
  obtain ⟨x5, H36⟩ := H35
  obtain ⟨x6, H37⟩ := H36
  obtain ⟨H38, H39⟩ := H37
  obtain ⟨H40, H41⟩ := H39
  obtain ⟨H42, H43⟩ := H41
  obtain ⟨H44, H45⟩ := H43
  obtain ⟨H46, H47⟩ := H45
  obtain ⟨H48, H49⟩ := H47
  obtain ⟨H50, H51⟩ := H49
  obtain ⟨H52, H53⟩ := H51
  have H54 := construction_uniqueness (Ne.symm H26) H38 H40 H6 H7
  have H55 := construction_uniqueness (Ne.symm H28) H42 H44 H11 H12
  have H56 := construction_uniqueness (Ne.symm H30) H46 H48 H16 H17
  have H57 := construction_uniqueness (Ne.symm H32) H50 H52 H21 H22
  subst H54
  subst H55
  subst H56
  subst H57
  exact ((H23 H53)).elim)))))
theorem lta_not_conga_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → ¬ CongA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro H0
  obtain ⟨_, H1⟩ := b6
  exact ((H1 H0)).elim
theorem lta__lea_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LeA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨x, x0⟩ := b6
  exact x
theorem nlta_c :
    ∀ (A B C : Tpoint), ¬ LtA A B C A B C := sorry
theorem lea__nlta_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ¬ LtA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro Hlta
  obtain ⟨x, x0⟩ := Hlta
  exact x0 (lea_asym_c b3 b4 b5 b0 b1 b2 x b6)
theorem lta__nlea_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → ¬ LeA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨x, x0⟩ := b6
  intro H
  exact x0 (lea_asym_c b0 b1 b2 b3 b4 b5 x H)
theorem l11_44_1_b_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → CongA B A C B C A → Cong B A B C := by
  intro b0 b1 b2 b3 b4
  have H1 := not_col_distincts_c b0 b1 b2 b3
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, _⟩ := H4
  have HH := or_lt_cong_gt_c b1 b0 b1 b2
  rcases HH with H5 | H5
  · have H6 := l11_44_2_a_c b0 b1 b2 H2 H5
    have H7 := lta_not_conga_c b1 b2 b0 b1 b0 b2 H6
    have H8 := conga_sym_c b1 b0 b2 b1 b2 b0 b4
    exact ((H7 H8)).elim
  · rcases H5 with H6 | H6
    · have H7 := l11_44_2_a_c b2 b1 b0 ((fun H7 => H2 (col_permutation_3_c b2 b1 b0 H7))) H6
      have H8 := lta_not_conga_c b1 b0 b2 b1 b2 b0 H7
      exact ((H8 b4)).elim
    · exact H6
theorem l11_44_2_b_c :
    ∀ (A B C : Tpoint), LtA B A C B C A → Lt B C B A := by
  intro b0 b1 b2 b3
  have o := col_dec_c b0 b1 b2
  rcases o with H0 | H0
  · have Hd := b3
    have Hd0 := lta_distincts_c b1 b0 b2 b1 b2 b0 Hd
    obtain ⟨_, H2⟩ := Hd0
    obtain ⟨H3, H4⟩ := H2
    obtain ⟨_, H5⟩ := H4
    obtain ⟨_, _⟩ := H5
    have H1 := col_lta__bet_c b1 b0 b2 b1 b2 b0 (col_permutation_5_c b1 b0 b2 (col_permutation_4_c b0 b1 b2 H0)) b3
    exact lt_left_comm_c b2 b1 b1 b0 (lt_left_comm_c b1 b2 b1 b0 (bet__lt1213_c b1 b2 b0 H3 H1))
  · have H1 := not_col_distincts_c b0 b1 b2 H0
    obtain ⟨H2, H3⟩ := H1
    obtain ⟨H4, H5⟩ := H3
    obtain ⟨_, H6⟩ := H5
    have HH := or_lt_cong_gt_c b1 b0 b1 b2
    rcases HH with H7 | H7
    · have H8 := l11_44_2_a_c b0 b1 b2 H2 H7
      have HH0 := not_and_lta_c b1 b0 b2 b1 b2 b0
      exact ((HH0 (⟨b3, H8⟩))).elim
    · rcases H7 with H8 | H8
      · exact H8
      · have H9 := l11_44_1_a_c b0 b1 b2 H4 H6 H8
        have H10 := lta_not_conga_c b1 b0 b2 b1 b2 b0 b3
        exact ((H10 H9)).elim
theorem l11_44_1_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → (CongA B A C B C A ↔ Cong B A B C) := by
  intro b0 b1 b2 b3
  have H0 := not_col_distincts_c b0 b1 b2 b3
  have H1 := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  exact ⟨(fun H6 => l11_44_1_b_c b0 b1 b2 b3 H6), (fun H6 => l11_44_1_a_c b0 b1 b2 H3 H5 H6)⟩
theorem l11_44_2_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → (LtA B A C B C A ↔ Lt B C B A) :=
  fun b0 b1 b2 b3 =>
  ⟨(fun H0 => l11_44_2_b_c b0 b1 b2 H0), (fun H0 => l11_44_2_a_c b2 b1 b0 ((fun H1 => b3 (col_permutation_3_c b2 b1 b0 H1))) H0)⟩
theorem l11_44_2bis_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → (LeA B A C B C A ↔ Le B C B A) := sorry
theorem l11_46_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → (Per A B C ∨ Obtuse A B C) → Lt B A A C ∧ Lt B C A C := sorry
theorem l11_47_c :
    ∀ (A B C H : Tpoint), Per A C B → Perp_at H C H A B → Bet A H B ∧ A ≠ H ∧ B ≠ H := sorry
theorem l11_49_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → Cong B A B' A' → Cong B C B' C' → Cong A C A' C' ∧ (A ≠ C → CongA B A C B' A' C' ∧ CongA B C A B' C' A') := sorry
theorem l11_50_1_c :
    ∀ (A B C A' B' C' : Tpoint), ¬ Col A B C → CongA B A C B' A' C' → CongA A B C A' B' C' → Cong A B A' B' → Cong A C A' C' ∧ Cong B C B' C' ∧ CongA A C B A' C' B' := sorry
theorem l11_50_2_c :
    ∀ (A B C A' B' C' : Tpoint), ¬ Col A B C → CongA B C A B' C' A' → CongA A B C A' B' C' → Cong A B A' B' → Cong A C A' C' ∧ Cong B C B' C' ∧ CongA C A B C' A' B' := sorry
theorem l11_51_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → A ≠ C → B ≠ C → Cong A B A' B' → Cong A C A' C' → Cong B C B' C' → CongA B A C B' A' C' ∧ CongA A B C A' B' C' ∧ CongA B C A B' C' A' := sorry
theorem conga_distinct_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA A B C D E F ∧ A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := by
  intro b0 b1 b2 b3 b4 b5 b6
  exact ⟨b6, ((by
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, _⟩ := H5
  exact ⟨H0, (⟨H2, (⟨H4, H6⟩)⟩)⟩))⟩
theorem l11_52_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → Cong A C A' C' → Cong B C B' C' → Le B C A C → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry
theorem l11_53_c :
    ∀ (A B C D : Tpoint), Per D C B → C ≠ D → A ≠ B → B ≠ C → Bet A B C → LtA C A D C B D ∧ Lt B D A D := sorry
theorem cong2_conga_obtuse__cong_conga2_c :
    ∀ (A B C A' B' C' : Tpoint), Obtuse A B C → CongA A B C A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry
theorem cong2_per2__cong_conga2_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → B ≠ C → Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have H5 := cong_diff b7 b11
  have H6 := per_distinct_c b0 b1 b2 b8 b6
  have H7 := cong_diff H6 b10
  have a := l11_46_c b0 b1 b2 b6 b7 (Or.inl b8)
  obtain ⟨x, x0⟩ := a
  obtain ⟨x1, x2⟩ := x0
  exact l11_52_c b0 b1 b2 b3 b4 b5 (l11_16_c b0 b1 b2 b3 b4 b5 b8 b6 (Ne.symm b7) b9 ((fun H11 => (by
  subst H11
  exact x2 (cong_transitivity b11 (cong_symmetry b10))))) (Ne.symm H5)) b10 b11 x1
theorem cong2_per2__cong_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' := sorry
theorem cong2_per2__cong_3_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong_3 A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ((let H3 := cong2_per2__cong_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; ⟨(cong_symmetry (cong_symmetry (cong_commutativity H3))), (⟨b8, b9⟩)⟩))
theorem cong_lt_per2__lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry
theorem cong_le_per2__le_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Le B C B' C' → Le A C A' C' := sorry
theorem lt2_per2__lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Lt A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry
theorem le_lt_per2__lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Le A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry
theorem le2_per2__le_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Le A B A' B' → Le B C B' C' → Le A C A' C' := sorry
theorem cong_lt_per2__lt_1_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Lt A B A' B' → Cong A C A' C' → Lt B' C' B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  exact nle__lt_c b1 b2 b4 b5 ((fun H3 => (let l := le_lt_per2__lt_c b2 b1 b0 b5 b4 b3 (l8_2_c b0 b1 b2 b6) (l8_2_c b3 b4 b5 b7) (le_comm_c b1 b2 b4 b5 H3) (lt_left_comm_c b0 b1 b4 b3 (lt_left_comm_c b1 b0 b4 b3 (lt_left_comm_c b0 b1 b4 b3 (lt_right_comm_c b0 b1 b3 b4 b8)))); (by
  obtain ⟨x, x0⟩ := l
  exact x0 (le_anti_symmetry_c b2 b0 b5 b3 x (le_comm_c b3 b5 b0 b2 (cong__le3412_c b0 b2 b3 b5 b9)))))))
theorem symmetry_preserves_conga_c :
    ∀ (A B C A' B' C' M : Tpoint), A ≠ B → C ≠ B → Midpoint M A A' → Midpoint M B B' → Midpoint M C C' → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
  (let H4 := l7_13_c b6 b0 b1 b3 b4 (l7_2_c b6 b0 b3 b9) (l7_2_c b6 b1 b4 b10); (let H5 := l7_13_c b6 b1 b2 b4 b5 (l7_2_c b6 b1 b4 b10) (l7_2_c b6 b2 b5 b11); (let H6 := l7_13_c b6 b0 b2 b3 b5 (l7_2_c b6 b0 b3 b9) (l7_2_c b6 b2 b5 b11); cong3_conga_c b0 b1 b2 b3 b4 b5 b7 b8 (⟨H4, (⟨H6, H5⟩)⟩))))
theorem l11_57_c :
    ∀ (A B C A' B' C' : Tpoint), OS A A' B B' → Per B A A' → Per B' A' A → OS A A' C C' → Per C A A' → Per C' A' A → CongA B A C B' A' C' := sorry
theorem cop3_orth_at__orth_at_c :
    ∀ (A B C D E F U V X : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth_at X A B C U V → Orth_at X D E F U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  obtain ⟨x, x0⟩ := b13
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨b9, (⟨x1, (⟨(coplanar_pseudo_trans_c b3 b4 b5 b8 b0 b1 b2 x b10 b11 b12 x3), (⟨x5, ((let HCop := fun M => coplanar_pseudo_trans_c b3 b4 b5 M b0 b1 b2 x b10 b11 b12; (let H3 := fun M => coplanar_pseudo_trans_c b0 b1 b2 M b3 b4 b5 b9 (HCop b0 (coplanar_perm_23_c b0 b2 b1 b0 (coplanar_perm_23_c b0 b1 b2 b0 (coplanar_perm_11_c b0 b0 b2 b1 (coplanar_trivial_c b0 b2 b1))))) (HCop b1 (coplanar_perm_23_c b1 b2 b1 b0 (coplanar_perm_23_c b0 b1 b2 b1 (coplanar_perm_21_c b1 b1 b2 b0 (coplanar_trivial_c b1 b2 b0))))) (HCop b2 (coplanar_perm_23_c b2 b2 b1 b0 (coplanar_trivial_c b2 b1 b0))); fun P Q H4 H5 => x6 P Q (H3 P H4) H5)))⟩)⟩)⟩)⟩
theorem col2_orth_at__orth_at_c :
    ∀ (A B C P Q U V X : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth_at X A B C P Q → Orth_at X A B C U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨x, x0⟩ := b11
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨x, (⟨b8, (⟨x3, (⟨(col3_c b3 b4 b5 b6 b7 x1 b9 b10 x5), (fun D W HD HW => x6 D W HD (colx_c b5 b6 W b3 b4 b8 b9 b10 HW))⟩)⟩)⟩)⟩
theorem col_orth_at__orth_at_c :
    ∀ (A B C U V W X : Tpoint), U ≠ W → Col U V W → Orth_at X A B C U V → Orth_at X A B C U W :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  col2_orth_at__orth_at_c b0 b1 b2 b3 b4 b3 b5 b6 b7 (col_trivial_3_c b3 b4) b8 b9
theorem orth_at_symmetry_c :
    ∀ (A B C U V X : Tpoint), Orth_at X A B C U V → Orth_at X A B C V U := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H, H0⟩ := b6
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H, (⟨(Ne.symm H1), (⟨H3, (⟨(col_permutation_5_c b4 b5 b3 (col_permutation_1_c b3 b4 b5 H5)), (fun P Q H7 H8 => H6 P Q H7 (col_permutation_4_c b4 b3 Q H8))⟩)⟩)⟩)⟩
theorem orth_at_distincts_c :
    ∀ (A B C U V X : Tpoint), Orth_at X A B C U V → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ U ≠ V := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, _⟩ := H4
  have H5 := not_col_distincts_c b0 b1 b2 H0
  have H6 := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  exact ⟨H8, (⟨H10, (⟨H11, H2⟩)⟩)⟩
theorem orth_at_chara_c :
    ∀ (A B C P X : Tpoint), Orth_at X A B C X P ↔ ¬ Col A B C ∧ X ≠ P ∧ Coplanar A B C X ∧ (∀ (D : Tpoint), Coplanar A B C D → Per D X P) := by
  intro b0 b1 b2 b3 b4
  exact ⟨((fun H => (by
  obtain ⟨H0, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, H6⟩ := H5
  exact ⟨H0, (⟨H2, (⟨H4, (fun D H7 => H6 D b3 H7 (col_trivial_2_c b4 b3))⟩)⟩)⟩))), (fun H => (by
  obtain ⟨H0, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨H0, (⟨H2, (⟨H4, (⟨(col_trivial_3_c b4 b3), (fun P0 Q H6 H7 => per_col_c P0 b4 b3 Q H2 (H5 P0 H6) H7)⟩)⟩)⟩)⟩))⟩
theorem cop3_orth__orth_c :
    ∀ (A B C D E F U V : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth A B C U V → Orth D E F U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  obtain ⟨x, x0⟩ := b12
  exact ⟨x, (cop3_orth_at__orth_at_c b0 b1 b2 b3 b4 b5 b6 b7 x b8 b9 b10 b11 x0)⟩
theorem col2_orth__orth_c :
    ∀ (A B C P Q U V : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth A B C P Q → Orth A B C U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  obtain ⟨x, x0⟩ := b10
  exact ⟨x, (col2_orth_at__orth_at_c b0 b1 b2 b3 b4 b5 b6 x b7 b8 b9 x0)⟩
theorem col_orth__orth_c :
    ∀ (A B C U V W : Tpoint), U ≠ W → Col U V W → Orth A B C U V → Orth A B C U W :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  col2_orth__orth_c b0 b1 b2 b3 b4 b3 b5 b6 (col_trivial_3_c b3 b4) b7 b8
theorem orth_symmetry_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V → Orth A B C V U := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨x, x0⟩ := b5
  exact ⟨x, (orth_at_symmetry_c b0 b1 b2 b3 b4 x x0)⟩
theorem orth_distincts_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ U ≠ V := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨x, x0⟩ := b5
  exact orth_at_distincts_c b0 b1 b2 b3 b4 x x0
theorem col_cop_orth__orth_at_c :
    ∀ (A B C U V X : Tpoint), Orth A B C U V → Coplanar A B C X → Col U V X → Orth_at X A B C U V := sorry
theorem l11_60_aux_c :
    ∀ (A B C D P Q : Tpoint), ¬ Col A B C → Cong A P A Q → Cong B P B Q → Cong C P C Q → Coplanar A B C D → Cong D P D Q := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have e := midpoint_existence_c b4 b5
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  have H1 := not_col_distincts_c b0 b1 b2 b6
  have H2 := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨x3, x4⟩ := b10
  rcases x4 with x5 | x5
  · obtain ⟨H10, H11⟩ := x5
    exact l4_17 ((fun H12 => (by
  subst H12
  exact b6 H10))) ((by colr)) b9 (l4_17 H4 H10 b7 b8)
  · rcases x5 with x6 | x6
    · obtain ⟨H11, H12⟩ := x6
      exact l4_17 ((fun H13 => (by
  subst H13
  exact b6 ((by colr))))) ((by colr)) b8 (l4_17 H7 H11 b7 b9)
    · obtain ⟨H11, H12⟩ := x6
      exact l4_17 ((fun H13 => (by
  subst H13
  exact b6 ((by colr))))) ((by colr)) b7 (l4_17 H6 H12 b8 b9)
theorem l11_60_c :
    ∀ (A B C D E P : Tpoint), ¬ Col A B C → Per A D P → Per B D P → Per C D P → Coplanar A B C E → Per E D P := sorry
theorem l11_60_bis_c :
    ∀ (A B C D P : Tpoint), ¬ Col A B C → D ≠ P → Coplanar A B C D → Per A D P → Per B D P → Per C D P → Orth_at D A B C D P :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  ⟨b5, (⟨b6, (⟨b7, (⟨(col_trivial_3_c b3 b4), (fun E Q HE HQ => per_col_c E b3 b4 Q b6 (l11_60_c b0 b1 b2 b3 E b4 b5 b8 b9 b10 HE) HQ)⟩)⟩)⟩)⟩
theorem l11_61_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ A' → A ≠ B → A ≠ C → Coplanar A A' B B' → Per B A A' → Per B' A' A → Coplanar A A' C C' → Per C A A' → Per B A C → Per B' A' C' := sorry
theorem l11_61_bis_c :
    ∀ (A B C D E P Q : Tpoint), Orth_at D A B C D P → Perp D E E Q → Coplanar A B C E → Coplanar D E P Q → Orth_at E A B C E Q := sorry
theorem l11_62_unicity_c :
    ∀ (A B C D D' P : Tpoint), Coplanar A B C D → Coplanar A B C D' → (∀ (E : Tpoint), Coplanar A B C E → Per E D P) → (∀ (E : Tpoint), Coplanar A B C E → Per E D' P) → D = D' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  l8_7_c b5 b3 b4 (l8_2_c b4 b3 b5 (b8 b4 b7)) (l8_2_c b3 b4 b5 (b9 b3 b6))
theorem l11_62_unicity_bis_c :
    ∀ (A B C U X Y : Tpoint), Orth_at X A B C X U → Orth_at Y A B C Y U → X = Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H0⟩ := b7
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := b6
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, H9⟩ := H8
  exact l11_62_unicity_c b0 b1 b2 b4 b5 b3 H7 H2 (fun E H => H9 E b3 H (col_trivial_2_c b4 b3)) (fun E H => H4 E b3 H (col_trivial_2_c b5 b3))
theorem orth_at2__eq_c :
    ∀ (A B C U V X Y : Tpoint), Orth_at X A B C U V → Orth_at Y A B C U V → X = Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨_, H0⟩ := b8
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := b7
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, H9⟩ := H8
  exact l11_62_unicity_c b0 b1 b2 b5 b6 b3 H7 H2 (fun E H => H9 E b3 H (col_trivial_3_c b3 b4)) (fun E H => H4 E b3 H (col_trivial_3_c b3 b4))
theorem col_cop_orth_at__eq_c :
    ∀ (A B C U V X Y : Tpoint), Orth_at X A B C U V → Coplanar A B C Y → Col U V Y → X = Y :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  orth_at2__eq_c b0 b1 b2 b3 b4 b5 b6 b7 (col_cop_orth__orth_at_c b0 b1 b2 b3 b4 b6 (⟨b5, b7⟩) b8 b9)
theorem orth_at__ncop1_c :
    ∀ (A B C U V X : Tpoint), U ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C U :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  (fun HCop => b6 (Eq.symm (col_cop_orth_at__eq_c b0 b1 b2 b3 b4 b5 b3 b7 HCop (col_trivial_3_c b3 b4))))
theorem orth_at__ncop2_c :
    ∀ (A B C U V X : Tpoint), V ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C V :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  orth_at__ncop1_c b0 b1 b2 b4 b3 b5 b6 (orth_at_symmetry_c b0 b1 b2 b3 b4 b5 b7)
theorem orth_at__ncop_c :
    ∀ (A B C P X : Tpoint), Orth_at X A B C X P → ¬ Coplanar A B C P := by
  intro b0 b1 b2 b3 b4 b5
  have Hd := b5
  have Hd0 := orth_at_distincts_c b0 b1 b2 b4 b3 b4 Hd
  obtain ⟨_, H0⟩ := Hd0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact orth_at__ncop2_c b0 b1 b2 b4 b3 b4 (Ne.symm H2) b5
theorem l11_62_existence_c :
    ∀ (A B C P : Tpoint), ∃ (D : Tpoint), Coplanar A B C D ∧ ∀ (E : Tpoint), Coplanar A B C E → Per E D P := sorry
theorem l11_62_existence_bis_c :
    ∀ (A B C P : Tpoint), ¬ Coplanar A B C P → ∃ (X : Tpoint), Orth_at X A B C X P := sorry
theorem l11_63_aux_c :
    ∀ (A B C D E P : Tpoint), Coplanar A B C D → D ≠ E → Orth_at E A B C E P → ∃ (Q : Tpoint), OS D E P Q ∧ Orth A B C D Q := sorry
theorem l11_63_existence_c :
    ∀ (A B C D P : Tpoint), Coplanar A B C D → ¬ Coplanar A B C P → ∃ (Q : Tpoint), Orth A B C D Q := by
  intro b0 b1 b2 b3 b4 b5 b6
  have e := l11_62_existence_bis_c b0 b1 b2 b4 b6
  obtain ⟨x, x0⟩ := e
  have o := point_equality_decidability b3 x
  rcases o with x1 | x1
  · exact ⟨b4, (⟨b3, ((by
  subst x1
  exact x0))⟩)⟩
  · have e0 := l11_63_aux_c b0 b1 b2 b3 x b4 b5 x1 x0
    obtain ⟨x2, x3⟩ := e0
    obtain ⟨x4, x5⟩ := x3
    exact ⟨x2, x5⟩
theorem l8_21_3_c :
    ∀ (A B C D X : Tpoint), Coplanar A B C D → ¬ Coplanar A B C X → ∃ (P T : Tpoint), Orth A B C D P ∧ Coplanar A B C T ∧ Bet X T P := sorry
theorem mid2_orth_at2__cong_c :
    ∀ (A B C X Y P Q P' Q' : Tpoint), Orth_at X A B C X P → Orth_at Y A B C Y Q → Midpoint X P P' → Midpoint Y Q Q' → Cong P Q P' Q' := sorry
theorem orth_at2_tsp__ts_c :
    ∀ (A B C X Y P Q : Tpoint), P ≠ Q → Orth_at P A B C P X → Orth_at Q A B C Q Y → TSP A B C X Y → TS P Q X Y := sorry
theorem orth_dec_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V ∨ ¬ Orth A B C U V := sorry
theorem orth_at_dec_c :
    ∀ (A B C U V X : Tpoint), Orth_at X A B C U V ∨ ¬ Orth_at X A B C U V := by
  intro b0 b1 b2 b3 b4 b5
  have o := orth_dec_c b0 b1 b2 b3 b4
  rcases o with x | x
  · have o0 := cop_dec_c b0 b1 b2 b5
    rcases o0 with x0 | x0
    · have o1 := col_dec_c b3 b4 b5
      rcases o1 with x1 | x1
      · exact Or.inl (col_cop_orth__orth_at_c b0 b1 b2 b3 b4 b5 x x0 x1)
      · exact Or.inr ((fun H2 => (by
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨H6, _⟩ := H5
  exact x1 H6)))
    · exact Or.inr ((fun H1 => (by
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, _⟩ := H5
  exact x0 H4)))
  · exact Or.inr ((fun HX => x (⟨b5, HX⟩)))
theorem tsp_dec_c :
    ∀ (A B C X Y : Tpoint), TSP A B C X Y ∨ ¬ TSP A B C X Y := sorry
theorem osp_dec_c :
    ∀ (A B C X Y : Tpoint), OSP A B C X Y ∨ ¬ OSP A B C X Y := sorry
theorem ts2__inangle_c :
    ∀ (A B C P : Tpoint), TS A C B P → TS B P A C → InAngle P A B C := sorry
theorem os_ts__inangle_c :
    ∀ (A B C P : Tpoint), TS B P A C → OS B A C P → InAngle P A B C := sorry
theorem os2__inangle_c :
    ∀ (A B C P : Tpoint), OS B A C P → OS B C A P → InAngle P A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  os_ts__inangle_c b0 b1 b2 b3 (l9_31_c b1 b0 b3 b2 (one_side_symmetry_c b1 b0 b2 b3 b4) (one_side_symmetry_c b1 b2 b0 b3 b5)) b4
theorem acute_conga__acute_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → CongA A B C D E F → Acute D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  acute_lea_acute_c b3 b4 b5 b0 b1 b2 b6 (conga__lea_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b7))
theorem acute_out2__acute_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Acute A B C → Acute A' B C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  acute_conga__acute_c b0 b1 b2 b3 b1 b4 b7 (out2__conga_c b0 b1 b2 b3 b4 b5 b6)
theorem conga_obtuse__obtuse_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → CongA A B C D E F → Obtuse D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  lea_obtuse_obtuse_c b3 b4 b5 b0 b1 b2 b6 (conga__lea_c b0 b1 b2 b3 b4 b5 b7)
theorem obtuse_out2__obtuse_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Obtuse A B C → Obtuse A' B C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  conga_obtuse__obtuse_c b0 b1 b2 b3 b1 b4 b7 (out2__conga_c b0 b1 b2 b3 b4 b5 b6)
theorem bet_lea__bet_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → LeA A B C D E F → Bet D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  exact bet_conga__bet_c b0 b1 b2 b3 b4 b5 b6 (lea_asym_c b0 b1 b2 b3 b4 b5 b7 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b7; (by
  obtain ⟨H, H0⟩ := Hlea0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  exact l11_31_2_c b3 b4 b5 b0 b1 b2 H3 H4 H H1 b6))))
theorem out_lea__out_c :
    ∀ (A B C D E F : Tpoint), Out E D F → LeA A B C D E F → Out B A C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  exact l11_21_a_c b3 b4 b5 b0 b1 b2 b6 (lea_asym_c b3 b4 b5 b0 b1 b2 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b7; (by
  obtain ⟨H, H0⟩ := Hlea0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, _⟩ := H2
  exact l11_31_1_c b3 b4 b5 b0 b1 b2 b6 H H1))) b7)
theorem bet2_lta__lta_c :
    ∀ (A B C D E F A' D' : Tpoint), LtA A B C D E F → Bet A B A' → A' ≠ B → Bet D E D' → D' ≠ E → LtA D' E F A' B C := sorry
theorem lea123456_lta__lta_c :
    ∀ (A B C D E F G H I : Tpoint), LeA A B C D E F → LtA D E F G H I → LtA A B C G H I := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨(lea_trans_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 (lta__lea_c b3 b4 b5 b6 b7 b8 b10)), ((fun H0 => (by
  obtain ⟨x, x0⟩ := b10
  exact x0 (lea_asym_c b3 b4 b5 b6 b7 b8 x (l11_30_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b3 b4 b5 b9 H0 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b9; (by
  obtain ⟨_, H2⟩ := Hlea0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  exact conga_refl_c b3 b4 b5 H4 H5))))))))⟩
theorem lea456789_lta__lta_c :
    ∀ (A B C D E F G H I : Tpoint), LtA A B C D E F → LeA D E F G H I → LtA A B C G H I := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨(lea_trans_c b0 b1 b2 b3 b4 b5 b6 b7 b8 (lta__lea_c b0 b1 b2 b3 b4 b5 b9) b10), ((fun H0 => (by
  obtain ⟨x, x0⟩ := b9
  exact x0 (lea_asym_c b0 b1 b2 b3 b4 b5 x (l11_30_c b3 b4 b5 b6 b7 b8 b3 b4 b5 b0 b1 b2 b10 ((let Hlea0 := lea_distincts_c b3 b4 b5 b6 b7 b8 b10; (by
  obtain ⟨H1, H2⟩ := Hlea0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact conga_refl_c b3 b4 b5 H1 H3))) (conga_sym_c b0 b1 b2 b6 b7 b8 H0))))))⟩
theorem acute_per__lta_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → D ≠ E → E ≠ F → Per D E F → LtA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := b6
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  have Hdiff := lta_distincts_c b0 b1 b2 x x1 x3 x6
  obtain ⟨H3, H4⟩ := Hdiff
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, _⟩ := H8
  exact conga_preserves_lta_c b0 b1 b2 x x1 x3 b0 b1 b2 b3 b4 b5 (conga_refl_c b0 b1 b2 H3 H5) (l11_16_c x x1 x3 b3 b4 b5 x5 H7 H9 b9 b7 (Ne.symm b8)) x6
theorem obtuse_per__lta_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → D ≠ E → E ≠ F → Per D E F → LtA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := b6
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  have Hdiff := lta_distincts_c x x1 x3 b0 b1 b2 x6
  obtain ⟨H3, H4⟩ := Hdiff
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, _⟩ := H8
  exact conga_preserves_lta_c x x1 x3 b0 b1 b2 b3 b4 b5 b0 b1 b2 (l11_16_c x x1 x3 b3 b4 b5 x5 H3 H5 b9 b7 (Ne.symm b8)) (conga_refl_c b0 b1 b2 H7 H9) x6
theorem acute_obtuse__lta_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → Obtuse D E F → LtA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨x, x0⟩ := b6
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact lta_trans_c b0 b1 b2 x x1 x3 b3 b4 b5 x6 ((let Hlta0 := lta_distincts_c b0 b1 b2 x x1 x3 x6; (by
  obtain ⟨_, H3⟩ := Hlta0
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, _⟩ := H6
  exact obtuse_per__lta_c b3 b4 b5 x x1 x3 b7 H5 (Ne.symm H7) x5)))
theorem lea_in_angle_c :
    ∀ (A B C P : Tpoint), LeA A B P A B C → OS A B C P → InAngle P A B C := sorry
theorem acute_bet__obtuse_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Acute A B C → Obtuse A' B C := sorry
theorem bet_obtuse__acute_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Obtuse A B C → Acute A' B C := sorry
theorem inangle_dec_c :
    ∀ (A B C P : Tpoint), InAngle P A B C ∨ ¬ InAngle P A B C := sorry
theorem lea_dec_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F ∨ ¬ LeA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5
  rcases (point_equality_decidability b0 b1) with H | H
  · exact Or.inr ((fun Hlea => (let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 Hlea; (by
  obtain ⟨H0, H1⟩ := Hlea0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, _⟩ := H2
  exact H0 H))))
  · rcases (point_equality_decidability b1 b2) with H0 | H0
    · exact Or.inr ((fun Hlea => (let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 Hlea; (by
  obtain ⟨_, H2⟩ := Hlea0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact H3 (Eq.symm H0)))))
    · rcases (point_equality_decidability b3 b4) with H1 | H1
      · exact Or.inr ((fun Hlea => (let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 Hlea; (by
  obtain ⟨_, H3⟩ := Hlea0
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, _⟩ := H4
  exact H5 H1))))
      · rcases (point_equality_decidability b4 b5) with H2 | H2
        · exact Or.inr ((fun Hlea => (let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 Hlea; (by
  obtain ⟨_, H4⟩ := Hlea0
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  exact H6 (Eq.symm H2)))))
        · rcases (col_dec_c b0 b1 b2) with H3 | HNColB
          · rcases (out_dec_c b1 b0 b2) with H4 | H4
            · exact Or.inl (l11_31_1_c b0 b1 b2 b3 b4 b5 H4 H1 (Ne.symm H2))
            · rcases (bet_dec_c b3 b4 b5) with H5 | HENBet
              · exact Or.inl (l11_31_2_c b0 b1 b2 b3 b4 b5 H (Ne.symm H0) H1 (Ne.symm H2) H5)
              · exact Or.inr ((fun H5 => HENBet (bet_lea__bet_c b0 b1 b2 b3 b4 b5 (not_out_bet_c b0 b1 b2 H3 H4) H5)))
          · rcases (col_dec_c b3 b4 b5) with H3 | H3
            · rcases (bet_dec_c b3 b4 b5) with H4 | H4
              · exact Or.inl (l11_31_2_c b0 b1 b2 b3 b4 b5 H (Ne.symm H0) H1 (Ne.symm H2) H4)
              · exact Or.inr ((fun H5 => HNColB (col_permutation_4_c b1 b0 b2 (out_col (out_lea__out_c b0 b1 b2 b3 b4 b5 (not_bet_out_c b3 b4 b5 H3 H4) H5)))))
            · have HP := angle_construction_1_c b0 b1 b2 b3 b4 b5
              have e := HP HNColB H3
              obtain ⟨x, x0⟩ := e
              obtain ⟨x1, x2⟩ := x0
              rcases (inangle_dec_c b3 b4 b5 x) with H7 | HNInAngle
              · exact Or.inl (⟨x, (⟨H7, x1⟩)⟩)
              · exact Or.inr ((fun H7 => HNInAngle (lea_in_angle_c b3 b4 b5 x (l11_30_c b0 b1 b2 b3 b4 b5 b3 b4 x b3 b4 b5 H7 x1 (conga_refl_c b3 b4 b5 H1 (Ne.symm H2))) (one_side_symmetry_c b3 b4 x b5 x2))))
theorem lta_dec_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F ∨ ¬ LtA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5
  rcases (conga_dec_c b0 b1 b2 b3 b4 b5) with H | H
  · exact Or.inr (((fun H0 => (by
  obtain ⟨_, H1⟩ := H0
  exact H1 H))))
  · rcases (lea_dec_c b0 b1 b2 b3 b4 b5) with H0 | H0
    · exact Or.inl (⟨H0, H⟩)
    · exact Or.inr (((fun H1 => (by
  obtain ⟨H2, _⟩ := H1
  exact H0 H2))))
theorem lea_total_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → D ≠ E → E ≠ F → LeA A B C D E F ∨ LeA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  rcases (col_dec_c b0 b1 b2) with H | H
  · rcases (out_dec_c b1 b0 b2) with H0 | H0
    · exact Or.inl (l11_31_1_c b0 b1 b2 b3 b4 b5 H0 b8 (Ne.symm b9))
    · exact Or.inr (l11_31_2_c b3 b4 b5 b0 b1 b2 b8 (Ne.symm b9) b6 (Ne.symm b7) (not_out_bet_c b0 b1 b2 H H0))
  · rcases (col_dec_c b3 b4 b5) with H0 | H0
    · rcases (out_dec_c b4 b3 b5) with H1 | H1
      · exact Or.inr (l11_31_1_c b3 b4 b5 b0 b1 b2 H1 b6 (Ne.symm b7))
      · exact Or.inl (l11_31_2_c b0 b1 b2 b3 b4 b5 b6 (Ne.symm b7) b8 (Ne.symm b9) (not_out_bet_c b3 b4 b5 H0 H1))
    · rcases (lea_dec_c b0 b1 b2 b3 b4 b5) with H1 | HNlea
      · exact Or.inl H1
      · exact Or.inr ((let HP := angle_construction_1_c b3 b4 b5 b0 b1 b2; (let e := HP H0 H; (by
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨x, (⟨(os2__inangle_c b0 b1 b2 x (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2)) (cop_nts__os_c b1 b2 b0 x ((let H4 := os__coplanar_c b0 b1 x b2 x2; coplanar_perm_10_c b0 b1 x b2 H4)) H ((fun H4 => HNlea (conga__lea_c b0 b1 b2 b3 b4 b5 (l11_10_c b0 b1 x b3 b4 b5 b0 b2 b3 b5 (conga_sym_c b3 b4 b5 b0 b1 x x1) (out_trivial b6) (col_one_side_out_c b1 b0 b2 x (col_permutation_5_c b1 x b2 (col_permutation_4_c x b1 b2 H4)) (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2))) (out_trivial b8) (out_trivial (Ne.symm b9)))))) ((fun H4 => HNlea (l11_30_c b0 b1 b2 b0 b1 x b0 b1 b2 b3 b4 b5 (⟨b2, (⟨(os_ts__inangle_c b0 b1 x b2 H4 (one_side_symmetry_c b1 b0 b2 x (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2)))), (conga_refl_c b0 b1 b2 b6 (Ne.symm b7))⟩)⟩) (conga_refl_c b0 b1 b2 b6 (Ne.symm b7)) (conga_sym_c b3 b4 b5 b0 b1 x x1)))))), x1⟩)⟩))))
theorem or_lta2_conga_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → C ≠ B → D ≠ E → F ≠ E → LtA A B C D E F ∨ LtA D E F A B C ∨ CongA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HH := lea_total_c b0 b1 b2 b3 b4 b5
  have o := HH b6 (Ne.symm b7) b8 (Ne.symm b9)
  rcases o with H3 | H3
  · have o0 := conga_dec_c b0 b1 b2 b3 b4 b5
    rcases o0 with H4 | H4
    · exact Or.inr (Or.inr H4)
    · exact Or.inl (⟨H3, H4⟩)
  · have o0 := conga_dec_c b0 b1 b2 b3 b4 b5
    rcases o0 with H4 | H4
    · exact Or.inr (Or.inr H4)
    · exact Or.inr (Or.inl (⟨H3, ((fun H5 => H4 (conga_sym_c b3 b4 b5 b0 b1 b2 H5)))⟩))
theorem angle_partition_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Acute A B C ∨ Per A B C ∨ Obtuse A B C := sorry
theorem acute_chara_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → B ≠ A' → (Acute A B C ↔ LtA A B C A' B C) := sorry
theorem obtuse_chara_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → B ≠ A' → (Obtuse A B C ↔ LtA A' B C A B C) := sorry
theorem conga__acute_c :
    ∀ (A B C : Tpoint), CongA A B C A C B → Acute A B C := sorry
theorem cong__acute_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Cong A B A C → Acute A B C := by
  intro b0 b1 b2 b3 b4 b5
  exact conga__acute_c b0 b1 b2 ((let H := cong_diff b3 b5; (let a := l11_51_c b0 b1 b2 b0 b2 b1 b3 H b4 b5 (cong_symmetry b5) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity b1 b2)))); (by
  obtain ⟨x, x0⟩ := a
  obtain ⟨x1, x2⟩ := x0
  exact x1))))
theorem nlta__lea_c :
    ∀ (A B C D E F : Tpoint), ¬ LtA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LeA D E F A B C := sorry
theorem nlea__lta_c :
    ∀ (A B C D E F : Tpoint), ¬ LeA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LtA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨((by
  rcases (lea_total_c b3 b4 b5 b0 b1 b2 b9 b10 b7 b8) with H3 | H3
  · exact H3
  · exact ((b6 H3)).elim)), ((fun H3 => b6 (conga__lea_c b0 b1 b2 b3 b4 b5 (conga_sym_c b3 b4 b5 b0 b1 b2 H3))))⟩
theorem triangle_strict_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → ¬ Bet A B C → Lt A C A D := sorry
theorem triangle_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → Le A C A D := sorry
theorem triangle_strict_inequality_2_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → ¬ Bet A B C → Lt A C A' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have e := segment_construction b0 b1 b1 b2
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact cong2_lt__lt_c b0 b2 b0 x b0 b2 b3 b5 (triangle_strict_inequality_c b0 b1 b2 x x1 (cong_symmetry x2) b9) (cong_reflexivity b0 b2) (l2_11 x1 b6 b7 (cong_transitivity x2 b8))
theorem triangle_inequality_2_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → Le A C A' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have e := segment_construction b0 b1 b1 b2
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact l5_6_c b0 b2 b0 x b0 b2 b3 b5 (triangle_inequality_c b0 b1 b2 x x1 (cong_symmetry x2)) (cong_reflexivity b0 b2) (l2_11 x1 b6 b7 (cong_transitivity x2 b8))
theorem triangle_strict_reverse_inequality_c :
    ∀ (A B C D : Tpoint), Out A B D → Cong A C A D → ¬ Out A B C → Lt B D B C := sorry
theorem triangle_reverse_inequality_c :
    ∀ (A B C D : Tpoint), Out A B D → Cong A C A D → Le B D B C := sorry
theorem os3__lta_c :
    ∀ (A B C D : Tpoint), OS A B C D → OS B C A D → OS A C B D → LtA B A C B D C := sorry
theorem bet_le__lt_c :
    ∀ (A B C D : Tpoint), Bet A D B → A ≠ D → D ≠ B → Le A C B C → Lt D C B C := sorry
theorem cong2__ncol_c :
    ∀ (P A B C : Tpoint), A ≠ B → B ≠ C → A ≠ C → Cong A P B P → Cong A P C P → ¬ Col A B C := sorry
theorem cong4_cop2__eq_c :
    ∀ (A B C P Q : Tpoint), A ≠ B → B ≠ C → A ≠ C → Cong A P B P → Cong A P C P → Coplanar A B C P → Cong A Q B Q → Cong A Q C Q → Coplanar A B C Q → P = Q := sorry
theorem t18_18_aux_c :
    ∀ (A B C D E F : Tpoint), Cong A B D E → Cong A C D F → LtA F D E C A B → ¬ Col A B C → ¬ Col D E F → Le D F D E → Lt E F B C := sorry
theorem t18_18_c :
    ∀ (A B C D E F : Tpoint), Cong A B D E → Cong A C D F → LtA F D E C A B → Lt E F B C := sorry
theorem t18_19_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → A ≠ C → Cong A B D E → Cong A C D F → Lt E F B C → LtA F D E C A B := sorry
theorem acute_trivial_c :
    ∀ (A B : Tpoint), A ≠ B → Acute A B A := by
  intro b0 b1 b2
  have HH := not_col_exists_c b0 b1 b2
  obtain ⟨P, H0⟩ := HH
  have H1 := ex_per_cong_c b0 b1 b1 P b0 b1 b2 b2 (col_trivial_2_c b0 b1) H0
  obtain ⟨C, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, _⟩ := H4
  have H6 := not_col_distincts_c b0 b1 P H0
  have H7 := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, _⟩ := H9
  have H10 := cong_diff_3_c C b1 b0 b1 b2 H5
  have H11 := per_distinct_c C b1 b0 H3 H10
  exact ⟨b0, (⟨b1, (⟨C, (⟨(l8_2_c C b1 b0 H3), (⟨(⟨b0, (⟨(inangle1123_c b0 b1 C b2 H10), (conga_refl_c b0 b1 b0 b2 b2)⟩)⟩), ((fun H12 => (let H13 := l11_21_a_c b0 b1 b0 b0 b1 C (out_trivial b2) H12; (let H14 := (let H14 := per_perp_in_c C b1 b0 H10 (Ne.symm b2) H3; (let H15 := perp_in_perp_bis_c C b1 b1 b0 b1 H14; (by
  rcases H15 with H16 | H16
  · have H17 := perp_not_eq_1_c b1 b1 b1 b0 H16
    have H18 := (let H18 := rfl; H17 H18)
    exact (H18).elim
  · exact H16))); (let H15 := perp_comm_c C b1 b1 b0 H14; (let H16 := perp_not_col_c b1 C b0 H15; (let H17 := out_col H13; H16 (col_permutation_5_c b1 b0 C H17))))))))⟩)⟩)⟩)⟩)⟩
theorem acute_not_per_c :
    ∀ (A B C : Tpoint), Acute A B C → ¬ Per A B C := sorry
theorem angle_bisector_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → ∃ (P : Tpoint), InAngle P A B C ∧ CongA P B A P B C := sorry
theorem reflectl__conga_c :
    ∀ (A B P P' : Tpoint), A ≠ B → B ≠ P → ReflectL P P' A B → CongA A B P A B P' := sorry
theorem conga_cop_out_reflectl__out_c :
    ∀ (A B C P T T' : Tpoint), ¬ Out B A C → Coplanar A B C P → CongA P B A P B C → Out B A T → ReflectL T T' B P → Out B C T' := sorry
theorem col_conga_cop_reflectl__col_c :
    ∀ (A B C P T T' : Tpoint), ¬ Out B A C → Coplanar A B C P → CongA P B A P B C → Col B A T → ReflectL T T' B P → Col B C T' := sorry
theorem conga2_cop2__col_c :
    ∀ (A B C P P' : Tpoint), ¬ Out B A C → CongA P B A P B C → CongA P' B A P' B C → Coplanar A B P P' → Coplanar B C P P' → Col B P P' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HP0 := conga_distinct_c b3 b1 b0 b3 b1 b2 b6
  have HP'0 := conga_distinct_c b4 b1 b0 b4 b1 b2 b7
  obtain ⟨H, H0⟩ := HP'0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  obtain ⟨H4, H5⟩ := HP0
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  have e := l6_11_existence_c b1 b1 b0 b2 H10 (Ne.symm H8)
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  have a := l11_49_c b3 b1 b0 b3 b1 x (l11_10_c b3 b1 b0 b3 b1 b2 b3 b0 b3 x H4 (out_trivial H6) (out_trivial H8) (out_trivial H6) x1) (cong_reflexivity b1 b3) (cong_symmetry x2)
  obtain ⟨x3, x4⟩ := a
  have a0 := l11_49_c b4 b1 b0 b4 b1 x (l11_10_c b4 b1 b0 b4 b1 b2 b4 b0 b4 x H (out_trivial H1) (out_trivial H8) (out_trivial H1) x1) (cong_reflexivity b1 b4) (cong_symmetry x2)
  obtain ⟨x5, x6⟩ := a0
  exact cong3_cop2__col_c b1 b3 b4 b0 x (coplanar_perm_9_c b0 b1 b3 b4 b8) (coplanar_perm_12_c b3 b4 b1 x (col_cop__cop_c b3 b4 b1 b2 x (coplanar_perm_16_c b1 b2 b3 b4 b9) (Ne.symm H10) (col_permutation_5_c b1 x b2 (out_col x1)))) ((fun H16 => (by
  subst H16
  exact b5 x1))) (cong_symmetry x2) x3 x5
theorem conga2_cop2__col_1_c :
    ∀ (A B C P P' : Tpoint), ¬ Col A B C → CongA P B A P B C → CongA P' B A P' B C → Coplanar A B C P → Coplanar A B C P' → Col B P P' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  conga2_cop2__col_c b0 b1 b2 b3 b4 ((fun H => b5 (col_permutation_4_c b1 b0 b2 (out_col H)))) b6 b7 (coplanar_pseudo_trans_c b0 b1 b3 b4 b0 b1 b2 b5 (coplanar_perm_1_c b0 b1 b0 b2 (col__coplanar_c b0 b1 b0 b2 (col_trivial_3_c b0 b1))) (coplanar_perm_1_c b0 b1 b1 b2 (col__coplanar_c b0 b1 b1 b2 (col_trivial_2_c b0 b1))) b8 b9) (coplanar_pseudo_trans_c b1 b2 b3 b4 b0 b1 b2 b5 (coplanar_perm_1_c b0 b1 b1 b2 (col__coplanar_c b0 b1 b1 b2 (col_trivial_2_c b0 b1))) (coplanar_perm_4_c b0 b2 b2 b1 (col__coplanar_c b0 b2 b2 b1 (col_trivial_2_c b0 b2))) b8 b9)
theorem col_conga__conga_c :
    ∀ (A B C P P' : Tpoint), CongA P B A P B C → Col B P P' → B ≠ P' → CongA P' B A P' B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have o := bet_dec_c b3 b1 b4
  rcases o with x | x
  · exact l11_13_c b3 b1 b0 b3 b1 b2 b4 b4 b5 x (Ne.symm b7) x (Ne.symm b7)
  · have HNBet0 := not_bet_out_c b3 b1 b4 (col_permutation_5_c b3 b4 b1 (col_permutation_1_c b1 b3 b4 b6)) x
    have HNBet1 := l6_6 HNBet0
    have HConga0 := conga_distinct_c b3 b1 b0 b3 b1 b2 b5
    obtain ⟨H, H0⟩ := HConga0
    obtain ⟨_, H1⟩ := H0
    obtain ⟨H2, H3⟩ := H1
    obtain ⟨_, H4⟩ := H3
    exact l11_10_c b3 b1 b0 b3 b1 b2 b4 b0 b4 b2 H HNBet1 (out_trivial H2) HNBet1 (out_trivial H4)
theorem cop_inangle__ex_col_inangle_c :
    ∀ (A B C P Q : Tpoint), ¬ Out B A C → InAngle P A B C → Coplanar A B C Q → ∃ (R : Tpoint), InAngle R A B C ∧ P ≠ R ∧ Col P Q R := sorry
theorem col_inangle2__out_c :
    ∀ (A B C P Q : Tpoint), ¬ Bet A B C → InAngle P A B C → InAngle Q A B C → Col B P Q → Out B P Q := sorry
theorem inangle2__lea_c :
    ∀ (A B C P Q : Tpoint), InAngle P A B C → InAngle Q A B C → LeA P B Q A B C := sorry
theorem conga_inangle_per__acute_c :
    ∀ (A B C P : Tpoint), Per A B C → InAngle P A B C → CongA P B A P B C → Acute A B P := sorry
theorem conga_inangle2_per__acute_c :
    ∀ (A B C P Q : Tpoint), Per A B C → InAngle P A B C → CongA P B A P B C → InAngle Q A B C → Acute P B Q := sorry
theorem lta_os__ts_c :
    ∀ (A O B P : Tpoint), ¬ Col A O P → LtA A O P A O B → OS O A B P → TS O P A B := sorry
theorem bet__suppa_c :
    ∀ (A B C A' : Tpoint), A ≠ B → B ≠ C → B ≠ A' → Bet A B A' → SuppA A B C C B A' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b4, (⟨b3, (⟨b7, (conga_refl_c b2 b1 b3 (Ne.symm b5) (Ne.symm b6))⟩)⟩)⟩
theorem ex_suppa_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → ∃ (D E F : Tpoint), SuppA A B C D E F := by
  intro b0 b1 b2 b3 b4
  have e := segment_construction b0 b1 b0 b1
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨b2, (⟨b1, (⟨x, (bet__suppa_c b0 b1 b2 x b3 b4 ((fun H4 => (by
  subst H4
  have H6 := cong_symmetry x2
  have H7 := cong_identity b0 b1 b1 H6
  subst H7
  exact b3 rfl))) x1)⟩)⟩)⟩
theorem suppa_distincts_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → A ≠ B ∧ B ≠ C ∧ D ≠ E ∧ E ≠ F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨A', H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  have H4 := conga_distinct_c b3 b4 b5 b2 b1 A' H3
  obtain ⟨_, H5⟩ := H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, _⟩ := H9
  exact ⟨H0, (⟨(Ne.symm H10), (⟨H6, (Ne.symm H8)⟩)⟩)⟩
theorem suppa_right_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA A B C F E D := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  exact ⟨H0, ((by
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact ⟨A', (⟨H3, (conga_left_comm_c b3 b4 b5 b2 b1 A' H4)⟩)⟩))⟩
theorem suppa_left_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA C B A D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  exact ⟨H10, ((let e := segment_construction b2 b1 b2 b1; (by
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨x, (⟨x1, (conga_trans_c b3 b4 b5 b2 b1 A' b0 b1 x H6 ((let H15 := bet_neq12__neq x1 H10; (let H16 := bet_neq12__neq H3 H0; (let H17 := cong_diff_3_c b1 x b2 b1 H10 x2; conga_left_comm_c A' b1 b2 b0 b1 x (l11_14_c A' b1 b2 b0 x (between_symmetry H3) H11 H0 x1 (Ne.symm H10) H17))))))⟩)⟩)))⟩
theorem suppa_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA C B A F E D :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  suppa_left_comm_c b0 b1 b2 b5 b4 b3 (suppa_right_comm_c b0 b1 b2 b3 b4 b5 b6)
theorem suppa_sym_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨_, _⟩ := H10
  exact ⟨H8, ((let e := segment_construction b3 b4 b3 b4; (by
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨x, (⟨x1, ((let H14 := bet_neq12__neq x1 H8; (let H15 := bet_neq12__neq H3 H0; (let H16 := cong_diff_3_c b4 x b3 b4 H8 x2; conga_right_comm_c b0 b1 b2 x b4 b5 (l11_13_c A' b1 b2 b3 b4 b5 b0 x (conga_sym_c b3 b4 b5 A' b1 b2 (conga_right_comm_c b3 b4 b5 b2 b1 A' H6)) (between_symmetry H3) H0 x1 (Ne.symm H16))))))⟩)⟩)))⟩
theorem conga2_suppa__suppa_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), CongA A B C A' B' C' → CongA D E F D' E' F' → SuppA A B C D E F → SuppA A' B' C' D' E' F' := sorry
theorem suppa2__conga456_c :
    ∀ (A B C D E F D' E' F' : Tpoint), SuppA A B C D E F → SuppA A B C D' E' F' → CongA D E F D' E' F' := sorry
theorem suppa2__conga123_c :
    ∀ (A B C D E F A' B' C' : Tpoint), SuppA A B C D E F → SuppA A' B' C' D E F → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  suppa2__conga456_c b3 b4 b5 b0 b1 b2 b6 b7 b8 (suppa_sym_c b0 b1 b2 b3 b4 b5 b9) (suppa_sym_c b6 b7 b8 b3 b4 b5 b10)
theorem bet_out__suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → Bet A B C → Out E D F → SuppA A B C D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ⟨b6, (⟨b2, (⟨b8, (l11_21_b_c b3 b4 b5 b2 b1 b2 b9 (out_trivial (Ne.symm b7)))⟩)⟩)⟩
theorem bet_suppa__out_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → SuppA A B C D E F → Out E D F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have Hd := b7
  have Hd0 := suppa_distincts_c b0 b1 b2 b3 b4 b5 Hd
  obtain ⟨H1, H2⟩ := Hd0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact l11_21_a_c b2 b1 b2 b3 b4 b5 (out_trivial (Ne.symm H3)) (suppa2__conga456_c b0 b1 b2 b2 b1 b2 b3 b4 b5 (⟨H1, (⟨b2, (⟨b6, (conga_refl_c b2 b1 b2 (Ne.symm H3) (Ne.symm H3))⟩)⟩)⟩) b7)
theorem out_suppa__bet_c :
    ∀ (A B C D E F : Tpoint), Out B A C → SuppA A B C D E F → Bet D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have e := segment_construction b0 b1 b0 b1
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact bet_conga__bet_c b0 b1 x b3 b4 b5 x1 (suppa2__conga456_c b0 b1 b2 b0 b1 x b3 b4 b5 ((let H4 := out_distinct_c b1 b0 b2 b6; (let H5 := H4; (by
  obtain ⟨H6, _⟩ := H5
  have H7 := bet_neq12__neq x1 H6
  have H8 := cong_diff_3_c b1 x b0 b1 H6 x2
  exact suppa_sym_c b0 b1 x b0 b1 b2 (bet_out__suppa_c b0 b1 x b0 b1 b2 H6 H8 x1 b6))))) b7)
theorem per_suppa__per_c :
    ∀ (A B C D E F : Tpoint), Per A B C → SuppA A B C D E F → Per D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨A', H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  exact l11_17_c b2 b1 A' b3 b4 b5 ((let H6 := conga_distinct_c b3 b4 b5 b2 b1 A' H5; (by
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, _⟩ := H9
  exact per_col_c b2 b1 b0 A' (Ne.symm H1) (perp_in_per_c b2 b1 b0 (perp_in_sym_c b1 b0 b2 b1 b1 (perp_in_comm_c b0 b1 b1 b2 b1 (per_perp_in_c b0 b1 b2 H1 (Ne.symm H10) b6)))) (col_permutation_4_c b0 b1 A' (bet_col_c b0 b1 A' H4))))) (conga_sym_c b3 b4 b5 b2 b1 A' H5)
theorem per2__suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → D ≠ E → E ≠ F → Per A B C → Per D E F → SuppA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have e := ex_suppa_c b0 b1 b2 b6 b7
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  exact conga2_suppa__suppa_c b0 b1 b2 x x1 x3 b0 b1 b2 b3 b4 b5 (conga_refl_c b0 b1 b2 b6 (Ne.symm b7)) ((let Hd := x4; (let Hd0 := suppa_distincts_c b0 b1 b2 x x1 x3 Hd; (by
  obtain ⟨_, H8⟩ := Hd0
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  exact l11_16_c x x1 x3 b3 b4 b5 (per_suppa__per_c b0 b1 b2 x x1 x3 b10 x4) H10 (Ne.symm H11) b11 b8 (Ne.symm b9))))) x4
theorem suppa__per_c :
    ∀ (A B C : Tpoint), SuppA A B C A B C → Per A B C := by
  intro b0 b1 b2 b3
  obtain ⟨_, H0⟩ := b3
  obtain ⟨A', H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  exact l8_2_c b2 b1 b0 (l11_18_2_c b2 b1 b0 A' H2 (conga_left_comm_c b0 b1 b2 b2 b1 A' H3))
theorem acute_suppa__obtuse_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → SuppA A B C D E F → Obtuse D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact conga_obtuse__obtuse_c b2 b1 A' b3 b4 b5 ((let H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  exact obtuse_sym_c A' b1 b2 (acute_bet__obtuse_c b0 b1 b2 A' H3 H9 b6)))) (conga_sym_c b3 b4 b5 b2 b1 A' H4)
theorem obtuse_suppa__acute_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → SuppA A B C D E F → Acute D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact acute_conga__acute_c b2 b1 A' b3 b4 b5 ((let H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  exact acute_sym_c A' b1 b2 (bet_obtuse__acute_c b0 b1 b2 A' H3 H9 b6)))) (conga_sym_c b3 b4 b5 b2 b1 A' H4)
theorem lea_suppa2__lea_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), SuppA A B C A' B' C' → SuppA D E F D' E' F' → LeA A B C D E F → LeA D' E' F' A' B' C' := sorry
theorem lta_suppa2__lta_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), SuppA A B C A' B' C' → SuppA D E F D' E' F' → LtA A B C D E F → LtA D' E' F' A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  obtain ⟨_, H2⟩ := b13
  obtain ⟨_, H3⟩ := b12
  obtain ⟨A0, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨D0, H7⟩ := H2
  obtain ⟨H8, H9⟩ := H7
  exact conga_preserves_lta_c b5 b4 D0 b2 b1 A0 b9 b10 b11 b6 b7 b8 (conga_sym_c b9 b10 b11 b5 b4 D0 H9) (conga_sym_c b6 b7 b8 b2 b1 A0 H6) ((let H10 := conga_distinct_c b6 b7 b8 b2 b1 A0 H6; (let H11 := conga_distinct_c b9 b10 b11 b5 b4 D0 H9; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H10
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, H19⟩ := H18
  exact lta_comm_c D0 b4 b5 A0 b1 b2 (bet2_lta__lta_c b0 b1 b2 b3 b4 b5 A0 D0 b14 H5 H19 H8 H15)))))
theorem suppa_dec_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F ∨ ¬ SuppA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b0 b1
  rcases o with H | H
  · exact Or.inr ((fun H0 => (by
  obtain ⟨x, x0⟩ := H0
  exact x H)))
  · have o0 := point_equality_decidability b1 b2
    rcases o0 with H0 | H0
    · exact Or.inr ((fun Habs => (let Habs0 := suppa_distincts_c b0 b1 b2 b3 b4 b5 Habs; (by
  obtain ⟨_, H2⟩ := Habs0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact H3 H0))))
    · have e := ex_suppa_c b0 b1 b2 H H0
      obtain ⟨x, x0⟩ := e
      obtain ⟨x1, x2⟩ := x0
      obtain ⟨x3, x4⟩ := x2
      have o1 := conga_dec_c x x1 x3 b3 b4 b5
      rcases o1 with H4 | H4
      · exact Or.inl (conga2_suppa__suppa_c b0 b1 b2 x x1 x3 b0 b1 b2 b3 b4 b5 (conga_refl_c b0 b1 b2 H (Ne.symm H0)) H4 x4)
      · exact Or.inr ((fun H5 => H4 (suppa2__conga456_c b0 b1 b2 x x1 x3 b3 b4 b5 x4 H5)))
theorem acute_one_side_aux_c :
    ∀ (P A O B : Tpoint), OS O A P B → Acute A O P → Perp O A B O → OS O B A P := sorry
theorem acute_one_side_aux0_c :
    ∀ (P A O B : Tpoint), Col A O P → Acute A O P → Perp O A B O → OS O B A P := sorry
theorem acute_cop_perp__one_side_c :
    ∀ (P A O B : Tpoint), Acute A O P → Perp O A B O → Coplanar A B O P → OS O B A P := sorry
theorem acute__not_obtuse_c :
    ∀ (A B C : Tpoint), Acute A B C → ¬ Obtuse A B C := sorry
#print axioms GeocoqTranslate.Tarski.Base.l11_3_c
#print axioms GeocoqTranslate.Tarski.Base.l11_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_3_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_4_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_4_2_c
#print axioms GeocoqTranslate.Tarski.Base.conga_refl_c
#print axioms GeocoqTranslate.Tarski.Base.conga_sym_c
#print axioms GeocoqTranslate.Tarski.Base.l11_10_c
#print axioms GeocoqTranslate.Tarski.Base.out2__conga_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_diff_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_diff2_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_conga_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_conga2_c
#print axioms GeocoqTranslate.Tarski.Base.conga_diff1_c
#print axioms GeocoqTranslate.Tarski.Base.conga_diff2_c
#print axioms GeocoqTranslate.Tarski.Base.conga_diff45_c
#print axioms GeocoqTranslate.Tarski.Base.conga_diff56_c
#print axioms GeocoqTranslate.Tarski.Base.conga_trans_c
#print axioms GeocoqTranslate.Tarski.Base.conga_pseudo_refl_c
#print axioms GeocoqTranslate.Tarski.Base.conga_trivial_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_13_c
#print axioms GeocoqTranslate.Tarski.Base.conga_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.conga_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.conga_comm_c
#print axioms GeocoqTranslate.Tarski.Base.conga_line_c
#print axioms GeocoqTranslate.Tarski.Base.l11_14_c
#print axioms GeocoqTranslate.Tarski.Base.l11_16_c
#print axioms GeocoqTranslate.Tarski.Base.l11_17_c
#print axioms GeocoqTranslate.Tarski.Base.l11_18_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_18_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.l11_21_a_c
#print axioms GeocoqTranslate.Tarski.Base.l11_21_b_c
#print axioms GeocoqTranslate.Tarski.Base.conga_cop__or_out_ts_c
#print axioms GeocoqTranslate.Tarski.Base.conga_os__out_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_conga_cong_c
#print axioms GeocoqTranslate.Tarski.Base.angle_construction_1_c
#print axioms GeocoqTranslate.Tarski.Base.angle_construction_2_c
#print axioms GeocoqTranslate.Tarski.Base.ex_conga_ts_c
#print axioms GeocoqTranslate.Tarski.Base.l11_15_c
#print axioms GeocoqTranslate.Tarski.Base.l11_19_c
#print axioms GeocoqTranslate.Tarski.Base.l11_22_bet_c
#print axioms GeocoqTranslate.Tarski.Base.l11_22a_c
#print axioms GeocoqTranslate.Tarski.Base.l11_22b_c
#print axioms GeocoqTranslate.Tarski.Base.l11_22_c
#print axioms GeocoqTranslate.Tarski.Base.l11_24_c
#print axioms GeocoqTranslate.Tarski.Base.col_in_angle_c
#print axioms GeocoqTranslate.Tarski.Base.out321__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.inangle1123_c
#print axioms GeocoqTranslate.Tarski.Base.out341__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.inangle3123_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_in_angle_out_c
#print axioms GeocoqTranslate.Tarski.Base.l11_25_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_25_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.segment_construction_0_c
#print axioms GeocoqTranslate.Tarski.Base.angle_construction_3_c
#print axioms GeocoqTranslate.Tarski.Base.l11_28_c
#print axioms GeocoqTranslate.Tarski.Base.bet_conga__bet_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_one_side2_c
#print axioms GeocoqTranslate.Tarski.Base.col_conga_col_c
#print axioms GeocoqTranslate.Tarski.Base.ncol_conga_ncol_c
#print axioms GeocoqTranslate.Tarski.Base.angle_construction_4_c
#print axioms GeocoqTranslate.Tarski.Base.lea_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.l11_29_a_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_line_c
#print axioms GeocoqTranslate.Tarski.Base.l11_29_b_c
#print axioms GeocoqTranslate.Tarski.Base.bet_in_angle_bet_c
#print axioms GeocoqTranslate.Tarski.Base.lea_line_c
#print axioms GeocoqTranslate.Tarski.Base.eq_conga_out_c
#print axioms GeocoqTranslate.Tarski.Base.conga_ex_cong3_c
#print axioms GeocoqTranslate.Tarski.Base.conga_preserves_in_angle_c
#print axioms GeocoqTranslate.Tarski.Base.l11_30_c
#print axioms GeocoqTranslate.Tarski.Base.l11_31_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_31_2_c
#print axioms GeocoqTranslate.Tarski.Base.lea_refl_c
#print axioms GeocoqTranslate.Tarski.Base.conga__lea_c
#print axioms GeocoqTranslate.Tarski.Base.conga__lea456123_c
#print axioms GeocoqTranslate.Tarski.Base.lea_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_out4__lea_c
#print axioms GeocoqTranslate.Tarski.Base.lea121345_c
#print axioms GeocoqTranslate.Tarski.Base.inangle__lea_c
#print axioms GeocoqTranslate.Tarski.Base.inangle__lea_1_c
#print axioms GeocoqTranslate.Tarski.Base.inangle__lta_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_trans_c
#print axioms GeocoqTranslate.Tarski.Base.lea_trans_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_asym_c
#print axioms GeocoqTranslate.Tarski.Base.lea_asym_c
#print axioms GeocoqTranslate.Tarski.Base.col_lta__bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_lta__out_c
#print axioms GeocoqTranslate.Tarski.Base.lta_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.gta_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.acute_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_in_angle_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_reverse_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_trans2_c
#print axioms GeocoqTranslate.Tarski.Base.l11_36_c
#print axioms GeocoqTranslate.Tarski.Base.l11_41_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_41_c
#print axioms GeocoqTranslate.Tarski.Base.not_conga_c
#print axioms GeocoqTranslate.Tarski.Base.not_conga_sym_c
#print axioms GeocoqTranslate.Tarski.Base.not_and_lta_c
#print axioms GeocoqTranslate.Tarski.Base.conga_preserves_lta_c
#print axioms GeocoqTranslate.Tarski.Base.lta_trans_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_sym_c
#print axioms GeocoqTranslate.Tarski.Base.acute_sym_c
#print axioms GeocoqTranslate.Tarski.Base.acute_col__out_c
#print axioms GeocoqTranslate.Tarski.Base.col_obtuse__bet_c
#print axioms GeocoqTranslate.Tarski.Base.out__acute_c
#print axioms GeocoqTranslate.Tarski.Base.bet__obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.l11_43_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_43_c
#print axioms GeocoqTranslate.Tarski.Base.acute_lea_acute_c
#print axioms GeocoqTranslate.Tarski.Base.lea_obtuse_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_1_a_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_2_a_c
#print axioms GeocoqTranslate.Tarski.Base.not_lta_and_conga_c
#print axioms GeocoqTranslate.Tarski.Base.conga_sym_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.conga_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lta_not_conga_c
#print axioms GeocoqTranslate.Tarski.Base.lta__lea_c
#print axioms GeocoqTranslate.Tarski.Base.nlta_c
#print axioms GeocoqTranslate.Tarski.Base.lea__nlta_c
#print axioms GeocoqTranslate.Tarski.Base.lta__nlea_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_1_b_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_2_b_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_2_c
#print axioms GeocoqTranslate.Tarski.Base.l11_44_2bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_46_c
#print axioms GeocoqTranslate.Tarski.Base.l11_47_c
#print axioms GeocoqTranslate.Tarski.Base.l11_49_c
#print axioms GeocoqTranslate.Tarski.Base.l11_50_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_50_2_c
#print axioms GeocoqTranslate.Tarski.Base.l11_51_c
#print axioms GeocoqTranslate.Tarski.Base.conga_distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l11_52_c
#print axioms GeocoqTranslate.Tarski.Base.l11_53_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_conga_obtuse__cong_conga2_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2__cong_conga2_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2__cong_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2__cong_3_c
#print axioms GeocoqTranslate.Tarski.Base.cong_lt_per2__lt_c
#print axioms GeocoqTranslate.Tarski.Base.cong_le_per2__le_c
#print axioms GeocoqTranslate.Tarski.Base.lt2_per2__lt_c
#print axioms GeocoqTranslate.Tarski.Base.le_lt_per2__lt_c
#print axioms GeocoqTranslate.Tarski.Base.le2_per2__le_c
#print axioms GeocoqTranslate.Tarski.Base.cong_lt_per2__lt_1_c
#print axioms GeocoqTranslate.Tarski.Base.symmetry_preserves_conga_c
#print axioms GeocoqTranslate.Tarski.Base.l11_57_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_orth_at__orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.col2_orth_at__orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.col_orth_at__orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_chara_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_orth__orth_c
#print axioms GeocoqTranslate.Tarski.Base.col2_orth__orth_c
#print axioms GeocoqTranslate.Tarski.Base.col_orth__orth_c
#print axioms GeocoqTranslate.Tarski.Base.orth_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.orth_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop_orth__orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_61_c
#print axioms GeocoqTranslate.Tarski.Base.l11_61_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_unicity_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_unicity_bis_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at2__eq_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop_orth_at__eq_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at__ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at__ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at__ncop_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_existence_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_63_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_63_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_3_c
#print axioms GeocoqTranslate.Tarski.Base.mid2_orth_at2__cong_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at2_tsp__ts_c
#print axioms GeocoqTranslate.Tarski.Base.orth_dec_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_dec_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.osp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.ts2__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.os_ts__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.os2__inangle_c
#print axioms GeocoqTranslate.Tarski.Base.acute_conga__acute_c
#print axioms GeocoqTranslate.Tarski.Base.acute_out2__acute_c
#print axioms GeocoqTranslate.Tarski.Base.conga_obtuse__obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_out2__obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lea__bet_c
#print axioms GeocoqTranslate.Tarski.Base.out_lea__out_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lta__lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea123456_lta__lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea456789_lta__lta_c
#print axioms GeocoqTranslate.Tarski.Base.acute_per__lta_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_per__lta_c
#print axioms GeocoqTranslate.Tarski.Base.acute_obtuse__lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea_in_angle_c
#print axioms GeocoqTranslate.Tarski.Base.acute_bet__obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.bet_obtuse__acute_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lea_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lta_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lea_total_c
#print axioms GeocoqTranslate.Tarski.Base.or_lta2_conga_c
#print axioms GeocoqTranslate.Tarski.Base.angle_partition_c
#print axioms GeocoqTranslate.Tarski.Base.acute_chara_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_chara_c
#print axioms GeocoqTranslate.Tarski.Base.conga__acute_c
#print axioms GeocoqTranslate.Tarski.Base.cong__acute_c
#print axioms GeocoqTranslate.Tarski.Base.nlta__lea_c
#print axioms GeocoqTranslate.Tarski.Base.nlea__lta_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_inequality_2_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_inequality_2_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_reverse_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_reverse_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.os3__lta_c
#print axioms GeocoqTranslate.Tarski.Base.bet_le__lt_c
#print axioms GeocoqTranslate.Tarski.Base.cong2__ncol_c
#print axioms GeocoqTranslate.Tarski.Base.cong4_cop2__eq_c
#print axioms GeocoqTranslate.Tarski.Base.t18_18_aux_c
#print axioms GeocoqTranslate.Tarski.Base.t18_18_c
#print axioms GeocoqTranslate.Tarski.Base.t18_19_c
#print axioms GeocoqTranslate.Tarski.Base.acute_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.acute_not_per_c
#print axioms GeocoqTranslate.Tarski.Base.angle_bisector_c
#print axioms GeocoqTranslate.Tarski.Base.reflectl__conga_c
#print axioms GeocoqTranslate.Tarski.Base.conga_cop_out_reflectl__out_c
#print axioms GeocoqTranslate.Tarski.Base.col_conga_cop_reflectl__col_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_cop2__col_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_cop2__col_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_conga__conga_c
#print axioms GeocoqTranslate.Tarski.Base.cop_inangle__ex_col_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.col_inangle2__out_c
#print axioms GeocoqTranslate.Tarski.Base.inangle2__lea_c
#print axioms GeocoqTranslate.Tarski.Base.conga_inangle_per__acute_c
#print axioms GeocoqTranslate.Tarski.Base.conga_inangle2_per__acute_c
#print axioms GeocoqTranslate.Tarski.Base.lta_os__ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet__suppa_c
#print axioms GeocoqTranslate.Tarski.Base.ex_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_sym_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_suppa__suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa2__conga456_c
#print axioms GeocoqTranslate.Tarski.Base.suppa2__conga123_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out__suppa_c
#print axioms GeocoqTranslate.Tarski.Base.bet_suppa__out_c
#print axioms GeocoqTranslate.Tarski.Base.out_suppa__bet_c
#print axioms GeocoqTranslate.Tarski.Base.per_suppa__per_c
#print axioms GeocoqTranslate.Tarski.Base.per2__suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa__per_c
#print axioms GeocoqTranslate.Tarski.Base.acute_suppa__obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_suppa__acute_c
#print axioms GeocoqTranslate.Tarski.Base.lea_suppa2__lea_c
#print axioms GeocoqTranslate.Tarski.Base.lta_suppa2__lta_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_dec_c
#print axioms GeocoqTranslate.Tarski.Base.acute_one_side_aux_c
#print axioms GeocoqTranslate.Tarski.Base.acute_one_side_aux0_c
#print axioms GeocoqTranslate.Tarski.Base.acute_cop_perp__one_side_c
#print axioms GeocoqTranslate.Tarski.Base.acute__not_obtuse_c
end GeocoqTranslate.Tarski.Base