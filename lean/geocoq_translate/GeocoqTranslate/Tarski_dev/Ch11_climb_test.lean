import GeocoqTranslate.Tarski_dev.Ch10

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
  exact ⟨A', (⟨C', (⟨D', (⟨F', ((let H28 := bet_neq21_neq H24 H6; (let H29 := bet_neq21__neq H20 H4; (let H30 := bet_neq21__neq H16 H2; (let H31 := bet_neq21__neq H12 H0; (let H32 := cong_diff_4_c b2 C' b4 b5 H6 H18; (let H33 := cong_diff_4_c b0 A' b4 b3 H4 H14; (let H34 := cong_diff_4_c b5 F' b1 b2 H2 H26; (let H35 := cong_diff_4_c b3 D' b1 b0 H0 H22; ⟨(⟨(Ne.symm H31), (⟨H0, (Or.inr H12)⟩)⟩), (⟨(⟨H2, (⟨(Ne.symm H30), (Or.inl H16)⟩)⟩), (⟨(⟨(Ne.symm H29), (⟨H4, (Or.inr H20)⟩)⟩), (⟨(⟨H6, (⟨(Ne.symm H28), (Or.inl H24)⟩)⟩), (⟨(cong_left_commutativity (l2_11 H12 (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_3421_c b3 D' b1 b0 H22))) (cong_symmetry (cong_symmetry (cong_right_commutativity H14))))), (⟨H27, (cong_left_commutativity (l2_11 (between_symmetry H16) H24 (cong_symmetry (cong_symmetry (cong_left_commutativity H18))) (cong_symmetry (cong_symmetry (cong_4312_c b5 F' b1 b2 H26)))))⟩)⟩)⟩)⟩)⟩)⟩)))))))))⟩)⟩)⟩)⟩

theorem l11_aux_c :
    ∀ (B A A' A0 E D D' D0 : Tpoint), Out B A A' → Out E D D' → Cong B A' E D' → Bet B A A0 → Bet E D D0 → Cong A A0 E D → Cong D D0 B A → Cong B A0 E D0 ∧ Cong A' A0 D' D0 := sorry

theorem l11_3_bis_c :
    ∀ (A B C D E F : Tpoint), (∃ (A' : Tpoint), ∃ (C' : Tpoint), ∃ (D' : Tpoint), ∃ (F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong_3 A' B C' D' E F') → CongA A B C D E F := sorry

theorem l11_4_1_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ (∀ (A' C' D' F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F') := by
  intro A B C D E F hCongA
  obtain ⟨hAB, hCB, hDE, hFE, _⟩ := hCongA
  obtain ⟨A0, C0, D0, F0, hOutBA0A, hOutBCC0, hOutED0D, hOutEFF0, hCong3⟩ := l11_3_c A B C D E F hCongA
  obtain ⟨hCongA0BD0E, hCongA0C0D0F0, hCongBC0EF0⟩ := hCong3
  refine ⟨hAB, hCB, hDE, hFE, ?_⟩
  rintro A1 C1 D1 F1 ⟨hOutBA1A, hOutBC1C, hOutED1D, hOutEF1F, hCongBA1ED1, hCongBC1EF1⟩
  have hOutBA1A0 : Out B A1 A0 := l6_7_c B A1 A A0 hOutBA1A (l6_6_c B A0 A hOutBA0A)
  have hOutED1D0 : Out E D1 D0 := l6_7_c E D1 D D0 hOutED1D (l6_6_c E D0 D hOutED0D)
  have hCongBA0ED0 : Cong B A0 E D0 := cong_right_commutativity_c B A0 D0 E (cong_left_commutativity_c A0 B D0 E hCongA0BD0E)
  have hCongA1A0D1D0 : Cong A1 A0 D1 D0 := out_cong_cong_c B A1 A0 E D1 D0 hOutBA1A0 hOutED1D0 hCongBA1ED1 hCongBA0ED0
  have hCongA0A1D0D1 : Cong A0 A1 D0 D1 := cong_right_commutativity_c A0 A1 D1 D0 (cong_left_commutativity_c A1 A0 D1 D0 hCongA1A0D1D0)
  have hColBA0A1 : Col B A0 A1 := col_permutation_5_c B A1 A0 (out_col_c B A1 A0 hOutBA1A0)
  have hA0B : B ≠ A0 := Ne.symm hOutBA0A.1
  have hCongA1C0D1F0 : Cong A1 C0 D1 F0 :=
    l4_16_c B A0 A1 C0 E D0 D1 F0 ⟨hColBA0A1, ⟨hCongBA0ED0, hCongBA1ED1, hCongA0A1D0D1⟩, hCongBC0EF0, hCongA0C0D0F0⟩ hA0B
  have hOutBC1C0 : Out B C1 C0 := l6_7_c B C1 C C0 hOutBC1C hOutBCC0
  have hOutEF1F0 : Out E F1 F0 := l6_7_c E F1 F F0 hOutEF1F hOutEFF0
  have hCongC1C0F1F0 : Cong C1 C0 F1 F0 := out_cong_cong_c B C1 C0 E F1 F0 hOutBC1C0 hOutEF1F0 hCongBC1EF1 hCongBC0EF0
  have hColBC0C1 : Col B C0 C1 := col_permutation_5_c B C1 C0 (out_col_c B C1 C0 hOutBC1C0)
  have hB0C : B ≠ C0 := Ne.symm hOutBCC0.1
  have hCongC0C1F0F1 : Cong C0 C1 F0 F1 :=
    cong_right_commutativity_c C0 C1 F1 F0 (cong_left_commutativity_c C1 C0 F1 F0 hCongC1C0F1F0)
  have hCongC0A1F0D1 : Cong C0 A1 F0 D1 :=
    cong_right_commutativity_c C0 A1 D1 F0 (cong_left_commutativity_c A1 C0 D1 F0 hCongA1C0D1F0)
  have hCongC1A1F1D1 : Cong C1 A1 F1 D1 :=
    l4_16_c B C0 C1 A1 E F0 F1 D1
      ⟨hColBC0C1, ⟨hCongBC0EF0, hCongBC1EF1, hCongC0C1F0F1⟩, hCongBA1ED1, hCongC0A1F0D1⟩ hB0C
  exact cong_right_commutativity_c A1 C1 D1 F1 (cong_left_commutativity_c C1 A1 F1 D1 hCongC1A1F1D1)

theorem l11_4_2_c :
    ∀ (A B C D E F : Tpoint), (A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ (∀ (A' C' D' F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong B A' E D' ∧ Cong B C' E F' → Cong A' C' D' F')) → CongA A B C D E F := sorry
theorem conga_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → CongA A B C A B C := sorry
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
    ∀ (A B C D E F A' C' D' F' : Tpoint), CongA A B C D E F → Out B A' A → Out B C' C → Out E D' D → Out E F' F → CongA A' B C' D' E F' := by
  intro A B C D E F A' C' D' F' hCongA hOutA' hOutC' hOutD' hOutF'
  obtain ⟨hAB, hCB, hDE, hFE, hBound⟩ := l11_4_1_c A B C D E F hCongA
  apply l11_4_2_c A' B C' D' E F'
  refine ⟨hOutA'.1, hOutC'.1, hOutD'.1, hOutF'.1, ?_⟩
  rintro A1 C1 D1 F1 ⟨h1, h2, h3, h4, h5, h6⟩
  exact hBound A1 C1 D1 F1 ⟨l6_7_c B A1 A' A h1 hOutA', l6_7_c B C1 C' C h2 hOutC', l6_7_c E D1 D' D h3 hOutD', l6_7_c E F1 F' F h4 hOutF', h5, h6⟩

theorem out2__conga_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → CongA A B C A' B C' := sorry
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
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → C ≠ B → Cong_3 A B C A' B' C' → CongA A B C A' B' C' := sorry
theorem cong3_conga2_c :
    ∀ (A B C A' B' C' A'' B'' C'' : Tpoint), Cong_3 A B C A' B' C' → CongA A B C A'' B'' C'' → CongA A' B' C' A'' B'' C'' := sorry

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
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → A' ≠ B' := sorry
theorem conga_diff56_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → C' ≠ B' := sorry
theorem conga_trans_c :
    ∀ (A B C A' B' C' A'' B'' C'' : Tpoint), CongA A B C A' B' C' → CongA A' B' C' A'' B'' C'' → CongA A B C A'' B'' C'' := sorry

theorem conga_pseudo_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → CongA A B C C B A := sorry

theorem conga_trivial_1_c :
    ∀ (A B C D : Tpoint), A ≠ B → C ≠ D → CongA A B A C D C := sorry

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
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA A B C F E D := sorry
theorem conga_left_comm_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA C B A D E F := sorry
theorem conga_comm_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA C B A F E D := sorry
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
    ∀ (A B C A' C' : Tpoint), Bet A B A' → A ≠ B → A' ≠ B → Bet C B C' → B ≠ C → B ≠ C' → CongA A B C A' B C' := sorry
theorem l11_16_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → A ≠ B → C ≠ B → Per A' B' C' → A' ≠ B' → C' ≠ B' → CongA A B C A' B' C' := sorry

theorem l11_17_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → CongA A B C A' B' C' → Per A' B' C' := sorry

theorem l11_18_1_c :
    ∀ (A B C D : Tpoint), Bet C B D → B ≠ C → B ≠ D → A ≠ B → Per A B C → CongA A B C A B D := sorry
theorem l11_18_2_c :
    ∀ (A B C D : Tpoint), Bet C B D → CongA A B C A B D → Per A B C := sorry

theorem cong3_preserves_out_c :
    ∀ (A B C A' B' C' : Tpoint), Out A B C → Cong_3 A B C A' B' C' → Out A' B' C' := sorry

theorem l11_21_a_c :
    ∀ (A B C A' B' C' : Tpoint), Out B A C → CongA A B C A' B' C' → Out B' A' C' := sorry

theorem l11_21_b_c :
    ∀ (A B C A' B' C' : Tpoint), Out B A C → Out B' A' C' → CongA A B C A' B' C' := sorry
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
    ∀ (A B C A' B' P : Tpoint), A ≠ B → A ≠ C → B ≠ C → A' ≠ B' → ¬ Col A' B' P → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ (OS A' B' C' P ∨ Col A' B' C') := sorry
theorem ex_conga_ts_c :
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → ∃ C' : Tpoint, CongA A B C A' B' C' ∧ TS A' B' C' P := sorry

theorem l11_15_c :
    ∀ (A B C D E P : Tpoint), ¬ Col A B C → ¬ Col D E P → ∃ (F : Tpoint), CongA A B C D E F ∧ OS E D F P ∧ (∀ (F1 F2 : Tpoint), ((CongA A B C D E F1 ∧ OS E D F1 P) ∧ (CongA A B C D E F2 ∧ OS E D F2 P)) → Out E F1 F2) := sorry

theorem l11_19_c :
    ∀ (A B P1 P2 : Tpoint), Per A B P1 → Per A B P2 → OS A B P1 P2 → Out B P1 P2 := sorry

theorem l11_22_bet_c :
    ∀ (A B C P A' B' C' P' : Tpoint), Bet A B C → TS P' B' A' C' → CongA A B P A' B' P' ∧ CongA P B C P' B' C' → Bet A' B' C' := sorry

theorem l11_22a_c :
    ∀ (A B C P A' B' C' P' : Tpoint), TS B P A C ∧ TS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := sorry

theorem l11_22b_c :
    ∀ (A B C P A' B' C' P' : Tpoint), OS B P A C ∧ OS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := sorry
theorem l11_22_c :
    ∀ (A B C P A' B' C' P' : Tpoint), ((TS B P A C ∧ TS B' P' A' C') ∨ (OS B P A C ∧ OS B' P' A' C')) ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := sorry
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
    ∀ (A B C P : Tpoint), C ≠ B → Out B A P → InAngle P A B C := sorry
theorem inangle1123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle A A B C := sorry
theorem out341__inangle_c :
    ∀ (A B C P : Tpoint), A ≠ B → Out B C P → InAngle P A B C := sorry
theorem inangle3123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle C A B C := sorry
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
    ∀ (A B A' : Tpoint), ∃ (B' : Tpoint), Cong A' B' A B := sorry

theorem angle_construction_3_c :
    ∀ (A B C A' B' : Tpoint), A ≠ B → C ≠ B → A' ≠ B' → ∃ (C' : Tpoint), CongA A B C A' B' C' := sorry
theorem l11_28_c :
    ∀ (A B C D A' B' C' : Tpoint), Cong_3 A B C A' B' C' → Col A C D → ∃ (D' : Tpoint), Cong A D A' D' ∧ Cong B D B' D' ∧ Cong C D C' D' := sorry

theorem bet_conga__bet_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A B C → CongA A B C A' B' C' → Bet A' B' C' := sorry
theorem in_angle_one_side_c :
    ∀ (A B C P : Tpoint), ¬ Col A B C → ¬ Col B A P → InAngle P A B C → OS A B P C := sorry

theorem inangle_one_side_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q := sorry

theorem inangle_one_side2_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → ¬ Col C B P → ¬ Col C B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q ∧ OS C B P Q := sorry
theorem col_conga_col_c :
    ∀ (A B C D E F : Tpoint), Col A B C → CongA A B C D E F → Col D E F := sorry
theorem ncol_conga_ncol_c :
    ∀ (A B C D E F : Tpoint), ¬ Col A B C → CongA A B C D E F → ¬ Col D E F := sorry
theorem angle_construction_4_c :
    ∀ (A B C A' B' P : Tpoint), A ≠ B → C ≠ B → A' ≠ B' → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ Coplanar A' B' C' P := sorry

theorem lea_distincts_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := sorry
theorem l11_29_a_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F := sorry

theorem in_angle_line_c :
    ∀ (A B C P : Tpoint), P ≠ B → A ≠ B → C ≠ B → Bet A B C → InAngle P A B C :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b5, (⟨b6, (⟨b4, (⟨b1, (⟨b7, (Or.inl rfl)⟩)⟩)⟩)⟩)⟩

theorem l11_29_b_c :
    ∀ (A B C D E F : Tpoint), (∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F) → LeA A B C D E F := sorry

theorem bet_in_angle_bet_c :
    ∀ (A B C P : Tpoint), Bet A B P → InAngle P A B C → Bet A B C := sorry

theorem lea_line_c :
    ∀ (A B C P : Tpoint), Bet A B P → LeA A B P A B C → Bet A B C := sorry
theorem eq_conga_out_c :
    ∀ (A B D E F : Tpoint), CongA A B A D E F → Out E D F := sorry
theorem conga_ex_cong3_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → ∃ (AA : Tpoint), ∃ (CC : Tpoint), Out B A AA → Out B C CC → Cong_3 AA B CC A' B' C' := sorry

theorem conga_preserves_in_angle_c :
    ∀ (A B C I A' B' C' I' : Tpoint), CongA A B C A' B' C' → CongA A B I A' B' I' → InAngle I A B C → OS A' B' I' C' → InAngle I' A' B' C' := sorry

theorem l11_30_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), LeA A B C D E F → CongA A B C A' B' C' → CongA D E F D' E' F' → LeA A' B' C' D' E' F' := sorry

theorem l11_31_1_c :
    ∀ (A B C D E F : Tpoint), Out B A C → D ≠ E → F ≠ E → LeA A B C D E F := sorry
theorem l11_31_2_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → C ≠ B → D ≠ E → F ≠ E → Bet D E F → LeA A B C D E F := sorry

theorem lea_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → LeA A B C A B C := sorry
theorem conga__lea_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA A B C D E F := sorry
theorem conga__lea456123_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA D E F A B C := sorry
theorem lea_left_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA C B A D E F := sorry
theorem lea_right_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA A B C F E D := sorry
theorem lea_comm_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA C B A F E D := sorry
theorem lta_left_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA C B A D E F := sorry
theorem lta_right_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA A B C F E D := sorry
theorem lta_comm_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LtA C B A F E D := sorry
theorem lea_out4__lea_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), LeA A B C D E F → Out B A A' → Out B C C' → Out E D D' → Out E F F' → LeA A' B C' D' E F' := sorry
theorem lea121345_c :
    ∀ (A B C D E : Tpoint), A ≠ B → C ≠ D → D ≠ E → LeA A B A C D E := sorry
theorem inangle__lea_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA A B P A B C := sorry

theorem inangle__lea_1_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA P B C A B C := sorry
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
    ∀ (A B C X Y Z : Tpoint), Col X Y Z → LtA A B C X Y Z → Bet X Y Z := sorry
theorem col_lta__out_c :
    ∀ (A B C X Y Z : Tpoint), Col A B C → LtA A B C X Y Z → Out B A C := sorry

theorem lta_distincts_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ D ≠ F := sorry

theorem gta_distincts_c :
    ∀ (A B C D E F : Tpoint), GtA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧ A ≠ C := sorry
theorem acute_distincts_c :
    ∀ (A B C : Tpoint), Acute A B C → A ≠ B ∧ C ≠ B := sorry
theorem obtuse_distincts_c :
    ∀ (A B C : Tpoint), Obtuse A B C → A ≠ B ∧ C ≠ B ∧ A ≠ C := sorry
theorem two_sides_in_angle_c :
    ∀ (A B C P P' : Tpoint), B ≠ P' → TS B P A C → Bet P B P' → InAngle P A B C ∨ InAngle P' A B C := sorry

theorem in_angle_reverse_c :
    ∀ (A B A' C D : Tpoint), A' ≠ B → Bet A B A' → InAngle C A B D → InAngle D A' B C := sorry

theorem in_angle_trans2_c :
    ∀ (A B C D E : Tpoint), InAngle C A B D → InAngle D A B E → InAngle D C B E := sorry
theorem l11_36_c :
    ∀ (A B C D E F A' D' : Tpoint), A ≠ B → A' ≠ B → D ≠ E → D' ≠ E → Bet A B A' → Bet D E D' → (LeA A B C D E F ↔ LeA D' E F A' B C) := sorry

theorem l11_41_aux_c :
    ∀ (A B C D : Tpoint), ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D := sorry

theorem l11_41_c :
    ∀ (A B C D : Tpoint), ¬ Col A B C → Bet B A D → A ≠ D → LtA A C B C A D ∧ LtA A B C C A D := sorry

theorem not_conga_c :
    ∀ (A B C A' B' C' D E F : Tpoint), CongA A B C A' B' C' → ¬ CongA A B C D E F → ¬ CongA A' B' C' D E F := sorry
theorem not_conga_sym_c :
    ∀ (A B C D E F : Tpoint), ¬ CongA A B C D E F → ¬ CongA D E F A B C := sorry
theorem not_and_lta_c :
    ∀ (A B C D E F : Tpoint), ¬ (LtA A B C D E F ∧ LtA D E F A B C) := sorry
theorem conga_preserves_lta_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), CongA A B C A' B' C' → CongA D E F D' E' F' → LtA A B C D E F → LtA A' B' C' D' E' F' := sorry
theorem lta_trans_c :
    ∀ (A B C A1 B1 C1 A2 B2 C2 : Tpoint), LtA A B C A1 B1 C1 → LtA A1 B1 C1 A2 B2 C2 → LtA A B C A2 B2 C2 := sorry
theorem obtuse_sym_c :
    ∀ (A B C : Tpoint), Obtuse A B C → Obtuse C B A := sorry
theorem acute_sym_c :
    ∀ (A B C : Tpoint), Acute A B C → Acute C B A := sorry
theorem acute_col__out_c :
    ∀ (A B C : Tpoint), Col A B C → Acute A B C → Out B A C := sorry
theorem col_obtuse__bet_c :
    ∀ (A B C : Tpoint), Col A B C → Obtuse A B C → Bet A B C := sorry
theorem out__acute_c :
    ∀ (A B C : Tpoint), Out B A C → Acute A B C := sorry
theorem bet__obtuse_c :
    ∀ (A B C : Tpoint), Bet A B C → A ≠ B → B ≠ C → Obtuse A B C := sorry
theorem l11_43_aux_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → (Per B A C ∨ Obtuse B A C) → Acute A B C := sorry

theorem l11_43_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → (Per B A C ∨ Obtuse B A C) → Acute A B C ∧ Acute A C B := sorry
theorem acute_lea_acute_c :
    ∀ (A B C D E F : Tpoint), Acute D E F → LeA A B C D E F → Acute A B C := sorry

theorem lea_obtuse_obtuse_c :
    ∀ (A B C D E F : Tpoint), Obtuse D E F → LeA D E F A B C → Obtuse A B C := sorry

theorem l11_44_1_a_c :
    ∀ (A B C : Tpoint), A ≠ B → A ≠ C → Cong B A B C → CongA B A C B C A := sorry
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
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' ↔ CongA A' B' C' A B C := sorry
theorem conga_dec_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F ∨ ¬ CongA A B C D E F := sorry

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
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ¬ LtA D E F A B C := sorry
theorem lta__nlea_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → ¬ LeA D E F A B C := sorry
theorem l11_44_1_b_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → CongA B A C B C A → Cong B A B C := sorry
theorem l11_44_2_b_c :
    ∀ (A B C : Tpoint), LtA B A C B C A → Lt B C B A := sorry
theorem l11_44_1_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → (CongA B A C B C A ↔ Cong B A B C) := sorry
theorem l11_44_2_c :
    ∀ (A B C : Tpoint), ¬ Col A B C → (LtA B A C B C A ↔ Lt B C B A) := sorry
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
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → CongA A B C D E F ∧ A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := sorry

theorem l11_52_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → Cong A C A' C' → Cong B C B' C' → Le B C A C → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry

theorem l11_53_c :
    ∀ (A B C D : Tpoint), Per D C B → C ≠ D → A ≠ B → B ≠ C → Bet A B C → LtA C A D C B D ∧ Lt B D A D := sorry

theorem cong2_conga_obtuse__cong_conga2_c :
    ∀ (A B C A' B' C' : Tpoint), Obtuse A B C → CongA A B C A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry
theorem cong2_per2__cong_conga2_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ B → B ≠ C → Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry
theorem cong2_per2__cong_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' := sorry

theorem cong2_per2__cong_3_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong_3 A B C A' B' C' := sorry
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
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Lt A B A' B' → Cong A C A' C' → Lt B' C' B C := sorry

theorem symmetry_preserves_conga_c :
    ∀ (A B C A' B' C' M : Tpoint), A ≠ B → C ≠ B → Midpoint M A A' → Midpoint M B B' → Midpoint M C C' → CongA A B C A' B' C' := sorry
theorem l11_57_c :
    ∀ (A B C A' B' C' : Tpoint), OS A A' B B' → Per B A A' → Per B' A' A → OS A A' C C' → Per C A A' → Per C' A' A → CongA B A C B' A' C' := sorry

theorem cop3_orth_at__orth_at_c :
    ∀ (A B C D E F U V X : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth_at X A B C U V → Orth_at X D E F U V := sorry

theorem col2_orth_at__orth_at_c :
    ∀ (A B C P Q U V X : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth_at X A B C P Q → Orth_at X A B C U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨x, x0⟩ := b11
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨x, (⟨b8, (⟨x3, (⟨(col3_c b3 b4 b5 b6 b7 x1 b9 b10 x5), (fun D W HD HW => x6 D W HD (colx_c b5 b6 W b3 b4 b8 b9 b10 HW))⟩)⟩)⟩)⟩

theorem col_orth_at__orth_at_c :
    ∀ (A B C U V W X : Tpoint), U ≠ W → Col U V W → Orth_at X A B C U V → Orth_at X A B C U W := sorry
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
    ∀ (A B C P X : Tpoint), Orth_at X A B C X P ↔ ¬ Col A B C ∧ X ≠ P ∧ Coplanar A B C X ∧ (∀ (D : Tpoint), Coplanar A B C D → Per D X P) := sorry

theorem cop3_orth__orth_c :
    ∀ (A B C D E F U V : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth A B C U V → Orth D E F U V := sorry
theorem col2_orth__orth_c :
    ∀ (A B C P Q U V : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth A B C P Q → Orth A B C U V := sorry
theorem col_orth__orth_c :
    ∀ (A B C U V W : Tpoint), U ≠ W → Col U V W → Orth A B C U V → Orth A B C U W := sorry
theorem orth_symmetry_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V → Orth A B C V U := sorry
theorem orth_distincts_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ U ≠ V := sorry
theorem col_cop_orth__orth_at_c :
    ∀ (A B C U V X : Tpoint), Orth A B C U V → Coplanar A B C X → Col U V X → Orth_at X A B C U V := sorry

theorem l11_60_aux_c :
    ∀ (A B C D P Q : Tpoint), ¬ Col A B C → Cong A P A Q → Cong B P B Q → Cong C P C Q → Coplanar A B C D → Cong D P D Q := sorry

theorem l11_60_c :
    ∀ (A B C D E P : Tpoint), ¬ Col A B C → Per A D P → Per B D P → Per C D P → Coplanar A B C E → Per E D P := sorry
theorem l11_60_bis_c :
    ∀ (A B C D P : Tpoint), ¬ Col A B C → D ≠ P → Coplanar A B C D → Per A D P → Per B D P → Per C D P → Orth_at D A B C D P := sorry
theorem l11_61_c :
    ∀ (A B C A' B' C' : Tpoint), A ≠ A' → A ≠ B → A ≠ C → Coplanar A A' B B' → Per B A A' → Per B' A' A → Coplanar A A' C C' → Per C A A' → Per B A C → Per B' A' C' := sorry
theorem l11_61_bis_c :
    ∀ (A B C D E P Q : Tpoint), Orth_at D A B C D P → Perp D E E Q → Coplanar A B C E → Coplanar D E P Q → Orth_at E A B C E Q := sorry

theorem l11_62_unicity_c :
    ∀ (A B C D D' P : Tpoint), Coplanar A B C D → Coplanar A B C D' → (∀ (E : Tpoint), Coplanar A B C E → Per E D P) → (∀ (E : Tpoint), Coplanar A B C E → Per E D' P) → D = D' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  l8_7_c b5 b3 b4 (l8_2_c b4 b3 b5 (b8 b4 b7)) (l8_2_c b3 b4 b5 (b9 b3 b6))

theorem l11_62_unicity_bis_c :
    ∀ (A B C U X Y : Tpoint), Orth_at X A B C X U → Orth_at Y A B C Y U → X = Y := sorry
theorem orth_at2__eq_c :
    ∀ (A B C U V X Y : Tpoint), Orth_at X A B C U V → Orth_at Y A B C U V → X = Y := sorry
theorem col_cop_orth_at__eq_c :
    ∀ (A B C U V X Y : Tpoint), Orth_at X A B C U V → Coplanar A B C Y → Col U V Y → X = Y := sorry
theorem orth_at__ncop1_c :
    ∀ (A B C U V X : Tpoint), U ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C U := sorry
theorem orth_at__ncop2_c :
    ∀ (A B C U V X : Tpoint), V ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C V := sorry
theorem orth_at__ncop_c :
    ∀ (A B C P X : Tpoint), Orth_at X A B C X P → ¬ Coplanar A B C P := sorry
theorem l11_62_existence_c :
    ∀ (A B C P : Tpoint), ∃ (D : Tpoint), Coplanar A B C D ∧ ∀ (E : Tpoint), Coplanar A B C E → Per E D P := sorry

theorem l11_62_existence_bis_c :
    ∀ (A B C P : Tpoint), ¬ Coplanar A B C P → ∃ (X : Tpoint), Orth_at X A B C X P := sorry

theorem l11_63_aux_c :
    ∀ (A B C D E P : Tpoint), Coplanar A B C D → D ≠ E → Orth_at E A B C E P → ∃ (Q : Tpoint), OS D E P Q ∧ Orth A B C D Q := sorry

theorem l11_63_existence_c :
    ∀ (A B C D P : Tpoint), Coplanar A B C D → ¬ Coplanar A B C P → ∃ (Q : Tpoint), Orth A B C D Q := sorry

theorem l8_21_3_c :
    ∀ (A B C D X : Tpoint), Coplanar A B C D → ¬ Coplanar A B C X → ∃ (P T : Tpoint), Orth A B C D P ∧ Coplanar A B C T ∧ Bet X T P := sorry

theorem mid2_orth_at2__cong_c :
    ∀ (A B C X Y P Q P' Q' : Tpoint), Orth_at X A B C X P → Orth_at Y A B C Y Q → Midpoint X P P' → Midpoint Y Q Q' → Cong P Q P' Q' := sorry

theorem orth_at2_tsp__ts_c :
    ∀ (A B C X Y P Q : Tpoint), P ≠ Q → Orth_at P A B C P X → Orth_at Q A B C Q Y → TSP A B C X Y → TS P Q X Y := sorry

theorem orth_dec_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V ∨ ¬ Orth A B C U V := sorry

theorem orth_at_dec_c :
    ∀ (A B C U V X : Tpoint), Orth_at X A B C U V ∨ ¬ Orth_at X A B C U V := sorry

theorem tsp_dec_c :
    ∀ (A B C X Y : Tpoint), TSP A B C X Y ∨ ¬ TSP A B C X Y := sorry

theorem osp_dec_c :
    ∀ (A B C X Y : Tpoint), OSP A B C X Y ∨ ¬ OSP A B C X Y := sorry

theorem ts2__inangle_c :
    ∀ (A B C P : Tpoint), TS A C B P → TS B P A C → InAngle P A B C := sorry

theorem os_ts__inangle_c :
    ∀ (A B C P : Tpoint), TS B P A C → OS B A C P → InAngle P A B C := sorry

theorem os2__inangle_c :
    ∀ (A B C P : Tpoint), OS B A C P → OS B C A P → InAngle P A B C := sorry
theorem acute_conga__acute_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → CongA A B C D E F → Acute D E F := sorry
theorem acute_out2__acute_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Acute A B C → Acute A' B C' := sorry
theorem conga_obtuse__obtuse_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → CongA A B C D E F → Obtuse D E F := sorry
theorem obtuse_out2__obtuse_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Obtuse A B C → Obtuse A' B C' := sorry
theorem bet_lea__bet_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → LeA A B C D E F → Bet D E F := sorry
theorem out_lea__out_c :
    ∀ (A B C D E F : Tpoint), Out E D F → LeA A B C D E F → Out B A C := sorry
theorem bet2_lta__lta_c :
    ∀ (A B C D E F A' D' : Tpoint), LtA A B C D E F → Bet A B A' → A' ≠ B → Bet D E D' → D' ≠ E → LtA D' E F A' B C := sorry

theorem lea123456_lta__lta_c :
    ∀ (A B C D E F G H I : Tpoint), LeA A B C D E F → LtA D E F G H I → LtA A B C G H I := sorry

theorem lea456789_lta__lta_c :
    ∀ (A B C D E F G H I : Tpoint), LtA A B C D E F → LeA D E F G H I → LtA A B C G H I := sorry

theorem acute_per__lta_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → D ≠ E → E ≠ F → Per D E F → LtA A B C D E F := sorry
theorem obtuse_per__lta_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → D ≠ E → E ≠ F → Per D E F → LtA D E F A B C := sorry
theorem acute_obtuse__lta_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → Obtuse D E F → LtA A B C D E F := sorry
theorem lea_in_angle_c :
    ∀ (A B C P : Tpoint), LeA A B P A B C → OS A B C P → InAngle P A B C := sorry

theorem acute_bet__obtuse_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Acute A B C → Obtuse A' B C := sorry

theorem bet_obtuse__acute_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Obtuse A B C → Acute A' B C := sorry

theorem inangle_dec_c :
    ∀ (A B C P : Tpoint), InAngle P A B C ∨ ¬ InAngle P A B C := sorry

theorem lea_dec_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F ∨ ¬ LeA A B C D E F := sorry

theorem lta_dec_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F ∨ ¬ LtA A B C D E F := sorry

theorem lea_total_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → D ≠ E → E ≠ F → LeA A B C D E F ∨ LeA D E F A B C := sorry

theorem or_lta2_conga_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → C ≠ B → D ≠ E → F ≠ E → LtA A B C D E F ∨ LtA D E F A B C ∨ CongA A B C D E F := sorry
theorem angle_partition_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Acute A B C ∨ Per A B C ∨ Obtuse A B C := sorry

theorem acute_chara_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → B ≠ A' → (Acute A B C ↔ LtA A B C A' B C) := sorry

theorem obtuse_chara_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → B ≠ A' → (Obtuse A B C ↔ LtA A' B C A B C) := sorry

theorem conga__acute_c :
    ∀ (A B C : Tpoint), CongA A B C A C B → Acute A B C := sorry
theorem cong__acute_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Cong A B A C → Acute A B C := sorry
theorem nlta__lea_c :
    ∀ (A B C D E F : Tpoint), ¬ LtA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LeA D E F A B C := sorry
theorem nlea__lta_c :
    ∀ (A B C D E F : Tpoint), ¬ LeA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LtA D E F A B C := sorry

theorem triangle_strict_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → ¬ Bet A B C → Lt A C A D := sorry

theorem triangle_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → Le A C A D := sorry
theorem triangle_strict_inequality_2_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → ¬ Bet A B C → Lt A C A' C' := sorry
theorem triangle_inequality_2_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → Le A C A' C' := sorry
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
    ∀ (A B : Tpoint), A ≠ B → Acute A B A := sorry

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
    ∀ (A B C P P' : Tpoint), ¬ Out B A C → CongA P B A P B C → CongA P' B A P' B C → Coplanar A B P P' → Coplanar B C P P' → Col B P P' := sorry

theorem conga2_cop2__col_1_c :
    ∀ (A B C P P' : Tpoint), ¬ Col A B C → CongA P B A P B C → CongA P' B A P' B C → Coplanar A B C P → Coplanar A B C P' → Col B P P' := sorry
theorem col_conga__conga_c :
    ∀ (A B C P P' : Tpoint), CongA P B A P B C → Col B P P' → B ≠ P' → CongA P' B A P' B C := sorry
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
    ∀ (A B C A' : Tpoint), A ≠ B → B ≠ C → B ≠ A' → Bet A B A' → SuppA A B C C B A' := sorry
theorem ex_suppa_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → ∃ (D E F : Tpoint), SuppA A B C D E F := sorry
theorem suppa_distincts_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → A ≠ B ∧ B ≠ C ∧ D ≠ E ∧ E ≠ F := sorry
theorem suppa_right_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA A B C F E D := sorry

theorem suppa_left_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA C B A D E F := sorry

theorem suppa_comm_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA C B A F E D := sorry
theorem suppa_sym_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F → SuppA D E F A B C := sorry

theorem conga2_suppa__suppa_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), CongA A B C A' B' C' → CongA D E F D' E' F' → SuppA A B C D E F → SuppA A' B' C' D' E' F' := sorry

theorem suppa2__conga456_c :
    ∀ (A B C D E F D' E' F' : Tpoint), SuppA A B C D E F → SuppA A B C D' E' F' → CongA D E F D' E' F' := sorry
theorem suppa2__conga123_c :
    ∀ (A B C D E F A' B' C' : Tpoint), SuppA A B C D E F → SuppA A' B' C' D E F → CongA A B C A' B' C' := sorry
theorem bet_out__suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → Bet A B C → Out E D F → SuppA A B C D E F := sorry
theorem bet_suppa__out_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → SuppA A B C D E F → Out E D F := sorry
theorem out_suppa__bet_c :
    ∀ (A B C D E F : Tpoint), Out B A C → SuppA A B C D E F → Bet D E F := sorry
theorem per_suppa__per_c :
    ∀ (A B C D E F : Tpoint), Per A B C → SuppA A B C D E F → Per D E F := sorry
theorem per2__suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → D ≠ E → E ≠ F → Per A B C → Per D E F → SuppA A B C D E F := sorry
theorem suppa__per_c :
    ∀ (A B C : Tpoint), SuppA A B C A B C → Per A B C := sorry
theorem acute_suppa__obtuse_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → SuppA A B C D E F → Obtuse D E F := sorry
theorem obtuse_suppa__acute_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → SuppA A B C D E F → Acute D E F := sorry
theorem lea_suppa2__lea_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), SuppA A B C A' B' C' → SuppA D E F D' E' F' → LeA A B C D E F → LeA D' E' F' A' B' C' := sorry
theorem lta_suppa2__lta_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), SuppA A B C A' B' C' → SuppA D E F D' E' F' → LtA A B C D E F → LtA D' E' F' A' B' C' := sorry
theorem suppa_dec_c :
    ∀ (A B C D E F : Tpoint), SuppA A B C D E F ∨ ¬ SuppA A B C D E F := sorry

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
