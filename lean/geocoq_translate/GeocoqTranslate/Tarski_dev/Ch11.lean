import GeocoqTranslate.Tarski_dev.Ch10Line2Extra
import GeocoqTranslate.Tarski_dev.TarskiFinish

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
  exact ⟨A', (⟨C', (⟨D', (⟨F', ((let H28 := bet_neq21_neq H24 H6; (let H29 := bet_neq21_neq H20 H4; (let H30 := bet_neq21_neq H16 H2; (let H31 := bet_neq21_neq H12 H0; (let H32 := cong_diff_4_c b2 C' b4 b5 H6 H18; (let H33 := cong_diff_4_c b0 A' b4 b3 H4 H14; (let H34 := cong_diff_4_c b5 F' b1 b2 H2 H26; (let H35 := cong_diff_4_c b3 D' b1 b0 H0 H22; ⟨(⟨(Ne.symm H31), (⟨H0, (Or.inr H12)⟩)⟩), (⟨(⟨H2, (⟨(Ne.symm H30), (Or.inl H16)⟩)⟩), (⟨(⟨(Ne.symm H29), (⟨H4, (Or.inr H20)⟩)⟩), (⟨(⟨H6, (⟨(Ne.symm H28), (Or.inl H24)⟩)⟩), (⟨(cong_left_commutativity (l2_11 H12 (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_3421_c b3 D' b1 b0 H22))) (cong_symmetry (cong_symmetry (cong_right_commutativity H14))))), (⟨H27, (cong_left_commutativity (l2_11 (between_symmetry H16) H24 (cong_symmetry (cong_symmetry (cong_left_commutativity H18))) (cong_symmetry (cong_symmetry (cong_4312_c b5 F' b1 b2 H26)))))⟩)⟩)⟩)⟩)⟩)⟩)))))))))⟩)⟩)⟩)⟩
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
      · have H20 := cong_preserves_bet_c b0 b2 b3 b4 b6 b7 H19 b10 H7 (⟨H10, (⟨((let H20 := bet_neq21_neq b11 H6; (let H21 := bet_neq21_neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H21))))), (l5_1 (Ne.symm H8) H16 b12)⟩)⟩)
        exact cong_commutativity (l4_3 (between_symmetry H19) (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
      · have H20 := cong_preserves_bet_c b0 b3 b2 b4 b7 b6 H19 H7 b10 (⟨((let H20 := bet_neq21_neq b11 H6; (let H21 := bet_neq21_neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H21))))), (⟨((let H20 := bet_neq21_neq b11 H6; (let H21 := bet_neq21_neq b12 H8; (let H22 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H23 := cong_diff_4_c b5 b7 b0 b1 H12 b14; H10))))), (l5_1 (Ne.symm H8) b12 H16)⟩)⟩)
        exact l4_3 (between_symmetry H19) (between_symmetry H20) (cong_symmetry (cong_symmetry (cong_commutativity b10))) (cong_symmetry (cong_symmetry (cong_commutativity H7)))
    · exact cong_commutativity (l4_3 (between_symmetry (between_exchange4 H17 b11)) (between_symmetry (cong_preserves_bet_c b0 b2 b3 b4 b6 b7 (between_exchange4 H17 b11) b10 H7 (⟨H10, (⟨((let H18 := bet_neq21_neq b11 H6; (let H19 := bet_neq21_neq b12 H8; (let H20 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H21 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H19))))), (l5_1 (Ne.symm H8) H16 b12)⟩)⟩))) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
  · rcases H15 with H17 | H17
    · exact cong_commutativity (l4_3 (between_symmetry (cong_preserves_bet_c b4 b6 b7 b0 b2 b3 (between_exchange4 H16 b12) (cong_symmetry b10) (cong_symmetry H7) (⟨H14, (⟨((let H18 := bet_neq21_neq b11 H6; (let H19 := bet_neq21_neq b12 H8; (let H20 := cong_diff_4_c b1 b3 b4 b5 H8 b13; (let H21 := cong_diff_4_c b5 b7 b0 b1 H12 b14; Ne.symm H18))))), (l5_1 (Ne.symm H6) H17 b11)⟩)⟩))) (between_symmetry (between_exchange4 H16 b12)) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))
    · exact cong_commutativity (l4_3 (between_symmetry (between_exchange4 H17 b11)) (between_symmetry (between_exchange4 H16 b12)) (cong_symmetry (cong_symmetry (cong_commutativity H7))) (cong_symmetry (cong_symmetry (cong_commutativity b10))))))⟩
theorem l11_3_bis_c :
    ∀ (A B C D E F : Tpoint), (∃ (A' : Tpoint), ∃ (C' : Tpoint), ∃ (D' : Tpoint), ∃ (F' : Tpoint), Out B A' A ∧ Out B C' C ∧ Out E D' D ∧ Out E F' F ∧ Cong_3 A' B C' D' E F') → CongA A B C D E F := by
  intro A B C D E F h
  obtain ⟨A', C', D', F', hA, hC, hD, hF, hCong3⟩ := h
  obtain ⟨A0, hBetA0, hCongA0⟩ := segment_construction B A E D
  obtain ⟨C0, hBetC0, hCongC0⟩ := segment_construction B C E F
  obtain ⟨D0, hBetD0, hCongD0⟩ := segment_construction E D B A
  obtain ⟨F0, hBetF0, hCongF0⟩ := segment_construction E F B C
  refine ⟨hA.2.1, hC.2.1, hD.2.1, hF.2.1, A0, C0, D0, F0,
    hBetA0, hCongA0, hBetC0, hCongC0, hBetD0, hCongD0, hBetF0, hCongF0, ?_⟩
  obtain ⟨hCong3_1, hCong3_2, hCong3_3⟩ := hCong3
  have hBA'ED' : Cong B A' E D' := by cong_r
  have hAux1 := l11_aux_c B A A' A0 E D D' D0 (l6_6 hA) (l6_6 hD) hBA'ED' hBetA0 hBetD0 hCongA0 hCongD0
  have hAux2 := l11_aux_c B C C' C0 E F F' F0 (l6_6 hC) (l6_6 hF) hCong3_3 hBetC0 hBetF0 hCongC0 hCongF0
  obtain ⟨hBA0ED0, hA'A0D'D0⟩ := hAux1
  obtain ⟨hBC0EF0, hC'C0F'F0⟩ := hAux2
  have hColBA'A0 : Col B A' A0 := by
    have h1 : Col B A' A := out_col hA
    have h2 : Col B A A0 := bet_col_c B A A0 hBetA0
    have h3 : B ≠ A := Ne.symm hA.2.1
    colr
  have hColBC'C0 : Col B C' C0 := by
    have h1 : Col B C' C := out_col hC
    have h2 : Col B C C0 := bet_col_c B C C0 hBetC0
    have h3 : B ≠ C := Ne.symm hC.2.1
    colr
  have hFSC1 : FSC B C' C0 A' E F' F0 D' :=
    ⟨hColBC'C0, ⟨hCong3_3, hBC0EF0, hC'C0F'F0⟩, hBA'ED', by cong_r⟩
  have hStep1 : Cong C0 A' F0 D' := l4_16 hFSC1 (Ne.symm hC.1)
  have hFSC2 : FSC B A' A0 C0 E D' D0 F0 :=
    ⟨hColBA'A0, ⟨hBA'ED', hBA0ED0, hA'A0D'D0⟩, hBC0EF0, by cong_r⟩
  exact l4_16 hFSC2 (Ne.symm hA.1)
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
  exact ⟨A', (⟨C', (⟨D', (⟨F', ((let H20 := cong_right_commutativity (l2_11 (between_symmetry H9) H15 (cong_symmetry (cong_symmetry (cong_left_commutativity H10))) (cong_symmetry (cong_symmetry (cong_4312_c b3 D' b1 b0 H16)))); (let H21 := cong_right_commutativity (l2_11 H12 (between_symmetry H18) (cong_symmetry (cong_symmetry (cong_3421_c b5 F' b1 b2 H19))) (cong_symmetry (cong_symmetry (cong_right_commutativity H13)))); (let H22 := bet_neq21_neq H18 H6; (let H23 := bet_neq21_neq H15 H4; (let H24 := bet_neq21_neq H12 H2; (let H25 := bet_neq21_neq H9 H0; (let H26 := cong_diff_4_c b2 C' b4 b5 H6 H13; (let H27 := cong_diff_4_c b0 A' b4 b3 H4 H10; (let H28 := cong_diff_4_c b5 F' b1 b2 H2 H19; (let H29 := cong_diff_4_c b3 D' b1 b0 H0 H16; ⟨(⟨(Ne.symm H25), (⟨H0, (Or.inr H9)⟩)⟩), (⟨(⟨(Ne.symm H24), (⟨H2, (Or.inr H12)⟩)⟩), (⟨(⟨(Ne.symm H23), (⟨H4, (Or.inr H15)⟩)⟩), (⟨(⟨(Ne.symm H22), (⟨H6, (Or.inr H18)⟩)⟩), (⟨H20, (⟨(H7 A' C' D' F' (⟨(⟨(Ne.symm H25), (⟨H0, (Or.inr H9)⟩)⟩), (⟨(⟨(Ne.symm H24), (⟨H2, (Or.inr H12)⟩)⟩), (⟨(⟨(Ne.symm H23), (⟨H4, (Or.inr H15)⟩)⟩), (⟨(⟨(Ne.symm H22), (⟨H6, (Or.inr H18)⟩)⟩), (⟨(cong_symmetry (cong_symmetry (cong_commutativity H20))), H21⟩)⟩)⟩)⟩)⟩)), H21⟩)⟩)⟩)⟩)⟩)⟩)))))))))))⟩)⟩)⟩)⟩)))
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
    ∀ (A B C D E F A' C' D' F' : Tpoint), CongA A B C D E F → Out B A' A → Out B C' C → Out E D' D → Out E F' F → CongA A' B C' D' E F' := by
  intro A B C D E F A' C' D' F' h1 h2 h3 h4 h5
  obtain ⟨hAB, hCB, hDE, hFE, hforall⟩ := l11_4_1_c A B C D E F h1
  apply l11_4_2_c
  refine ⟨h2.1, h3.1, h4.1, h5.1, ?_⟩
  intro A2 C2 D2 F2 hh
  obtain ⟨hOutA2, hOutC2, hOutD2, hOutF2, hCongA2, hCongC2⟩ := hh
  have outA2A : Out B A2 A := l6_7_c B A2 A' A hOutA2 h2
  have outC2C : Out B C2 C := l6_7_c B C2 C' C hOutC2 h3
  have outD2D : Out E D2 D := l6_7_c E D2 D' D hOutD2 h4
  have outF2F : Out E F2 F := l6_7_c E F2 F' F hOutF2 h5
  exact hforall A2 C2 D2 F2 ⟨outA2A, outC2C, outD2D, outF2F, hCongA2, hCongC2⟩
theorem out2_conga_c :
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
  have H33 := bet_neq21_neq H25 H7
  have H34 := bet_neq21_neq H21 H5
  have H35 := bet_neq21_neq H17 H3
  have H36 := bet_neq21_neq H13 H1
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
    ∀ (A B C A' B' C' A'' B'' C'' : Tpoint), CongA A B C A' B' C' → CongA A' B' C' A'' B'' C'' → CongA A B C A'' B'' C'' := by
  intro A B C A' B' C' A'' B'' C'' h1 h2
  have HH := h1
  obtain ⟨hAB, hCB, hA'B', hC'B', A0, C0, A1, C1,
    hBetA0, hCongA0, hBetC0, hCongC0, hBetA1, hCongA1, hBetC1, hCongC1, hCongAC⟩ := h1
  have h2' := h2
  obtain ⟨_, _, hA''B'', hC''B'', _⟩ := h2'
  have hA1C1 : CongA A1 B' C1 A'' B'' C'' :=
    l11_10_c A' B' C' A'' B'' C'' A1 C1 A'' C'' h2
      (l6_6 (bet_out hA'B' hBetA1))
      (l6_6 (bet_out hC'B' hBetC1))
      (out_trivial hA''B'')
      (out_trivial hC''B'')
  have hA0C0 : CongA A0 B C0 A' B' C' :=
    l11_10_c A B C A' B' C' A0 C0 A' C' HH
      (l6_6 (bet_out hAB hBetA0))
      (l6_6 (bet_out hCB hBetC0))
      (out_trivial hA'B')
      (out_trivial hC'B')
  have hCongBA0 : Cong B A0 B' A1 :=
    cong_right_commutativity (l2_11 hBetA0 (between_symmetry hBetA1)
      (cong_right_commutativity (cong_symmetry hCongA1))
      (cong_right_commutativity hCongA0))
  have hCongBC0 : Cong B C0 B' C1 :=
    cong_right_commutativity (l2_11 hBetC0 (between_symmetry hBetC1)
      (cong_right_commutativity (cong_symmetry hCongC1))
      (cong_right_commutativity hCongC0))
  have hA0neB : A0 ≠ B := Ne.symm (bet_neq21_neq hBetA0 hAB)
  have hC0neB : C0 ≠ B := Ne.symm (bet_neq21_neq hBetC0 hCB)
  have hCongDiag : Cong A0 C0 A1 C1 :=
    (l11_4_1_c A0 B C0 A' B' C' hA0C0).2.2.2.2 A0 C0 A1 C1
      ⟨out_trivial hA0neB, out_trivial hC0neB,
       l6_6 (bet_out hA'B' hBetA1), l6_6 (bet_out hC'B' hBetC1),
       hCongBA0, hCongBC0⟩
  have hCong3 : Cong_3 A0 B C0 A1 B' C1 :=
    ⟨cong_commutativity hCongBA0, hCongDiag, hCongBC0⟩
  have hCong3' : Cong_3 A1 B' C1 A0 B C0 := cong3_symmetry_c A0 B C0 A1 B' C1 hCong3
  have hFinal : CongA A0 B C0 A'' B'' C'' :=
    cong3_conga2_c A1 B' C1 A0 B C0 A'' B'' C'' hCong3' hA1C1
  exact l11_10_c A0 B C0 A'' B'' C'' A C A'' C'' hFinal
    (bet_out hAB hBetA0) (bet_out hCB hBetC0)
    (out_trivial hA''B'') (out_trivial hC''B'')
theorem conga_pseudo_refl_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → CongA A B C C B A := by
  intro A B C h1 h2
  obtain ⟨A', hA'⟩ := segment_construction B A B C
  obtain ⟨C', hC'⟩ := segment_construction B C B A
  have hpr : Cong A' C' C' A' := cong_pseudo_reflexivity A' C'
  unfold CongA
  tauto
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
  exact ⟨b10, (⟨H6, (⟨b12, (⟨H10, (⟨A0, (⟨C'', (⟨D0, (⟨F'', (⟨H33, (⟨H34, (⟨H20, (⟨H22, (⟨H36, (⟨H37, (⟨H28, (⟨H30, (five_segment_with_def (⟨(outer_transitivity_between2 (between_symmetry H16) (outer_transitivity_between b9 H33 (Ne.symm b10)) H4), (⟨(outer_transitivity_between2 (between_symmetry H24) (outer_transitivity_between b11 H36 (Ne.symm b12)) H8), (⟨(cong_left_commutativity (l2_11 H16 (between_symmetry H24) (cong_symmetry (cong_symmetry (cong_3421_c b3 D'' b1 b0 H26))) (cong_symmetry (cong_symmetry (cong_right_commutativity H18))))), (⟨(cong_right_commutativity (l2_11 H33 (between_symmetry H36) (cong_symmetry (cong_symmetry (cong_symmetry (cong_left_commutativity H37)))) (cong_symmetry (cong_symmetry (cong_right_commutativity H34))))), (⟨H31, (cong_right_commutativity (l2_11 H20 (between_symmetry H28) (cong_symmetry (cong_symmetry (cong_3421_c b5 F'' b1 b2 H30))) (cong_symmetry (cong_symmetry (cong_right_commutativity H22)))))⟩)⟩)⟩)⟩)⟩) ((let H38 := bet_neq12_neq b11 H8; (let H39 := bet_neq12_neq b9 H4; (let H40 := bet_neq21_neq H36 b12; (let H41 := bet_neq21_neq H33 b10; (let H42 := bet_neq21_neq H28 H10; (let H43 := bet_neq21_neq H24 H8; (let H44 := bet_neq21_neq H20 H6; (let H45 := bet_neq21_neq H16 H4; (let H46 := cong_diff_4_c b6 A0 b4 b7 b12 H34; (let H47 := cong_diff_4_c b7 D0 b1 b6 b10 H37; (let H48 := cong_diff_4_c b2 C'' b4 b5 H10 H22; (let H49 := cong_diff_4_c b0 A'' b4 b3 H8 H18; (let H50 := cong_diff_4_c b5 F'' b1 b2 H6 H30; (let H51 := cong_diff_4_c b3 D'' b1 b0 H4 H26; Ne.symm H45))))))))))))))))⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
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
  have H5 := bet_neq12_neq b11 b8
  have H6 := bet_neq12_neq b10 b6
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
  (let H5 := bet_neq12_neq b5 b6; (let H6 := bet_neq21_neq b8 b9; (let H7 := l11_13_c b0 b1 b2 b2 b1 b0 b3 b4 (conga_pseudo_refl_c b0 b1 b2 b6 (Ne.symm b9)) b5 b7 b8 (Ne.symm b10); l11_13_c b3 b1 b2 b0 b1 b4 b0 b3 (conga_right_comm_c b3 b1 b2 b4 b1 b0 H7) (between_symmetry b5) b6 b5 b7)))
theorem l11_16_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → A ≠ B → C ≠ B → Per A' B' C' → A' ≠ B' → C' ≠ B' → CongA A B C A' B' C' := by
  intro A B C A' B' C' hPer hAB hCB hPer' hA'B' hC'B'
  obtain ⟨C0, hBetC0, hCongC0⟩ := segment_construction B C B' C'
  obtain ⟨C1, hBetC1, hCongC1⟩ := segment_construction B' C' B C
  obtain ⟨A0, hBetA0, hCongA0⟩ := segment_construction B A B' A'
  obtain ⟨A1, hBetA1, hCongA1⟩ := segment_construction B' A' B A
  have hPerCBA : Per C B A := l8_2_c A B C hPer
  have hPerCBA0 : Per C B A0 := per_col_c C B A A0 (Ne.symm hAB) hPerCBA (Or.inl hBetA0)
  have hPerA0BC : Per A0 B C := l8_2_c C B A0 hPerCBA0
  have hPerA0BC0 : Per A0 B C0 := per_col_c A0 B C C0 (Ne.symm hCB) hPerA0BC (Or.inl hBetC0)
  have hPerC'B'A' : Per C' B' A' := l8_2_c A' B' C' hPer'
  have hPerC'B'A1 : Per C' B' A1 := per_col_c C' B' A' A1 (Ne.symm hA'B') hPerC'B'A' (Or.inl hBetA1)
  have hPerA1B'C' : Per A1 B' C' := l8_2_c C' B' A1 hPerC'B'A1
  have hPerA1B'C1 : Per A1 B' C1 := per_col_c A1 B' C' C1 (Ne.symm hC'B') hPerA1B'C' (Or.inl hBetC1)
  have hCongAB' : Cong A0 B A1 B' :=
    cong_right_commutativity_c A0 B B' A1
      (l2_11_c A0 A B B' A' A1
        (between_symmetry_c B A A0 hBetA0)
        hBetA1
        (cong_left_commutativity_c A A0 B' A' hCongA0)
        (cong_symmetry_c A' A1 A B (cong_right_commutativity_c A' A1 B A hCongA1)))
  have hCongBC0 : Cong B C0 B' C1 :=
    cong_right_commutativity_c B C0 C1 B'
      (l2_11_c B C C0 C1 C' B'
        hBetC0
        (between_symmetry_c B' C' C1 hBetC1)
        (cong_symmetry_c C1 C' B C (cong_left_commutativity_c C' C1 B C hCongC1))
        (cong_right_commutativity_c C C0 B' C' hCongC0))
  have hCongFinal : Cong A0 C0 A1 C1 :=
    l10_12_c A0 B C0 A1 B' C1 hPerA0BC0 hPerA1B'C1 hCongAB' hCongBC0
  exact ⟨hAB, hCB, hA'B', hC'B', A0, C0, A1, C1,
    hBetA0, hCongA0, hBetC0, hCongC0, hBetA1, hCongA1, hBetC1, hCongC1, hCongFinal⟩
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
    ∀ (A B C A' B' C' : Tpoint), Out B A C → CongA A B C A' B' C' → Out B' A' C' := by
  intro A B C A' B' C' h1 h2
  obtain ⟨hAB, hCB, hA'B', hC'B', A0, C0, A1, C1,
    hBetA0, hCongA0, hBetC0, hCongC0, hBetA1, hCongA1, hBetC1, hCongC1, hCongAC⟩ := h2
  have hA0B : A0 ≠ B := Ne.symm (bet_neq21_neq hBetA0 hAB)
  have hC0B : C0 ≠ B := Ne.symm (bet_neq21_neq hBetC0 hCB)
  have hOutBA0C0 : Out B A0 C0 := by
    refine ⟨hA0B, hC0B, ?_⟩
    rcases h1.2.2 with hCase | hCase
    · exact l5_1 (Ne.symm hAB) hBetA0 (between_exchange4 hCase hBetC0)
    · exact l5_1 (Ne.symm hCB) (between_exchange4 hCase hBetA0) hBetC0
  have hComp1 : Cong B A0 B' A1 :=
    cong_right_commutativity
      (l2_11 hBetA0 (between_symmetry hBetA1)
        (cong_symmetry (cong_left_commutativity hCongA1))
        (cong_right_commutativity hCongA0))
  have hComp2 : Cong B C0 B' C1 :=
    cong_right_commutativity
      (l2_11 hBetC0 (between_symmetry hBetC1)
        (cong_symmetry (cong_left_commutativity hCongC1))
        (cong_right_commutativity hCongC0))
  have hOutB'A1C1 : Out B' A1 C1 :=
    cong3_preserves_out_c B A0 C0 B' A1 C1 hOutBA0C0 ⟨hComp1, hComp2, hCongAC⟩
  have hOutB'A1A' : Out B' A1 A' := ⟨hOutB'A1C1.1, hA'B', Or.inr hBetA1⟩
  have hOutB'C1C' : Out B' C1 C' := ⟨hOutB'A1C1.2.1, hC'B', Or.inr hBetC1⟩
  have hOutB'C1A' : Out B' C1 A' := l6_7_c B' C1 A1 A' (l6_6 hOutB'A1C1) hOutB'A1A'
  have hOutB'A1A'2 : Out B' A1 A' := l6_7_c B' A1 C1 A' hOutB'A1C1 hOutB'C1A'
  have hFinal1 : Out B' A' A1 := l6_6 hOutB'A1A'2
  have hFinal2 : Out B' A1 C' := l6_7_c B' A1 C1 C' hOutB'A1C1 hOutB'C1C'
  exact l6_7_c B' A' A1 C' hFinal1 hFinal2
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
theorem conga_cop_or_out_ts_c :
    ∀ (A B C C' : Tpoint), Coplanar A B C C' → CongA A B C A B C' → Out B C C' ∨ TS A B C C' := by
  intro A B C C' hCop hCongA
  obtain ⟨hAB, hCB, _, hC'B, A0, C0, A1, C1, hBetA0, hCongA0, hBetC0, hCongC0, hBetA1, hCongA1, hBetC1, hCongC1, hCongF⟩ := hCongA
  have hA01 : A0 = A1 := construction_uniqueness_c B A B A A0 A1 (Ne.symm hAB) hBetA0 hCongA0 hBetA1 hCongA1
  subst hA01
  rcases point_equality_decidability C0 C1 with hEq | hNe
  · subst hEq
    left
    exact bet2_out_c B C C0 C' (Ne.symm hCB) (Ne.symm hC'B) hBetC0 hBetC1
  · have hR3 : Cong B C0 B C1 := by
      have h3 : Cong B C C1 C' := cong_right_commutativity_c B C C' C1 (cong_symmetry_c C' C1 B C hCongC1)
      have h4 : Cong C C0 C' B := cong_right_commutativity_c C C0 B C' hCongC0
      have h2 : Bet C1 C' B := between_symmetry_c B C' C1 hBetC1
      exact cong_right_commutativity_c B C0 C1 B (l2_11_c B C C0 C1 C' B hBetC0 h2 h3 h4)
    obtain ⟨M, hMidM⟩ := midpoint_existence_c C0 C1
    have hR7 : B ≠ A0 := bet_neq12_neq_c B A A0 hBetA0 (Ne.symm hAB)
    have hColA0BA : Col A0 B A := col_permutation_2_c B A A0 (bet_col_c B A A0 hBetA0)
    have hCongAC0C1 : Cong A C0 A C1 := l4_17_c A0 B A C0 C1 (Ne.symm hR7) hColA0BA hCongF hR3
    have hR9 : Per A M C0 := ⟨C1, hMidM, hCongAC0C1⟩
    have hR10 : Per A M C1 := l8_4_c A M C0 C1 hR9 hMidM
    have hR5 : Per B M C0 := ⟨C1, hMidM, hR3⟩
    have hR6 : Per B M C1 := l8_4_c B M C0 C1 hR5 hMidM
    have hU1 : Coplanar A C' B C := coplanar_perm_4_c A B C C' hCop
    have hStep2 : Coplanar A C' B C0 := col_cop_cop_c A C' B C C0 hU1 (Ne.symm hCB) (bet_col_c B C C0 hBetC0)
    have hCopAC0BC' : Coplanar A C0 B C' :=
      coplanar_perm_2_c A B C0 C' (coplanar_perm_1_c A B C' C0 (coplanar_perm_2_c A C' B C0 hStep2))
    have hStep4 : Coplanar A C0 B C1 := col_cop_cop_c A C0 B C' C1 hCopAC0BC' (Ne.symm hC'B) (bet_col_c B C' C1 hBetC1)
    have hT1 : Coplanar B A C0 C1 := coplanar_perm_6_c A B C0 C1 (coplanar_perm_2_c A C0 B C1 hStep4)
    have hColC0C1M : Col C0 C1 M := col_permutation_1_c M C0 C1 (midpoint_col_c C0 M C1 hMidM)
    have hStep7 : Coplanar B A C0 M := col_cop_cop_c B A C0 C1 M hT1 hNe hColC0C1M
    have hS1 : Coplanar C0 B A M :=
      coplanar_perm_6_c B C0 A M (coplanar_perm_2_c B A C0 M hStep7)
    have hC0M : C0 ≠ M := by
      intro hEqM
      subst hEqM
      exact hNe (is_midpoint_id_c C0 C1 hMidM)
    have hR11 : Col B A M := cop_per2_col_c C0 B A M hS1 hC0M hR5 hR9
    rcases point_equality_decidability B M with hBM | hBMne
    · subst hBM
      have hBC0 : B ≠ C0 := bet_neq12_neq_c B C C0 hBetC0 (Ne.symm hCB)
      have hPerABC : Per A B C := per_col_c A B C0 C hBC0 hR9 (col_permutation_5_c B C C0 (bet_col_c B C C0 hBetC0))
      have hNColABC : ¬ Col A B C := by
        intro hColABC
        rcases l8_9_c A B C hPerABC hColABC with h | h
        · exact hAB h
        · exact hCB h
      have hBC1 : B ≠ C1 := bet_neq12_neq_c B C' C1 hBetC1 (Ne.symm hC'B)
      have hPerABC' : Per A B C' := per_col_c A B C1 C' hBC1 hR10 (col_permutation_5_c B C' C1 (bet_col_c B C' C1 hBetC1))
      have hNColBAC : ¬ Col B A C := fun h => hNColABC (col_permutation_4_c B A C h)
      have hT1' : Bet C0 C B := between_symmetry_c B C C0 hBetC0
      have hMidBet : Bet C0 B C1 := hMidM.1
      have hInner1 : Bet C B C1 := between_exchange3_c C0 C B C1 hT1' hMidBet
      have hInner1' : Bet C1 B C := between_symmetry_c C B C1 hInner1
      have hS1' : Bet C1 C' B := between_symmetry_c B C' C1 hBetC1
      have hStep' : Bet C' B C := between_exchange3_c C1 C' B C hS1' hInner1'
      have hBetCBC' : Bet C B C' := between_symmetry_c C' B C hStep'
      right
      exact invert_two_sides_c B A C C' (bet_ts_c B A C C' (Ne.symm hC'B) hNColBAC hBetCBC')
    · have hC1M : C1 ≠ M := by
        intro hEq
        apply hC0M
        have hRev : Midpoint M C1 C0 := l7_2_c M C0 C1 hMidM
        rw [hEq] at hRev
        exact (is_midpoint_id_c M C0 hRev).symm
      have hM1 : ¬ Col C0 B M := by
        intro hCol
        rcases l8_9_c B M C0 hR5 (col_permutation_1_c C0 B M hCol) with h | h
        · exact hBMne h
        · exact hC0M h
      have hM2 : ¬ Col C1 B M := by
        intro hCol
        rcases l8_9_c B M C1 hR6 (col_permutation_1_c C1 B M hCol) with h | h
        · exact hBMne h
        · exact hC1M h
      have hM3 : Col M B M := col_trivial_3_c M B
      have hBetC0MC1 : Bet C0 M C1 := hMidM.1
      have hL2 : TS B M C0 C1 := ⟨hM1, hM2, M, hM3, hBetC0MC1⟩
      have hColBMA : Col B M A := col_permutation_5_c B A M hR11
      have hV1pre : TS B A C0 C1 := col_two_sides_c B M A C0 C1 hColBMA (Ne.symm hAB) hL2
      have hV1 : TS A B C0 C1 := invert_two_sides_c B A C0 C1 hV1pre
      have hBC0 : B ≠ C0 := bet_neq12_neq_c B C C0 hBetC0 (Ne.symm hCB)
      have hOutBC0C : Out B C0 C := ⟨Ne.symm hBC0, hCB, Or.inr hBetC0⟩
      have hW2 : TS A B C C1 := l9_5_c A B C0 C1 B C hV1 (col_trivial_3_c B A) hOutBC0C
      have hBC1 : B ≠ C1 := bet_neq12_neq_c B C' C1 hBetC1 (Ne.symm hC'B)
      have hOutBC1C' : Out B C1 C' := ⟨Ne.symm hBC1, hC'B, Or.inr hBetC1⟩
      have hZ1 : TS A B C1 C := l9_2_c A B C C1 hW2
      have hW1 : TS A B C' C := l9_5_c A B C1 C B C' hZ1 (col_trivial_3_c B A) hOutBC1C'
      right
      exact l9_2_c A B C' C hW1

theorem conga_os_out_c :
    ∀ (A B C C' : Tpoint), CongA A B C A B C' → OS A B C C' → Out B C C' := by
  intro A B C C' hCongA hOS
  rcases conga_cop_or_out_ts_c A B C C' (os_coplanar_c A B C C' hOS) hCongA with h | h
  · exact h
  · exact absurd hOS (l9_9_c A B C C' h)

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
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ OS A' B' C' P := by
  intro A B C A' B' P H H0
  have hNColBAC : ¬ Col B A C := fun h => H (col_permutation_4_c B A C h)
  obtain ⟨C0, H1, H2⟩ := l8_18_existence_c B A C hNColBAC
  have hAneB : A ≠ B := by
    intro heq; apply H; rw [heq]; exact col_trivial_1_c B C
  have hCneB : C ≠ B := by
    intro heq; apply H; rw [heq]; exact col_trivial_2_c A B
  have hA'neB' : A' ≠ B' := by
    intro heq; apply H0; rw [heq]; exact col_trivial_1_c B' P
  have hCneC0 : C ≠ C0 := by
    obtain ⟨_, _, hCC0, _, _, _⟩ := H2
    exact hCC0
  rcases eq_dec_points_c B C0 with H3 | H3
  · -- CASE B = C0
    subst C0
    have hStep1 : Perp_at B B A C B := perp_perp_in_c B A C H2
    have hStep2 : Perp_at B A B B C := perp_in_comm_c B A C B B hStep1
    have hPerABC : Per A B C := perp_in_per_c A B C hStep2
    obtain ⟨C', hPerC'B'A', hCongC'B'CB, hOSA'B'C'P⟩ :=
      ex_per_cong_c A' B' B' P C B hA'neB' hCneB (col_trivial_2_c A' B') H0
    have hPerA'B'C' : Per A' B' C' := l8_2_c C' B' A' hPerC'B'A'
    have hC'neB' : C' ≠ B' := by
      intro heq
      rw [heq] at hCongC'B'CB
      have hCB2 : C = B := cong_identity C B B' (cong_symmetry_c B' B' C B hCongC'B'CB)
      exact hCneB hCB2
    exact ⟨C', l11_16_c A B C A' B' C' hPerABC hAneB hCneB hPerA'B'C' hA'neB' hC'neB',
      hOSA'B'C'P⟩
  · -- CASE B ≠ C0
    rcases out_dec_c B A C0 with H4 | H4
    · -- CASE Out B A C0
      have hB'neA' : B' ≠ A' := Ne.symm hA'neB'
      obtain ⟨C0', hOutB'A'C0', hCongB'C0'BC0⟩ :=
        segment_construction_3_c B' A' B C0 hB'neA' H3
      have hB'neC0' : B' ≠ C0' := Ne.symm hOutB'A'C0'.2.1
      have hColB'C0'A' : Col B' C0' A' := out_col_c B' C0' A' (l6_6_c B' A' C0' hOutB'A'C0')
      have hNColB'C0'P : ¬ Col B' C0' P := by
        intro hColB'C0'P
        apply H0
        have hColB'PA' : Col B' P A' :=
          col_transitivity_1_c B' C0' P A' hB'neC0' hColB'C0'P hColB'C0'A'
        exact col_permutation_2_c B' P A' hColB'PA'
      obtain ⟨C', hPerC'C0'B', hCongC'C0'CC0, hOSB'C0'C'P⟩ :=
        ex_per_cong_c B' C0' C0' P C C0 hB'neC0' hCneC0 (col_trivial_2_c B' C0') hNColB'C0'P
      have hC0neB : C0 ≠ B := Ne.symm H3
      have hCong1 : Cong C0 B C0' B' :=
        cong_symmetry_c C0' B' C0 B (cong_commutativity_c B' C0' B C0 hCongB'C0'BC0)
      have hCong2 : Cong C0 C C0' C' :=
        cong_symmetry_c C0' C' C0 C (cong_commutativity_c C' C0' C C0 hCongC'C0'CC0)
      have hPerpBC0CC0 : Perp B C0 C C0 := perp_col_c B A C C0 C0 H3 H2 H1
      have hPerpC0BCC0 : Perp C0 B C C0 := perp_left_comm_c B C0 C C0 hPerpBC0CC0
      have hPerpAtC0 : Perp_at C0 C0 B C C0 := perp_perp_in_c C0 B C hPerpC0BCC0
      have hPerBC0C : Per B C0 C := perp_in_per_c B C0 C (perp_in_comm_c C0 B C C0 C0 hPerpAtC0)
      have hPerB'C0'C' : Per B' C0' C' := l8_2_c C' C0' B' hPerC'C0'B'
      have hCongBC0B'C0' : Cong B C0 B' C0' := cong_symmetry_c B' C0' B C0 hCongB'C0'BC0
      have hCong3 : Cong B C B' C' :=
        l10_12_c B C0 C B' C0' C' hPerBC0C hPerB'C0'C' hCongBC0B'C0' hCong2
      have hCong3triple : Cong_3 C0 B C C0' B' C' := ⟨hCong1, hCong2, hCong3⟩
      have hC'neB' : C' ≠ B' := by
        intro heq
        rw [heq] at hPerC'C0'B'
        have hEq2 : B' = C0' := l8_8_c B' C0' hPerC'C0'B'
        rw [← hEq2] at hOutB'A'C0'
        exact hOutB'A'C0'.2.1 rfl
      have hCongAfinal : CongA A B C A' B' C' :=
        l11_10_c C0 B C C0' B' C' A C A' C'
          (cong3_conga_c C0 B C C0' B' C' hC0neB hCneB hCong3triple)
          H4
          (out_trivial_c B C hCneB)
          hOutB'A'C0'
          (out_trivial_c B' C' hC'neB')
      have hOSB'A'C'P : OS B' A' C' P :=
        col_one_side_c B' C0' A' C' P hColB'C0'A' hB'neA' hOSB'C0'C'P
      have hOSA'B'C'P : OS A' B' C' P := invert_one_side_c B' A' C' P hOSB'A'C'P
      exact ⟨C', hCongAfinal, hOSA'B'C'P⟩
    · -- CASE ¬ Out B A C0, hence Bet A B C0
      have H4' : Bet A B C0 := not_out_bet_c A B C0 (col_permutation_4_c B A C0 H1) H4
      obtain ⟨C0', hBetA'B'C0', hCongB'C0'BC0⟩ := segment_construction A' B' B C0
      have hB'neC0' : B' ≠ C0' := by
        intro heq
        rw [heq] at hCongB'C0'BC0
        have hBC0 : B = C0 := cong_identity B C0 C0' (cong_symmetry_c C0' C0' B C0 hCongB'C0'BC0)
        exact H3 hBC0
      have hColB'C0'A' : Col B' C0' A' := Or.inr (Or.inr hBetA'B'C0')
      have hNColB'C0'P : ¬ Col B' C0' P := by
        intro hColB'C0'P
        apply H0
        have hColB'PA' : Col B' P A' :=
          col_transitivity_1_c B' C0' P A' hB'neC0' hColB'C0'P hColB'C0'A'
        exact col_permutation_2_c B' P A' hColB'PA'
      obtain ⟨C', hPerC'C0'B', hCongC'C0'CC0, hOSB'C0'C'P⟩ :=
        ex_per_cong_c B' C0' C0' P C C0 hB'neC0' hCneC0 (col_trivial_2_c B' C0') hNColB'C0'P
      have hC0neB : C0 ≠ B := Ne.symm H3
      have hCong1 : Cong C0 B C0' B' :=
        cong_symmetry_c C0' B' C0 B (cong_commutativity_c B' C0' B C0 hCongB'C0'BC0)
      have hCong2 : Cong C0 C C0' C' :=
        cong_symmetry_c C0' C' C0 C (cong_commutativity_c C' C0' C C0 hCongC'C0'CC0)
      have hPerpBC0CC0 : Perp B C0 C C0 := perp_col_c B A C C0 C0 H3 H2 H1
      have hPerpC0BCC0 : Perp C0 B C C0 := perp_left_comm_c B C0 C C0 hPerpBC0CC0
      have hPerpAtC0 : Perp_at C0 C0 B C C0 := perp_perp_in_c C0 B C hPerpC0BCC0
      have hPerCC0B : Per C C0 B := perp_in_per_c C C0 B (perp_in_sym_c C0 B C C0 C0 hPerpAtC0)
      have hPerC'B' : Per C' C0' B' := hPerC'C0'B'
      have hCongCC0C'C0' : Cong C C0 C' C0' := cong_symmetry_c C' C0' C C0 hCongC'C0'CC0
      have hCongCBC'B' : Cong C B C' B' :=
        l10_12_c C C0 B C' C0' B' hPerCC0B hPerC'B' hCongCC0C'C0' hCong1
      have hCong3 : Cong B C B' C' := cong_commutativity_c C B C' B' hCongCBC'B'
      have hCong3triple : Cong_3 C0 B C C0' B' C' := ⟨hCong1, hCong2, hCong3⟩
      have hCongAfinal : CongA A B C A' B' C' :=
        l11_13_c C0 B C C0' B' C' A A'
          (cong3_conga_c C0 B C C0' B' C' hC0neB hCneB hCong3triple)
          (between_symmetry_c A B C0 H4')
          hAneB
          (between_symmetry_c A' B' C0' hBetA'B'C0')
          hA'neB'
      have hOSB'A'C'P : OS B' A' C' P :=
        col_one_side_c B' C0' A' C' P hColB'C0'A' (Ne.symm hA'neB') hOSB'C0'C'P
      have hOSA'B'C'P : OS A' B' C' P := invert_one_side_c B' A' C' P hOSB'A'C'P
      exact ⟨C', hCongAfinal, hOSA'B'C'P⟩
theorem angle_construction_2_c :
    ∀ (A B C A' B' P : Tpoint), A ≠ B → A ≠ C → B ≠ C → A' ≠ B' → ¬ Col A' B' P → ∃ (C' : Tpoint), CongA A B C A' B' C' ∧ (OS A' B' C' P ∨ Col A' B' C') := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have o := col_dec_c b0 b1 b2
  rcases o with H4 | H4
  · have o0 := out_dec_c b1 b0 b2
    rcases o0 with H5 | H5
    · exact ⟨b3, (⟨((let H6 := out2_conga_c b0 b1 b0 b0 b2 (out_trivial b6) (l6_6 H5); (let H7 := conga_trivial_1_c b0 b1 b3 b4 b6 b9; conga_sym_c b3 b4 b3 b0 b1 b2 (conga_trans_c b3 b4 b3 b0 b1 b0 b0 b1 b2 (conga_sym_c b0 b1 b0 b3 b4 b3 H7) H6)))), (Or.inr (col_trivial_3_c b3 b4))⟩)⟩
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
  exact conga_os_out_c b3 b4 F1 F2 (conga_trans_c b3 b4 F1 b0 b1 b2 b3 b4 F2 (conga_sym_c b0 b1 b2 b3 b4 F1 H10) H8) (invert_one_side_c b4 b3 F1 F2 (one_side_transitivity_c b4 b3 F1 b5 F2 H11 (one_side_symmetry_c b4 b3 F2 b5 H9)))))⟩)⟩)⟩
theorem l11_19_c :
    ∀ (A B P1 P2 : Tpoint), Per A B P1 → Per A B P2 → OS A B P1 P2 → Out B P1 P2 := by
  intro A B P1 P2 hPer1 hPer2 hOS
  have hNColABP1 : ¬ Col A B P1 := by
    intro hCol
    obtain ⟨T, hTS1, _⟩ := hOS
    rcases l8_9_c A B P1 hPer1 hCol with hAB | hP1B
    · subst hAB; exact hTS1.1 (col_trivial_2_c P1 A)
    · subst hP1B; exact hTS1.1 (col_trivial_3_c P1 A)
  have hNColABP2 : ¬ Col A B P2 := by
    intro hCol
    obtain ⟨T, _, hTS2⟩ := hOS
    rcases l8_9_c A B P2 hPer2 hCol with hAB | hP2B
    · subst hAB; exact hTS2.1 (col_trivial_2_c P2 A)
    · subst hP2B; exact hTS2.1 (col_trivial_3_c P2 A)
  have hAB : A ≠ B := fun h => hNColABP1 (h ▸ col_trivial_1_c A P1)
  have hP1B : P1 ≠ B := fun h => hNColABP1 (h ▸ col_trivial_2_c A B)
  have hP2B : P2 ≠ B := fun h => hNColABP2 (h ▸ col_trivial_2_c A B)
  obtain ⟨F, hCongF, hOSF, hUniq⟩ := l11_15_c A B P1 A B P2 hNColABP1 hNColABP2
  apply hUniq P1 P2
  refine ⟨⟨conga_refl_c A B P1 hAB hP1B, invert_one_side_c A B P1 P2 hOS⟩,
    ⟨l11_16_c A B P1 A B P2 hPer1 hAB hP1B hPer2 hAB hP2B,
     one_side_reflexivity_c B A P2 (fun h => hNColABP2 (col_permutation_3_c P2 B A h))⟩⟩
theorem l11_22_bet_c :
    ∀ (A B C P A' B' C' P' : Tpoint), Bet A B C → TS P' B' A' C' → CongA A B P A' B' P' ∧ CongA P B C P' B' C' → Bet A' B' C' := by
  intro A B C P A' B' C' P' hBet hTS0 hCongPair
  obtain ⟨hCongABP, hCongPBC⟩ := hCongPair
  have hCneB : C ≠ B := hCongPBC.2.1
  obtain ⟨C'', H3, hCong4⟩ := segment_construction A' B' B C
  have hC''neB' : C'' ≠ B' := by
    intro heq
    rw [heq] at hCong4
    have hBC : B = C := cong_reverse_identity_c B' B C hCong4
    exact hCneB hBC.symm
  have H5 : CongA C B P C'' B' P' := l11_13_c A B P A' B' P' C C'' hCongABP hBet hCneB H3 hC''neB'
  have H6 : CongA C'' B' P' C' B' P' :=
    conga_trans_c C'' B' P' C B P C' B' P'
      (conga_sym_c C B P C'' B' P' H5)
      (conga_comm_c P B C P' B' C' hCongPBC)
  have hCop0 : Coplanar P' B' A' C' := ts_coplanar_c P' B' A' C' hTS0
  have hCopTarget : Coplanar P' C' B' A' := by
    obtain ⟨X, hX⟩ := hCop0
    rcases hX with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨X, Or.inr (Or.inl ⟨h1, col_permutation_4_c A' C' X h2⟩)⟩
    · exact ⟨X, Or.inr (Or.inr ⟨h1, col_permutation_4_c B' C' X h2⟩)⟩
    · exact ⟨X, Or.inl ⟨h1, h2⟩⟩
  obtain ⟨_, _, _, hB'neA', _, _⟩ := ts_distincts_c P' B' A' C' hTS0
  have hColB'A'C'' : Col B' A' C'' := col_permutation_4_c A' B' C'' (bet_col_c A' B' C'' H3)
  have hStep2 : Coplanar P' C' B' C'' := col_cop_cop_c P' C' B' A' C'' hCopTarget hB'neA' hColB'A'C''
  have hCopI : Coplanar P' B' C' C'' := coplanar_perm_2_c P' C' B' C'' hStep2
  have hCongII : CongA P' B' C' P' B' C'' :=
    conga_comm_c C' B' P' C'' B' P' (conga_sym_c C'' B' P' C' B' P' H6)
  have H7 : Out B' C' C'' ∨ TS P' B' C' C'' := conga_cop_or_out_ts_c P' B' C' C'' hCopI hCongII
  rcases H7 with hOut | hTS
  · obtain ⟨hC'neB', hC''neB'2, hBetOr⟩ := hOut
    rcases hBetOr with h9 | h9
    · exact between_inner_transitivity_c A' B' C' C'' H3 h9
    · exact outer_transitivity_between_c A' B' C'' C' H3 h9 (Ne.symm hC''neB'2)
  · rcases col_dec_c C' B' P' with hCol | hNCol
    · obtain ⟨hNColC'P'B', _, _⟩ := hTS
      exact (hNColC'P'B' (col_permutation_5_c C' B' P' hCol)).elim
    · have h1TS : TS B' P' C' A' := l9_2_c B' P' A' C' (invert_two_sides_c P' B' A' C' hTS0)
      have hTS_B'P'A'C'' : TS B' P' A' C'' := by
        obtain ⟨hA'nColP'B', hC'nColP'B', _, _, _⟩ := hTS0
        obtain ⟨hC'nColP'B'2, hC''nColP'B', _, _, _⟩ := hTS
        refine ⟨?_, ?_, B', col_trivial_1_c B' P', H3⟩
        · intro hColA'B'P'
          exact hA'nColP'B' (col_permutation_5_c A' B' P' hColA'B'P')
        · intro hColC''B'P'
          exact hC''nColP'B' (col_permutation_5_c C'' B' P' hColC''B'P')
      have h2TS : TS B' P' C'' A' := l9_2_c B' P' A' C'' hTS_B'P'A'C''
      have hOS : OS B' P' C' C'' := l9_8_1_c B' P' C' C'' A' h1TS h2TS
      exact ((l9_9_bis_c B' P' C' C'' hOS) (invert_two_sides_c P' B' C' C'' hTS)).elim
theorem l11_22a_c :
    ∀ (A B C P A' B' C' P' : Tpoint), TS B P A C ∧ TS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := by
  intro A B C P A' B' C' P' h
  obtain ⟨hTS, hTS', hCongABP, hCongPBC⟩ := h
  have hAB : A ≠ B := conga_diff1_c A B P A' B' P' hCongABP
  have hPB : P ≠ B := conga_diff2_c A B P A' B' P' hCongABP
  have hA'B' : A' ≠ B' := conga_diff45_c A B P A' B' P' hCongABP
  have hP'B' : P' ≠ B' := conga_diff56_c A B P A' B' P' hCongABP
  have hCB : C ≠ B := conga_diff2_c P B C P' B' C' hCongPBC
  have hC'B' : C' ≠ B' := conga_diff56_c P B C P' B' C' hCongPBC
  obtain ⟨A'', hOutB'A'A'', hCongB'A''BA⟩ :=
    segment_construction_3_c B' A' B A (Ne.symm hA'B') (Ne.symm hAB)
  have hColB'A'A'' : Col B' A' A'' := out_col_c B' A' A'' hOutB'A'A''
  have hB'neA'' : B' ≠ A'' := Ne.symm hOutB'A'A''.2.1
  have hColB'A''A' : Col B' A'' A' := col_permutation_5_c B' A' A'' hColB'A'A''
  obtain ⟨hNColABP, hNColCBP, T, hColTBP, hBetATC⟩ := hTS
  rcases eq_dec_points_c B T with hBT | hBT
  · -- Case B = T
    subst hBT
    have hBetPrimed : Bet A' B' C' :=
      l11_22_bet_c A B C P A' B' C' P' hBetATC (invert_two_sides_c B' P' A' C' hTS') ⟨hCongABP, hCongPBC⟩
    exact conga_line_c A B C A' B' C' hAB (Ne.symm hCB) hA'B' (Ne.symm hC'B') hBetATC hBetPrimed
  · -- Case B ≠ T
    have hNColA'P'B' : ¬ Col A' P' B' := fun hh => hTS'.1 (col_permutation_5_c A' P' B' hh)
    have hCop0 : Coplanar B' P' A' C' := ts_coplanar_c B' P' A' C' hTS'
    have hCopStep1 : Coplanar B' A' P' C' := coplanar_perm_2_c B' P' A' C' hCop0
    have hCopStep2 : Coplanar A' B' P' C' := coplanar_perm_6_c B' A' P' C' hCopStep1
    have hCopAPBC' : Coplanar A' P' B' C' := coplanar_perm_2_c A' B' P' C' hCopStep2
    rcases bet_dec_c P B T with hBetPBT | hNBetPBT
    · -- True sub-case: Bet P B T
      obtain ⟨T'', hBetP'B'T'', hCongB'T''BT⟩ := segment_construction P' B' B T
      have hColB'P'T'' : Col B' P' T'' :=
        col_permutation_4_c P' B' T'' (bet_col_c P' B' T'' hBetP'B'T'')
      have hT''neB' : T'' ≠ B' := by
        intro heq
        rw [heq] at hCongB'T''BT
        exact hBT (cong_reverse_identity_c B' B T hCongB'T''BT)
      have hCongPBAcomm : CongA P B A P' B' A' := conga_comm_c A B P A' B' P' hCongABP
      have hCongTBA : CongA T B A T'' B' A' :=
        l11_13_c P B A P' B' A' T T'' hCongPBAcomm hBetPBT (Ne.symm hBT) hBetP'B'T'' hT''neB'
      have hCongABT : CongA A B T A' B' T'' := conga_comm_c T B A T'' B' A' hCongTBA
      have hCongABT2 : CongA A B T A'' B' T'' :=
        l11_10_c A B T A' B' T'' A T A'' T'' hCongABT
          (out_trivial_c B A hAB) (out_trivial_c B T (Ne.symm hBT))
          (l6_6_c B' A' A'' hOutB'A'A'') (out_trivial_c B' T'' hT''neB')
      have hCongAT : Cong A T A'' T'' := by
        obtain ⟨_, _, _, _, hForall⟩ := l11_4_1_c A B T A'' B' T'' hCongABT2
        exact hForall A T A'' T'' ⟨out_trivial_c B A hAB, out_trivial_c B T (Ne.symm hBT),
          out_trivial_c B' A'' hOutB'A'A''.2.1, out_trivial_c B' T'' hT''neB',
          cong_symmetry_c B' A'' B A hCongB'A''BA, cong_symmetry_c B' T'' B T hCongB'T''BT⟩
      obtain ⟨C'', hBetA''T''C'', hCongT''C''TC⟩ := segment_construction A'' T'' T C
      have hCongAC : Cong A C A'' C'' :=
        l2_11_c A T C A'' T'' C'' hBetATC hBetA''T''C'' hCongAT
          (cong_symmetry_c T'' C'' T C hCongT''C''TC)
      have hATne : A ≠ T := by
        intro heq
        subst heq
        exact hNColABP hColTBP
      have hStepAB : Cong A B A'' B' :=
        cong_right_commutativity_c A B B' A''
          (cong_left_commutativity_c B A B' A'' (cong_symmetry_c B' A'' B A hCongB'A''BA))
      have hCongTBT''B' : Cong T B T'' B' :=
        cong_commutativity_c B T B' T'' (cong_symmetry_c B' T'' B T hCongB'T''BT)
      have hCongCB : Cong C B C'' B' :=
        five_segment A A'' T T'' C C'' B B' hCongAT
          (cong_symmetry_c T'' C'' T C hCongT''C''TC) hStepAB hCongTBT''B'
          hBetATC hBetA''T''C'' hATne
      have hCongBC : Cong B C B' C'' := cong_commutativity_c C B C'' B' hCongCB
      have hCongABC'' : CongA A B C A'' B' C'' :=
        cong3_conga_c A B C A'' B' C'' hAB hCB ⟨hStepAB, hCongAC, hCongBC⟩
      have hCongCT : Cong C T C'' T'' :=
        cong_commutativity_c T C T'' C'' (cong_symmetry_c T'' C'' T C hCongT''C''TC)
      have hCongBT : Cong B T B' T'' :=
        cong_commutativity_c T B T'' B' hCongTBT''B'
      have hCongCBT : CongA C B T C'' B' T'' :=
        cong3_conga_c C B T C'' B' T'' hCB (Ne.symm hBT) ⟨hCongCB, hCongCT, hCongBT⟩
      have hCongTBC : CongA T B C T'' B' C'' := conga_comm_c C B T C'' B' T'' hCongCBT
      have hBetTBP : Bet T B P := between_symmetry_c P B T hBetPBT
      have hBetT''B'P' : Bet T'' B' P' := between_symmetry_c P' B' T'' hBetP'B'T''
      have hCongPBC'' : CongA P B C P' B' C'' :=
        l11_13_c T B C T'' B' C'' P P' hCongTBC hBetTBP hPB hBetT''B'P' hP'B'
      have hCongP'C'C'' : CongA P' B' C' P' B' C'' :=
        conga_trans_c P' B' C' P B C P' B' C'' (conga_sym_c P B C P' B' C' hCongPBC) hCongPBC''
      have hColP'B'T'' : Col P' B' T'' := col_permutation_4_c B' P' T'' hColB'P'T''
      have hColC''A''T'' : Col C'' A'' T'' :=
        col_permutation_5_c C'' T'' A'' (col_permutation_3_c A'' T'' C'' (bet_col_c A'' T'' C'' hBetA''T''C''))
      have hCop_a : Coplanar P' C'' B' A'' := ⟨T'', Or.inr (Or.inl ⟨hColP'B'T'', hColC''A''T''⟩)⟩
      have hCop_b : Coplanar P' C'' B' A' :=
        col_cop_cop_c P' C'' B' A'' A' hCop_a hB'neA'' hColB'A''A'
      have hCopAPBC'' : Coplanar A' P' B' C'' := coplanar_perm_19_c P' C'' B' A' hCop_b
      have hCopFinal : Coplanar P' B' C' C'' :=
        coplanar_trans_1_c A' P' B' C' C'' hNColA'P'B' hCopAPBC' hCopAPBC''
      have hOutOrTS : Out B' C' C'' ∨ TS P' B' C' C'' :=
        conga_cop_or_out_ts_c P' B' C' C'' hCopFinal hCongP'C'C''
      rcases hOutOrTS with hOut | hTSfin
      · exact l11_10_c A B C A'' B' C'' A C A' C' hCongABC''
          (out_trivial_c B A hAB) (out_trivial_c B C hCB) hOutB'A'A'' hOut
      · have hTS_B'P'A''C' : TS B' P' A'' C' :=
          l9_5_c B' P' A' C' B' A'' hTS' (col_trivial_1_c B' P') hOutB'A'A''
        have hTS_B'P'C''C' : TS B' P' C'' C' :=
          l9_2_c B' P' C' C'' (invert_two_sides_c P' B' C' C'' hTSfin)
        have hOS_B'P'A''C'' : OS B' P' A'' C'' := ⟨C', hTS_B'P'A''C', hTS_B'P'C''C'⟩
        have hNColA''B'P' : ¬ Col A'' B' P' := by
          intro hCol
          apply hTS'.1
          exact col_permutation_4_c B' A' P'
            (col_transitivity_1_c B' A'' A' P' hB'neA''
              hColB'A''A' (col_permutation_4_c A'' B' P' hCol))
        have hColT''B'P' : Col T'' B' P' := col_permutation_2_c B' P' T'' hColB'P'T''
        have hTS_B'P'A''C'' : TS B' P' A'' C'' :=
          ⟨hNColA''B'P', hTS_B'P'C''C'.1, T'', hColT''B'P', hBetA''T''C''⟩
        exact absurd hOS_B'P'A''C'' (l9_9_c B' P' A'' C'' hTS_B'P'A''C'')
    · -- False sub-case: ¬ Bet P B T
      have hColPBT : Col P B T := col_permutation_3_c T B P hColTBP
      have hOutPBT : Out B P T := not_bet_out_c P B T hColPBT hNBetPBT
      obtain ⟨T'', hOutB'P'T'', hCongB'T''BT⟩ :=
        segment_construction_3_c B' P' B T (Ne.symm hP'B') hBT
      have hT''neB' : T'' ≠ B' := hOutB'P'T''.2.1
      have hColB'P'T'' : Col B' P' T'' := out_col_c B' P' T'' hOutB'P'T''
      obtain ⟨C'', hBetA''T''C'', hCongT''C''TC⟩ := segment_construction A'' T'' T C
      have hCongABT'A' : CongA A B T A' B' T'' :=
        l11_10_c A B P A' B' P' A T A' T'' hCongABP
          (out_trivial_c B A hAB) (l6_6_c B P T hOutPBT)
          (out_trivial_c B' A' hA'B') (l6_6_c B' P' T'' hOutB'P'T'')
      have hCongABT2 : CongA A B T A'' B' T'' :=
        l11_10_c A B T A' B' T'' A T A'' T'' hCongABT'A'
          (out_trivial_c B A hAB) (out_trivial_c B T (Ne.symm hBT))
          (l6_6_c B' A' A'' hOutB'A'A'') (out_trivial_c B' T'' hT''neB')
      have hCongAT : Cong A T A'' T'' := by
        obtain ⟨_, _, _, _, hForall⟩ := l11_4_1_c A B T A'' B' T'' hCongABT2
        exact hForall A T A'' T'' ⟨out_trivial_c B A hAB, out_trivial_c B T (Ne.symm hBT),
          out_trivial_c B' A'' hOutB'A'A''.2.1, out_trivial_c B' T'' hT''neB',
          cong_symmetry_c B' A'' B A hCongB'A''BA, cong_symmetry_c B' T'' B T hCongB'T''BT⟩
      have hCongAC : Cong A C A'' C'' :=
        l2_11_c A T C A'' T'' C'' hBetATC hBetA''T''C'' hCongAT
          (cong_symmetry_c T'' C'' T C hCongT''C''TC)
      have hATne : A ≠ T := by
        intro heq
        subst heq
        exact hNColABP hColTBP
      have hStepAB : Cong A B A'' B' :=
        cong_right_commutativity_c A B B' A''
          (cong_left_commutativity_c B A B' A'' (cong_symmetry_c B' A'' B A hCongB'A''BA))
      have hCongTBT''B' : Cong T B T'' B' :=
        cong_commutativity_c B T B' T'' (cong_symmetry_c B' T'' B T hCongB'T''BT)
      have hCongCB : Cong C B C'' B' :=
        five_segment A A'' T T'' C C'' B B' hCongAT
          (cong_symmetry_c T'' C'' T C hCongT''C''TC) hStepAB hCongTBT''B'
          hBetATC hBetA''T''C'' hATne
      have hCongBC : Cong B C B' C'' := cong_commutativity_c C B C'' B' hCongCB
      have hCongABC'' : CongA A B C A'' B' C'' :=
        cong3_conga_c A B C A'' B' C'' hAB hCB ⟨hStepAB, hCongAC, hCongBC⟩
      have hCongCT : Cong C T C'' T'' :=
        cong_commutativity_c T C T'' C'' (cong_symmetry_c T'' C'' T C hCongT''C''TC)
      have hCongBT : Cong B T B' T'' :=
        cong_commutativity_c T B T'' B' hCongTBT''B'
      have hCongCBT : CongA C B T C'' B' T'' :=
        cong3_conga_c C B T C'' B' T'' hCB (Ne.symm hBT) ⟨hCongCB, hCongCT, hCongBT⟩
      have hC''neB' : C'' ≠ B' := by
        intro heq
        rw [heq] at hCongCB
        exact hCB (cong_identity C B B' hCongCB)
      have hCongPBC'' : CongA P B C P' B' C'' :=
        l11_10_c T B C T'' B' C'' P C P' C'' (conga_comm_c C B T C'' B' T'' hCongCBT)
          hOutPBT (out_trivial_c B C hCB) hOutB'P'T'' (out_trivial_c B' C'' hC''neB')
      have hCongP'C'C'' : CongA P' B' C' P' B' C'' :=
        conga_trans_c P' B' C' P B C P' B' C'' (conga_sym_c P B C P' B' C' hCongPBC) hCongPBC''
      have hColP'B'T'' : Col P' B' T'' := col_permutation_4_c B' P' T'' hColB'P'T''
      have hColC''A''T'' : Col C'' A'' T'' :=
        col_permutation_5_c C'' T'' A'' (col_permutation_3_c A'' T'' C'' (bet_col_c A'' T'' C'' hBetA''T''C''))
      have hCop_a : Coplanar P' C'' B' A'' := ⟨T'', Or.inr (Or.inl ⟨hColP'B'T'', hColC''A''T''⟩)⟩
      have hCop_b : Coplanar P' C'' B' A' :=
        col_cop_cop_c P' C'' B' A'' A' hCop_a hB'neA'' hColB'A''A'
      have hCopAPBC'' : Coplanar A' P' B' C'' := coplanar_perm_19_c P' C'' B' A' hCop_b
      have hCopFinal : Coplanar P' B' C' C'' :=
        coplanar_trans_1_c A' P' B' C' C'' hNColA'P'B' hCopAPBC' hCopAPBC''
      have hOutOrTS : Out B' C' C'' ∨ TS P' B' C' C'' :=
        conga_cop_or_out_ts_c P' B' C' C'' hCopFinal hCongP'C'C''
      have hOutB'C'C'' : Out B' C' C'' := by
        rcases hOutOrTS with hOut | hTSfin
        · exact hOut
        · have hTS_B'P'A''C' : TS B' P' A'' C' :=
            l9_5_c B' P' A' C' B' A'' hTS' (col_trivial_1_c B' P') hOutB'A'A''
          have hTS_B'P'C''C' : TS B' P' C'' C' :=
            l9_2_c B' P' C' C'' (invert_two_sides_c P' B' C' C'' hTSfin)
          have hOS_B'P'A''C'' : OS B' P' A'' C'' := ⟨C', hTS_B'P'A''C', hTS_B'P'C''C'⟩
          have hNColA''B'P' : ¬ Col A'' B' P' := by
            intro hCol
            apply hTS'.1
            exact col_permutation_4_c B' A' P'
              (col_transitivity_1_c B' A'' A' P' hB'neA''
                hColB'A''A' (col_permutation_4_c A'' B' P' hCol))
          have hColT''B'P' : Col T'' B' P' := col_permutation_2_c B' P' T'' hColB'P'T''
          have hTS_B'P'A''C'' : TS B' P' A'' C'' :=
            ⟨hNColA''B'P', hTS_B'P'C''C'.1, T'', hColT''B'P', hBetA''T''C''⟩
          exact absurd hOS_B'P'A''C'' (l9_9_c B' P' A'' C'' hTS_B'P'A''C'')
      exact l11_10_c A B C A'' B' C'' A C A' C' hCongABC''
        (out_trivial_c B A hAB) (out_trivial_c B C hCB) hOutB'A'A'' hOutB'C'C''
theorem l11_22b_c :
    ∀ (A B C P A' B' C' P' : Tpoint), OS B P A C ∧ OS B' P' A' C' ∧ CongA A B P A' B' P' ∧ CongA P B C P' B' C' → CongA A B C A' B' C' := by
  intro A B C P A' B' C' P' h
  obtain ⟨hOS, hOS', hCongABP, hCongPBC⟩ := h
  have hAB : A ≠ B := conga_diff1_c A B P A' B' P' hCongABP
  have hA'B' : A' ≠ B' := conga_diff45_c A B P A' B' P' hCongABP
  -- Construct D beyond B on line A-B with Cong B D A B, and likewise D'.
  obtain ⟨D, hBetABD, hCongBDAB⟩ := segment_construction A B A B
  obtain ⟨D', hBetA'B'D', hCongB'D'A'B'⟩ := segment_construction A' B' A' B'
  have hBD : B ≠ D := cong_diff_3_c B D A B hAB hCongBDAB
  have hB'D' : B' ≠ D' := cong_diff_3_c B' D' A' B' hA'B' hCongB'D'A'B'
  -- Step 2: CongA D B P D' B' P' by extending the shared leg through the vertex.
  have hCongDBP_D'B'P' : CongA D B P D' B' P' :=
    l11_13_c A B P A' B' P' D D' hCongABP hBetABD (Ne.symm hBD) hBetA'B'D' (Ne.symm hB'D')
  -- Unpack OS B P A C to get ¬ Col A B P, then show D is off line B P too.
  have hOScopy := hOS
  obtain ⟨_R, hTS_BP_A_R, _hTS_BP_C_R⟩ := hOScopy
  have hNColABP : ¬ Col A B P := hTS_BP_A_R.1
  have hNColDBP : ¬ Col D B P := by
    intro hColDBP
    apply hNColABP
    have hColABD : Col A B D := bet_col_c A B D hBetABD
    have hColBDA : Col B D A := col_permutation_1_c A B D hColABD
    have hColBDP : Col B D P := col_permutation_4_c D B P hColDBP
    have hColBAP : Col B A P := col_transitivity_1_c B D A P hBD hColBDA hColBDP
    exact col_permutation_4_c B A P hColBAP
  have hTS_BP_A_D : TS B P A D :=
    ⟨hNColABP, hNColDBP, B, col_trivial_1_c B P, hBetABD⟩
  have hTS_BP_D_C : TS B P D C :=
    l9_2_c B P C D (l9_8_2_c B P A C D hTS_BP_A_D hOS)
  -- Primed side: identical argument for D', C'.
  have hOS'copy := hOS'
  obtain ⟨_R', hTS_B'P'_A'_R', _hTS_B'P'_C'_R'⟩ := hOS'copy
  have hNColA'B'P' : ¬ Col A' B' P' := hTS_B'P'_A'_R'.1
  have hNColD'B'P' : ¬ Col D' B' P' := by
    intro hColD'B'P'
    apply hNColA'B'P'
    have hColA'B'D' : Col A' B' D' := bet_col_c A' B' D' hBetA'B'D'
    have hColB'D'A' : Col B' D' A' := col_permutation_1_c A' B' D' hColA'B'D'
    have hColB'D'P' : Col B' D' P' := col_permutation_4_c D' B' P' hColD'B'P'
    have hColB'A'P' : Col B' A' P' := col_transitivity_1_c B' D' A' P' hB'D' hColB'D'A' hColB'D'P'
    exact col_permutation_4_c B' A' P' hColB'A'P'
  have hTS_B'P'_A'_D' : TS B' P' A' D' :=
    ⟨hNColA'B'P', hNColD'B'P', B', col_trivial_1_c B' P', hBetA'B'D'⟩
  have hTS_B'P'_D'_C' : TS B' P' D' C' :=
    l9_2_c B' P' C' D' (l9_8_2_c B' P' A' C' D' hTS_B'P'_A'_D' hOS')
  -- Step 3: CongA D B C D' B' C' via l11_22a_c.
  have hCongDBC_D'B'C' : CongA D B C D' B' C' :=
    l11_22a_c D B C P D' B' C' P' ⟨hTS_BP_D_C, hTS_B'P'_D'_C', hCongDBP_D'B'P', hCongPBC⟩
  -- Step 4: fold back through D, D' via l11_13_c to close the goal.
  exact l11_13_c D B C D' B' C' A A' hCongDBC_D'B'C'
    (between_symmetry_c A B D hBetABD) hAB
    (between_symmetry_c A' B' D' hBetA'B'D') hA'B'
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
theorem out321_inangle_c :
    ∀ (A B C P : Tpoint), C ≠ B → Out B A P → InAngle P A B C := by
  intro b0 b1 b2 b3 b4 b5
  have H1 := out_distinct_c b1 b0 b3 b5
  have H2 := H1
  obtain ⟨H3, H4⟩ := H2
  exact col_in_angle_c b0 b1 b2 b3 H3 b4 H4 (Or.inl b5)
theorem inangle1123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle A A B C :=
  fun b0 b1 b2 b3 b4 =>
  out321_inangle_c b0 b1 b2 b0 b4 (out_trivial b3)
theorem out341_inangle_c :
    ∀ (A B C P : Tpoint), A ≠ B → Out B C P → InAngle P A B C := by
  intro b0 b1 b2 b3 b4 b5
  have H1 := out_distinct_c b1 b2 b3 b5
  have H2 := H1
  obtain ⟨H3, H4⟩ := H2
  exact col_in_angle_c b0 b1 b2 b3 b4 H3 H4 (Or.inr b5)
theorem inangle3123_c :
    ∀ (A B C : Tpoint), A ≠ B → C ≠ B → InAngle C A B C :=
  fun b0 b1 b2 b3 b4 =>
  out341_inangle_c b0 b1 b2 b2 b3 (out_trivial b4)
theorem in_angle_two_sides_c :
    ∀ (A B C P : Tpoint), ¬ Col B A P → ¬ Col B C P → InAngle P A B C → TS P B A C := by
  intro A B C P hCol1 hCol2 hInAngle
  obtain ⟨hAB, hCB, hPB, X, hBetAXC, hXorOut⟩ := hInAngle
  have hNColAPB : ¬ Col A P B := fun h => hCol1 (col_permutation_2_c A P B h)
  have hNColCPB : ¬ Col C P B := fun h => hCol2 (col_permutation_2_c C P B h)
  rcases hXorOut with hXeqB | hOutBXP
  · subst hXeqB
    exact ⟨hNColAPB, hNColCPB, X, col_trivial_3_c X P, hBetAXC⟩
  · exact ⟨hNColAPB, hNColCPB, X, col_permutation_1_c B X P (out_col_c B X P hOutBXP), hBetAXC⟩
theorem in_angle_out_c :
    ∀ (A B C P : Tpoint), Out B A C → InAngle P A B C → Out B A P := by
  intro A B C P h1 h2
  obtain ⟨hAB, hCB, hPB, X, hAXC, hcase⟩ := h2
  rcases hcase with heq | hXP
  · rw [heq] at hAXC
    have hfalse : False := not_bet_and_out_c A B C ⟨hAXC, h1⟩
    Tfinish
  · have hkey := out2_bet_out_c A B C X P h1 hXP hAXC
    Tfinish
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
    ∀ (P A B C A' : Tpoint), InAngle P A B C → ¬ Bet A B C → Out B A' A → InAngle P A' B C := by
  intro P A B C A' hIn hNBet hOutA'
  obtain ⟨hAB, hCB, hPB, X, hAXC, hXcase⟩ := hIn
  obtain ⟨hA'B, hAB2, hOutDisj⟩ := hOutA'
  refine ⟨hA'B, hCB, hPB, ?_⟩
  rcases hOutDisj with hBetBA'A | hBetBAA'
  · -- Bet B A' A
    obtain ⟨T, hA'TC, hXTB⟩ :=
      inner_pasch B C A A' X hBetBA'A (between_symmetry_c A X C hAXC)
    refine ⟨T, hA'TC, Or.inr ?_⟩
    rcases hXcase with hXeqB | hOutBXP
    · exfalso; apply hNBet; rw [hXeqB] at hAXC; exact hAXC
    · obtain ⟨hXB2, hPB2, hOutDisj2⟩ := hOutBXP
      refine ⟨?_, hPB2, ?_⟩
      · intro hTeqB
        rw [hTeqB] at hA'TC
        exact hNBet (between_symmetry_c C B A
          (outer_transitivity_between_c C B A' A (between_symmetry_c A' B C hA'TC) hBetBA'A (Ne.symm hA'B)))
      · rcases hOutDisj2 with hBetBXP | hBetBPX
        · exact Or.inl (between_exchange4_c B T X P (between_symmetry_c X T B hXTB) hBetBXP)
        · exact l5_3_c B T P X (between_symmetry_c X T B hXTB) hBetBPX
  · -- Bet B A A'
    obtain ⟨T, hA'TC, hBXT⟩ :=
      outer_pasch_c A' C A B X (between_symmetry_c B A A' hBetBAA') (between_symmetry_c A X C hAXC)
    refine ⟨T, hA'TC, Or.inr ?_⟩
    rcases hXcase with hXeqB | hOutBXP
    · exfalso; apply hNBet; rw [hXeqB] at hAXC; exact hAXC
    · obtain ⟨hXB2, hPB2, hOutDisj2⟩ := hOutBXP
      refine ⟨?_, hPB2, ?_⟩
      · intro hTeqB
        rw [hTeqB] at hBXT
        have hBX : B = X := between_identity B X hBXT
        exact hXB2 hBX.symm
      · rcases hOutDisj2 with hBetBXP | hBetBPX
        · exact l5_1_c B X T P (Ne.symm hXB2) hBXT hBetBXP
        · exact Or.inr (between_exchange4_c B P X T hBetBPX hBXT)
theorem l11_25_c :
    ∀ (P A B C A' C' P' : Tpoint), InAngle P A B C → Out B A' A → Out B C' C → Out B P' P → InAngle P' A' B C' := by
  intro P A B C A' C' P' hIn hOut0 hOut1 hOut2
  rcases bet_dec_c A B C with hBetABC | hNotBetABC
  · exact ⟨hOut0.1, hOut1.1, hOut2.1, B,
      bet_out_out_bet_c A B C A' C' hBetABC (l6_6_c B A' A hOut0) (l6_6_c B C' C hOut1),
      Or.inl rfl⟩
  · have hCB : C ≠ B := hIn.2.1
    have hInA'BC : InAngle P A' B C := l11_25_aux_c P A B C A' hIn hNotBetABC hOut0
    have hInA'BC' : InAngle P A' B C' :=
      l11_24_c P C' B A'
        (l11_25_aux_c P C B A' C'
          (l11_24_c P A' B C hInA'BC)
          (fun H5 => hNotBetABC (between_symmetry_c C B A
            (bet_out_out_bet_c C B A' C A H5 (out_trivial hCB) hOut0)))
          hOut1)
    obtain ⟨_, _, _, X, hA'XC', hXcase2⟩ := hInA'BC'
    rcases hXcase2 with hXeqB | hOutBXP
    · exfalso
      rw [hXeqB] at hA'XC'
      exact hNotBetABC (bet_out_out_bet_c A' B C' A C hA'XC' hOut0 hOut1)
    · exact ⟨hOut0.1, hOut1.1, hOut2.1, X, hA'XC', Or.inr (l6_7_c B X P P' hOutBXP (l6_6_c B P' P hOut2))⟩
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
theorem bet_conga_bet_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A B C → CongA A B C A' B' C' → Bet A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H1, H2⟩ := b7
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨A0, H7⟩ := H6
  obtain ⟨C0, H8⟩ := H7
  obtain ⟨A1, H9⟩ := H8
  obtain ⟨C1, H10⟩ := H9
  obtain ⟨H11, H12⟩ := H10
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H20
  obtain ⟨H23, H24⟩ := H22
  obtain ⟨H25, H26⟩ := H24
  have H27 := outer_transitivity_between
    (between_symmetry (outer_transitivity_between (between_symmetry b6) H11 (Ne.symm H1)))
    H15 (Ne.symm H3)
  have H28 : Cong_3 A0 b1 C0 A1 b4 C1 :=
    ⟨cong_right_commutativity (l2_11 (between_symmetry H11) H19 (by cong_r) (by cong_r)),
     H26,
     cong_right_commutativity (l2_11 H15 (between_symmetry H23) (by cong_r) (by cong_r))⟩
  have H29 := l4_6 H27 H28
  exact between_inner_transitivity (between_exchange3 (between_symmetry H19) H29) H23

theorem in_angle_one_side_c :
    ∀ (A B C P : Tpoint), ¬ Col A B C → ¬ Col B A P → InAngle P A B C → OS A B P C := by
  intro A B C P hNColABC hNColBAP hInAngle
  obtain ⟨hAB, hCB, hPB, X, hAXC, hcase⟩ := hInAngle
  rcases hcase with hXB | hOutBXP
  · -- X = B: Bet A X C becomes Bet A B C, giving Col A B C, contradicting hNColABC.
    rw [hXB] at hAXC
    exact absurd (bet_col_c A B C hAXC) hNColABC
  · -- Out B X P: construct C' extending C-A beyond A with Cong A C' C A.
    obtain ⟨C', hBetCAC', hCongAC'CA⟩ := segment_construction C A C A
    -- A ≠ C': else Cong A C' C A degenerates to force C = A, contradicting hNColABC
    -- (which would then say ¬ Col A B A, false by col_trivial_3).
    have hAC' : A ≠ C' := by
      intro heq
      subst heq
      apply hNColABC
      have hCA : C = A := cong_identity C A A (cong_symmetry hCongAC'CA)
      rw [hCA]
      exact col_trivial_3_c A B
    have hColCAC' : Col C A C' := bet_col_c C A C' hBetCAC'
    -- ¬ Col C' A B: else {C,A,C'} and {C',A,B} merge on A≠C', forcing Col A B C.
    have hNColC'AB : ¬ Col C' A B := by
      intro hColC'AB
      apply hNColABC
      colr
    have hBneX : B ≠ X := Ne.symm hOutBXP.1
    have hColBXP : Col B X P := out_col hOutBXP
    -- ¬ Col X A B: else {X,A,B} and {B,X,P} merge on B≠X, forcing Col B A P.
    have hNColXAB : ¬ Col X A B := by
      intro hColXAB
      apply hNColBAP
      colr
    -- Bet X A C': X between A,C and A between C,C' nest to put A between X,C'.
    have hBetXAC' : Bet X A C' := between_exchange3 (between_symmetry hAXC) hBetCAC'
    have hTSAXC' : TS A B X C' := ⟨hNColXAB, hNColC'AB, A, col_trivial_1_c A B, hBetXAC'⟩
    -- Transport TS A B X C' across Out B X P to TS A B P C' via l9_5.
    have hTSPC' : TS A B P C' :=
      l9_5_c A B X C' B P hTSAXC' (col_trivial_3_c B A) hOutBXP
    have hTSCC' : TS A B C C' :=
      ⟨fun hColCAB => hNColABC (col_permutation_1_c C A B hColCAB),
       hNColC'AB, A, col_trivial_1_c A B, hBetCAC'⟩
    exact ⟨C', hTSPC', hTSCC'⟩
theorem inangle_one_side_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q := sorry

theorem inangle_one_side2_c :
    ∀ (A B C P Q : Tpoint), ¬ Col A B C → ¬ Col A B P → ¬ Col A B Q → ¬ Col C B P → ¬ Col C B Q → InAngle P A B C → InAngle Q A B C → OS A B P Q ∧ OS C B P Q :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
  ⟨(inangle_one_side_c b0 b1 b2 b3 b4 b5 b6 b7 b10 b11), (inangle_one_side_c b2 b1 b0 b3 b4 (not_col_permutation_5_c b2 b0 b1 (not_col_permutation_2_c b0 b1 b2 b5)) b8 b9 (l11_24_c b3 b0 b1 b2 b10) (l11_24_c b4 b0 b1 b2 b11))⟩
theorem col_conga_col_c :
    ∀ (A B C D E F : Tpoint), Col A B C → CongA A B C D E F → Col D E F := by
  intro A B C D E F h1 h2
  rcases h1 with hb | hb | hb
  · have hBet : Bet D E F := bet_conga_bet_c A B C D E F hb h2
    Tfinish
  · have hOut : Out E D F := l11_21_a_c A B C D E F (l6_6_c B C A (bet_out_c B C A h2.2.1 hb)) h2
    have hCol : Col E D F := out_col_c E D F hOut
    Tfinish
  · have hOut : Out E D F := l11_21_a_c A B C D E F (bet_out_c B A C h2.1 (between_symmetry hb)) h2
    have hCol : Col E D F := out_col_c E D F hOut
    Tfinish
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
    exact ⟨x0, (⟨x1, (coplanar_perm_1_c b3 b4 b5 x0 (col_coplanar_c b3 b4 b5 x0 x))⟩)⟩
  · have o0 := col_dec_c b0 b1 b2
    rcases o0 with x0 | x0
    · have e := angle_construction_3_c b0 b1 b2 b3 b4 b6 b7 b8
      obtain ⟨x1, x2⟩ := e
      exact ⟨x1, (⟨x2, (⟨x1, (Or.inl (⟨(col_conga_col_c b0 b1 b2 b3 b4 x1 x0 x2), (col_trivial_3_c x1 b5)⟩))⟩)⟩)⟩
    · have e := angle_construction_1_c b0 b1 b2 b3 b4 b5 x0 x
      obtain ⟨x1, x2⟩ := e
      obtain ⟨x3, x4⟩ := x2
      exact ⟨x1, (⟨x3, ((let H7 := os_coplanar_c b3 b4 x1 b5 x4; H7))⟩)⟩
theorem lea_distincts_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨x, x0⟩ := b6
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x1
  obtain ⟨x5, x6⟩ := x4
  exact ⟨(conga_diff1_c b0 b1 b2 b3 b4 x x2), (⟨(conga_diff2_c b0 b1 b2 b3 b4 x x2), (⟨x3, x5⟩)⟩)⟩
theorem l11_29_a_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F := by
  intro A B C D E F hLeA
  obtain ⟨P, hInP, hCongABCDEP⟩ := hLeA
  have hDE : D ≠ E := hInP.1
  have hFE : F ≠ E := hInP.2.1
  have hPE : P ≠ E := hInP.2.2.1
  have hAB : A ≠ B := hCongABCDEP.1
  have hCB : C ≠ B := hCongABCDEP.2.1
  rcases or_bet_out_c A B C with hBet | hOut | hNCol
  · -- Case 1: Bet A B C. Answer Q := C.
    have hBetDEP : Bet D E P := bet_conga_bet_c A B C D E P hBet hCongABCDEP
    refine ⟨C, inangle3123_c A B C hAB hCB, ?_⟩
    obtain ⟨_, _, _, X, hDXF, hXcase⟩ := hInP
    rcases hXcase with hXeqE | hOutEXP
    · -- X = E: Bet D E F directly, so l5_2 gives Bet E F P ∨ Bet E P F.
      have hBetDEF : Bet D E F := by rw [hXeqE] at hDXF; exact hDXF
      have hOr : Bet E F P ∨ Bet E P F := l5_2_c D E F P hDE hBetDEF hBetDEP
      exact l11_10_c A B C D E P A C D F hCongABCDEP
        (out_trivial hAB) (out_trivial hCB) (out_trivial hDE) ⟨hFE, hPE, hOr⟩
    · -- Out E X P: chase betweenness to get Out E P F, then transport via l11_10.
      have hOutEPF : Out E P F := by
        rcases hOutEXP.2.2 with hBetEXP | hBetEPX
        · have hDEX : Bet D E X := between_inner_transitivity_c D E X P hBetDEP hBetEXP
          have hBetDEF : Bet D E F := between_exchange4_c D E X F hDEX hDXF
          exact ⟨hPE, hFE, l5_2_c D E P F hDE hBetDEP hBetDEF⟩
        · have hDPX : Bet D P X :=
            outer_transitivity_between2_c D E P X hBetDEP hBetEPX (Ne.symm hPE)
          have hDPF : Bet D P F := between_exchange4_c D P X F hDPX hDXF
          have hBetEPF : Bet E P F := between_exchange3_c D E P F hBetDEP hDPF
          exact ⟨hPE, hFE, Or.inl hBetEPF⟩
      exact l11_10_c A B C D E P A C D F hCongABCDEP
        (out_trivial hAB) (out_trivial hCB) (out_trivial hDE) (l6_6_c E P F hOutEPF)
  · -- Case 2: Out B A C. Construct Q with CongA D E F A B Q.
    obtain ⟨Q, hCongDEFABQ⟩ := angle_construction_3_c D E F A B hDE hFE hAB
    exact ⟨Q, ⟨hAB, conga_diff56_c D E F A B Q hCongDEFABQ, hCB, A,
      between_trivial2_c A Q, Or.inr hOut⟩, conga_sym_c D E F A B Q hCongDEFABQ⟩
  · -- Case 3: ~ Col A B C.
    rcases or_bet_out_c D E F with hBetDEF | hOutEDF | hNColDEF
    · -- Case 3a: Bet D E F. Prolong A B by |EF|.
      obtain ⟨Q, hBetABQ, hCongBQEF⟩ := segment_construction A B E F
      have hQB : Q ≠ B := by
        intro heq
        subst heq
        have hcong2 : Cong E F Q Q := cong_symmetry_c Q Q E F hCongBQEF
        exact hFE (cong_identity E F Q hcong2).symm
      exact ⟨Q, ⟨hAB, hQB, hCB, B, hBetABQ, Or.inl rfl⟩,
        conga_line_c A B Q D E F hAB (Ne.symm hQB) hDE (Ne.symm hFE) hBetABQ hBetDEF⟩
    · -- Case 3b: Out E D F. Contradicts ~ Col A B C.
      exact absurd
        (col_permutation_4_c B A C (out_col_c B A C
          (l11_21_a_c D E P A B C (in_angle_out_c D E F P hOutEDF hInP)
            (conga_sym_c A B C D E P hCongABCDEP))))
        hNCol
    · -- Case 3c: ~ Col D E F. The big case.
      obtain ⟨Q, hCongDEFABQ, hOSABQC⟩ := angle_construction_1_c D E F A B C hNColDEF hNCol
      have hQB : Q ≠ B := conga_diff56_c D E F A B Q hCongDEFABQ
      obtain ⟨DD, hOutEDDD, hCongEDDBA⟩ :=
        segment_construction_3_c E D B A (Ne.symm hDE) (Ne.symm hAB)
      obtain ⟨FF, hOutEFFF, hCongEFFBQ⟩ :=
        segment_construction_3_c E F B Q (Ne.symm hFE) (Ne.symm hQB)
      have hDDE : DD ≠ E := hOutEDDD.2.1
      have hFFE : FF ≠ E := hOutEFFF.2.1
      have hInPDDEFF : InAngle P DD E FF :=
        l11_25_c P D E F DD FF P hInP
          (l6_6_c E D DD hOutEDDD) (l6_6_c E F FF hOutEFFF) (out_trivial hPE)
      have hInPDDEFFCopy := hInPDDEFF
      obtain ⟨_, _, _, X, hDDXFF, hXcase⟩ := hInPDDEFFCopy
      rcases hXcase with hXeqE | hOutEXP
      · -- X = E forces Bet D E F, contradicting ~ Col D E F.
        have hBetDDEFF : Bet DD E FF := by rw [hXeqE] at hDDXFF; exact hDDXFF
        have hBetDEF' : Bet D E F :=
          bet_out_out_bet_c DD E FF D F hBetDDEFF (l6_6_c E D DD hOutEDDD) (l6_6_c E F FF hOutEFFF)
        exact absurd (Or.inl hBetDEF' : Col D E F) hNColDEF
      · -- Main branch: build CC, then the key l11_22b congruence, then close.
        have hXE : X ≠ E := hOutEXP.1
        obtain ⟨CC, hOutBCCC, hCongBCCEX⟩ :=
          segment_construction_3_c B C E X (Ne.symm hCB) (Ne.symm hXE)
        have hCCB : CC ≠ B := hOutBCCC.2.1
        have hCongABCCDDEX : CongA A B CC DD E X :=
          l11_10_c A B C D E P A CC DD X hCongABCDEP
            (out_trivial hAB) (l6_6_c B C CC hOutBCCC) (l6_6_c E D DD hOutEDDD) hOutEXP
        have hCongACCDDX : Cong A CC DD X :=
          cong2_conga_cong_c A B CC DD E X hCongABCCDDEX
            (cong_symmetry_c DD E A B (cong_commutativity_c E DD B A hCongEDDBA)) hCongBCCEX
        have hCongABQDDEFF : CongA A B Q DD E FF :=
          l11_10_c A B Q D E F A Q DD FF (conga_sym_c D E F A B Q hCongDEFABQ)
            (out_trivial hAB) (out_trivial hQB) (l6_6_c E D DD hOutEDDD) (l6_6_c E F FF hOutEFFF)
        have hCongAQDDFF : Cong A Q DD FF :=
          cong2_conga_cong_c A B Q DD E FF hCongABQDDEFF
            (cong_symmetry_c DD E A B (cong_commutativity_c E DD B A hCongEDDBA))
            (cong_symmetry_c E FF B Q hCongEFFBQ)
        have hOSBAQCC : OS B A Q CC :=
          out_out_one_side_c B A Q C CC (invert_one_side_c A B Q C hOSABQC) hOutBCCC
        have hOSBACCQ : OS B A CC Q := one_side_symmetry_c B A Q CC hOSBAQCC
        have hInXDDEFF : InAngle X DD E FF :=
          l11_25_c P DD E FF DD FF X hInPDDEFF (out_trivial hDDE) (out_trivial hFFE) hOutEXP
        have hNColDDEFF : ¬ Col DD E FF := fun hCol =>
          hNColDEF (col_out2_col_c DD E FF D F hCol (l6_6_c E D DD hOutEDDD) (l6_6_c E F FF hOutEFFF))
        have hNColEDDX : ¬ Col E DD X := fun hCol =>
          hNCol (col_conga_col_c D E P A B C
            (col_out2_col_c DD E X D P (col_permutation_4_c E DD X hCol) (l6_6_c E D DD hOutEDDD) hOutEXP)
            (conga_sym_c A B C D E P hCongABCDEP))
        have hOSDDEXFF : OS DD E X FF :=
          in_angle_one_side_c DD E FF X hNColDDEFF hNColEDDX hInXDDEFF
        have hOSEDDXFF : OS E DD X FF := invert_one_side_c DD E X FF hOSDDEXFF
        have hCongCCBAXEDD : CongA CC B A X E DD :=
          conga_sym_c X E DD CC B A
            (l11_10_c P E D C B A X DD CC A
              (conga_sym_c C B A P E D (conga_comm_c A B C D E P hCongABCDEP))
              hOutEXP (l6_6_c E D DD hOutEDDD) (l6_6_c B C CC hOutBCCC) (out_trivial hAB))
        have hCongCCBQXEFF : CongA CC B Q X E FF :=
          l11_22b_c CC B Q A X E FF DD ⟨hOSBACCQ, hOSEDDXFF, hCongCCBAXEDD, hCongABQDDEFF⟩
        have hCongCCQXFF : Cong CC Q X FF :=
          cong2_conga_cong_c CC B Q X E FF hCongCCBQXEFF
            (cong_commutativity_c B CC E X hCongBCCEX) (cong_symmetry_c E FF B Q hCongEFFBQ)
        have hInAngleCCABQ : InAngle CC A B Q :=
          ⟨hAB, hQB, hCCB, CC,
            l4_6_c DD X FF A CC Q hDDXFF
              ⟨cong_symmetry_c A CC DD X hCongACCDDX,
               cong_symmetry_c A Q DD FF hCongAQDDFF,
               cong_symmetry_c CC Q X FF hCongCCQXFF⟩,
            Or.inr (out_trivial hCCB)⟩
        refine ⟨Q, ?_, conga_sym_c D E F A B Q hCongDEFABQ⟩
        exact l11_25_c CC A B Q A Q C hInAngleCCABQ (out_trivial hAB) (out_trivial hQB) hOutBCCC
theorem in_angle_line_c :
    ∀ (A B C P : Tpoint), P ≠ B → A ≠ B → C ≠ B → Bet A B C → InAngle P A B C := by
  intro A B C P hPB hAB hCB hBet
  exact ⟨hAB, ⟨hCB, ⟨hPB, ⟨B, ⟨hBet, Or.inl rfl⟩⟩⟩⟩⟩
theorem l11_29_b_c :
    ∀ (A B C D E F : Tpoint), (∃ (Q : Tpoint), InAngle C A B Q ∧ CongA A B Q D E F) → LeA A B C D E F := by
  intro A B C D E F hEx
  obtain ⟨Q, hInAngleC, hCongABQDEF⟩ := hEx
  have hInAngleCopy := hInAngleC
  obtain ⟨hAB, hQB, hCB, X, hBetAXQ, hXcase⟩ := hInAngleC
  have hDE : D ≠ E := hCongABQDEF.2.2.1
  have hFE : F ≠ E := hCongABQDEF.2.2.2.1
  rcases hXcase with hXB | hG1
  · -- X = B
    have hBetABQ : Bet A B Q := hXB ▸ hBetAXQ
    have hBetDEF : Bet D E F := bet_conga_bet_c A B Q D E F hBetABQ hCongABQDEF
    obtain ⟨P, hCongABCDEP⟩ := angle_construction_3_c A B C D E hAB hCB hDE
    have hPE : P ≠ E := hCongABCDEP.2.2.2.1
    have hPInAngleDEF : InAngle P D E F := in_angle_line_c D E F P hPE hDE hFE hBetDEF
    exact ⟨P, hPInAngleDEF, hCongABCDEP⟩
  · -- B Out X C
    have hXB' := hG1.1
    have hCB' := hG1.2.1
    have hBetCase := hG1.2.2
    obtain ⟨DD, hOutEDDD, hCongEDDBA⟩ := segment_construction_3_c E D B A (Ne.symm hDE) (Ne.symm hAB)
    have hG3 : DD ≠ E := out_diff2_c E D DD hOutEDDD
    obtain ⟨FF, hOutEFFF, hCongEFFBQ⟩ := segment_construction_3_c E F B Q (Ne.symm hFE) (Ne.symm hQB)
    have hG3B : FF ≠ E := out_diff2_c E F FF hOutEFFF
    have hL4 : Out E DD D := l6_6_c E D DD hOutEDDD
    have hL5 : Out E FF F := l6_6_c E F FF hOutEFFF
    rcases or_bet_out_c A B C with hG5 | hG8 | hR1
    · -- Bet A B C
      have hG6 : InAngle F D E F := inangle3123_c D E F hDE hFE
      have hOutBQC : Out B Q C := by
        rcases hBetCase with hBetBXC | hBetBCX
        · have hBetABX : Bet A B X := between_inner_transitivity_c A B X C hG5 hBetBXC
          have hBetBXQ : Bet B X Q := between_exchange3_c A B X Q hBetABX hBetAXQ
          have hOutBXQ : Out B X Q := bet_out_c B X Q hXB' hBetBXQ
          exact l6_7_c B Q X C (l6_6_c B X Q hOutBXQ) hG1
        · have hBetABX : Bet A B X := outer_transitivity_between_c A B C X hG5 hBetBCX (Ne.symm hCB')
          have hBetBXQ : Bet B X Q := between_exchange3_c A B X Q hBetABX hBetAXQ
          have hBetBCQ : Bet B C Q := between_exchange4_c B C X Q hBetBCX hBetBXQ
          exact l6_6_c B C Q (bet_out_c B C Q hCB' hBetBCQ)
      have hCongABCABQ : CongA A B C A B Q := out2_conga_c A B C A Q (out_trivial_c B A hAB) hOutBQC
      have hCongABCDEF : CongA A B C D E F := conga_trans_c A B C A B Q D E F hCongABCABQ hCongABQDEF
      exact ⟨F, hG6, hCongABCDEF⟩
    · -- B Out A C
      have hG9 : InAngle D D E F := inangle1123_c D E F hDE hFE
      have hCongABCDED : CongA A B C D E D := l11_21_b_c A B C D E D hG8 (out_trivial_c E D hDE)
      exact ⟨D, hG9, hCongABCDED⟩
    · -- ¬ Col A B C
      rcases or_bet_out_c A B Q with hR3 | hS1 | hS3B
      · -- Bet A B Q
        obtain ⟨P, hCongABCDEP⟩ := angle_construction_3_c A B C D E hAB hCB hDE
        have hR6 : P ≠ E := hCongABCDEP.2.2.2.1
        have hBetDEF_R : Bet D E F := bet_conga_bet_c A B Q D E F hR3 hCongABQDEF
        have hR5 : InAngle P D E F := in_angle_line_c D E F P hR6 hDE hFE hBetDEF_R
        exact ⟨P, hR5, hCongABCDEP⟩
      · -- Out B A Q
        have hS2 : Out B A C := l6_7_c B A X C (out_bet_out_1_c A X Q B hS1 hBetAXQ) hG1
        have hS3 : Col A B C := col_permutation_4_c B A C (out_col_c B A C hS2)
        exact absurd hS3 hR1
      · -- ¬ Col A B Q
        have hNColDEF : ¬ Col D E F := ncol_conga_ncol_c A B Q D E F hS3B hCongABQDEF
        obtain ⟨P, hCongABCDEP_S, hOSDEPF⟩ := angle_construction_1_c A B C D E F hR1 hNColDEF
        have hPE_S : P ≠ E := hCongABCDEP_S.2.2.2.1
        obtain ⟨PP, hOutEPPP, hCongEPPBX⟩ := segment_construction_3_c E P B X (Ne.symm hPE_S) (Ne.symm hXB')
        have hNColBAC_S : ¬ Col B A C := fun h => hR1 (col_permutation_4_c B A C h)
        have hOSABCQ : OS A B C Q := in_angle_one_side_c A B Q C hS3B hNColBAC_S hInAngleCopy
        have hK1 : OS B A C Q := invert_one_side_c A B C Q hOSABCQ
        have hK2 : OS E D P F := invert_one_side_c D E P F hOSDEPF
        have hCongCBAPED : CongA C B A P E D := conga_comm_c A B C D E P hCongABCDEP_S
        have hL1 : CongA C B Q P E F := l11_22b_c C B Q A P E F D ⟨hK1, hK2, hCongCBAPED, hCongABQDEF⟩
        have hL3A : CongA D E F A B Q := conga_sym_c A B Q D E F hCongABQDEF
        have hL6 : Out B A A := out_trivial_c B A hAB
        have hL6b : Out B Q Q := out_trivial_c B Q hQB
        have hDDEFFCongAABQ : CongA DD E FF A B Q :=
          l11_10_c D E F A B Q DD FF A Q hL3A hL4 hL5 hL6 hL6b
        have hL2B : Cong DD E A B :=
          cong_symmetry_c A B DD E (cong_right_commutativity_c A B E DD (cong_left_commutativity_c B A E DD (cong_symmetry_c E DD B A hCongEDDBA)))
        have hL2 : Cong DD FF A Q := cong2_conga_cong_c DD E FF A B Q hDDEFFCongAABQ hL2B hCongEFFBQ
        have hL9 : CongA A B X DD E PP :=
          l11_10_c A B C D E P A X DD PP hCongABCDEP_S (out_trivial_c B A hAB) hG1 hL4 (l6_6_c E P PP hOutEPPP)
        have hL10 : Cong A B DD E := cong_4321_c E DD B A hCongEDDBA
        have hCongBXEPP : Cong B X E PP := cong_symmetry_c E PP B X hCongEPPBX
        have hL8 : Cong A X DD PP := cong2_conga_cong_c A B X DD E PP hL9 hL10 hCongBXEPP
        have hL12B : Cong A Q DD FF := cong_symmetry_c DD FF A Q hL2
        have hL13A : CongA X B Q PP E FF :=
          l11_10_c C B Q P E F X Q PP FF hL1 hG1 (out_trivial_c B Q hQB) (l6_6_c E P PP hOutEPPP) hL5
        have hL13B : Cong X B PP E := cong_4321_c E PP B X hCongEPPBX
        have hCongBQEFF : Cong B Q E FF := cong_symmetry_c E FF B Q hCongEFFBQ
        have hCongXQPPFF : Cong X Q PP FF := cong2_conga_cong_c X B Q PP E FF hL13A hL13B hCongBQEFF
        have hCong3AXQDDPPFF : Cong_3 A X Q DD PP FF := ⟨hL8, hL12B, hCongXQPPFF⟩
        have hZ4 : Bet DD PP FF := l4_6_c A X Q DD PP FF hBetAXQ hCong3AXQDDPPFF
        have hZ3 : PP ≠ E := (l6_3_1_c P PP E hOutEPPP).2.1
        have hPPInAngle : InAngle PP DD E FF := ⟨hG3, hG3B, hZ3, PP, hZ4, Or.inr (out_trivial_c E PP hZ3)⟩
        have hS5 : InAngle P D E F := l11_25_c PP DD E FF D F P hPPInAngle hOutEDDD hOutEFFF hOutEPPP
        exact ⟨P, hS5, hCongABCDEP_S⟩

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
  · have H10 := bet_conga_bet_c b0 b1 b3 b0 b1 PP b4 H3
    exact bet_in_angle_bet_c b0 b1 b2 PP H10 HH
theorem eq_conga_out_c :
    ∀ (A B D E F : Tpoint), CongA A B A D E F → Out E D F := by
  intro A B D E F hCongABADEF
  have hAB : A ≠ B := hCongABADEF.1
  exact l11_21_a_c A B A D E F (out_trivial_c B A hAB) hCongABADEF
theorem conga_ex_cong3_c :
    ∀ (A B C A' B' C' : Tpoint), CongA A B C A' B' C' → ∃ (AA : Tpoint), ∃ (CC : Tpoint), Out B A AA → Out B C CC → Cong_3 AA B CC A' B' C' := sorry
theorem conga_preserves_in_angle_c :
    ∀ (A B C I A' B' C' I' : Tpoint), CongA A B C A' B' C' → CongA A B I A' B' I' → InAngle I A B C → OS A' B' I' C' → InAngle I' A' B' C' := by
  intro A B C I A' B' C' I' hCongABC hCongABI hInAngle hOS
  have P1 : A ≠ B := hCongABC.1
  have P2 : C ≠ B := hCongABC.2.1
  have P3 : A' ≠ B' := hCongABC.2.2.1
  have P4 : C' ≠ B' := hCongABC.2.2.2.1
  have P6 : I' ≠ B' := hCongABI.2.2.2.1
  rcases or_bet_out_c A B C with hBet | hOutBAC | Z1
  · -- Bet A B C
    have hBet' : Bet A' B' C' := bet_conga_bet_c A B C A' B' C' hBet hCongABC
    exact in_angle_line_c A' B' C' I' P6 P3 P4 hBet'
  · -- Out B A C
    have hOutBAI : Out B A I := in_angle_out_c A B C I hOutBAC hInAngle
    have hOutB'A'I' : Out B' A' I' := l11_21_a_c A B I A' B' I' hOutBAI hCongABI
    exact out321_inangle_c A' B' C' I' P4 hOutB'A'I'
  · -- ¬ Col A B C
    rcases or_bet_out_c A B I with hBetABI | hOutBAI | hNColABI
    · exfalso
      have hBetABC : Bet A B C := bet_in_angle_bet_c A B C I hBetABI hInAngle
      exact Z1 (bet_col_c A B C hBetABC)
    · have hOutB'A'I' : Out B' A' I' := l11_21_a_c A B I A' B' I' hOutBAI hCongABI
      exact out321_inangle_c A' B' C' I' P4 hOutB'A'I'
    · obtain ⟨AA', hOutB'A'AA', hCongB'AA'BA⟩ := segment_construction_3_c B' A' B A (Ne.symm P3) (Ne.symm P1)
      obtain ⟨CC', hOutB'C'CC', hCongB'CC'BC⟩ := segment_construction_3_c B' C' B C (Ne.symm P4) (Ne.symm P2)
      obtain ⟨_, _, _, J, hBetAJC, hJcase⟩ := hInAngle
      have hOutBJI : Out B J I := by
        rcases hJcase with hJB | h
        · exfalso; apply Z1; rw [hJB] at hBetAJC; exact bet_col_c A B C hBetAJC
        · exact h
      have hBJ : B ≠ J := Ne.symm hOutBJI.1
      have hQ7 : ¬ Col A B J := by
        intro hColABJ
        apply hNColABI
        have hColBAI : Col B A I :=
          col_transitivity_1_c B J A I hBJ (col_permutation_1_c A B J hColABJ) (out_col_c B J I hOutBJI)
        exact col_permutation_4_c B A I hColBAI
      have hNColA'B'I' : ¬ Col A' B' I' := by
        obtain ⟨R, hTS1, _⟩ := hOS
        exact fun h => hTS1.1 (col_permutation_2_c A' B' I' h)
      obtain ⟨J', hCongABJ, hOSJ'I'⟩ := angle_construction_1_c A B J A' B' I' hQ7 hNColA'B'I'
      have hB'J' : B' ≠ J' := Ne.symm hCongABJ.2.2.2.1
      obtain ⟨JJ', hOutB'J'JJ', hCongB'JJ'BJ⟩ := segment_construction_3_c B' J' B J hB'J' hBJ
      have hNColA'B'J' : ¬ Col A' B' J' := by
        obtain ⟨R2, hTS1', _⟩ := hOSJ'I'
        exact fun h => hTS1'.1 (col_permutation_2_c A' B' J' h)
      have hA'JJ' : A' ≠ JJ' := by
        intro hEq
        apply hNColA'B'J'
        have hColB'J'JJ' : Col B' J' JJ' := out_col_c B' J' JJ' hOutB'J'JJ'
        rw [← hEq] at hColB'J'JJ'
        exact col_permutation_2_c B' J' A' hColB'J'JJ'
      have hQ13 : B' ≠ JJ' := Ne.symm hOutB'J'JJ'.2.1
      have hQ14 : ¬ Col A' B' JJ' := by
        intro hCol
        apply hNColA'B'J'
        have hColB'JJ'A' : Col B' JJ' A' := col_permutation_1_c A' B' JJ' hCol
        have hColB'JJ'J' : Col B' JJ' J' := col_permutation_5_c B' J' JJ' (out_col_c B' J' JJ' hOutB'J'JJ')
        have hColB'A'J' : Col B' A' J' := col_transitivity_1_c B' JJ' A' J' hQ13 hColB'JJ'A' hColB'JJ'J'
        exact col_permutation_4_c B' A' J' hColB'A'J'
      have hQ15 : CongA A B C AA' B' CC' :=
        l11_10_c A B C A' B' C' A C AA' CC' hCongABC (out_trivial_c B A P1) (out_trivial_c B C P2)
          (l6_6_c B' A' AA' hOutB'A'AA') (l6_6_c B' C' CC' hOutB'C'CC')
      rcases conga_cop_or_out_ts_c A' B' I' JJ'
          (by
            have hCopA'B'J'I' : Coplanar A' B' J' I' := os_coplanar_c A' B' J' I' hOSJ'I'
            have hCopA'B'I'J' : Coplanar A' B' I' J' := coplanar_perm_1_c A' B' J' I' hCopA'B'J'I'
            have hCopA'I'B'J' : Coplanar A' I' B' J' := coplanar_perm_2_c A' B' I' J' hCopA'B'I'J'
            have hCopA'I'B'JJ' : Coplanar A' I' B' JJ' :=
              col_cop_cop_c A' I' B' J' JJ' hCopA'I'B'J' hB'J' (out_col_c B' J' JJ' hOutB'J'JJ')
            exact coplanar_perm_2_c A' I' B' JJ' hCopA'I'B'JJ')
          (by
            have hQ16 : CongA A' B' J' A' B' JJ' :=
              out2_conga_c A' B' J' A' JJ' (out_trivial_c B' A' P3) (l6_6_c B' J' JJ' hOutB'J'JJ')
            have hCongABIA'B'JJ' : CongA A B I A' B' JJ' :=
              l11_10_c A B J A' B' J' A I A' JJ' hCongABJ (out_trivial_c B A P1) (l6_6_c B J I hOutBJI)
                (out_trivial_c B' A' P3) (l6_6_c B' J' JJ' hOutB'J'JJ')
            exact conga_trans_c A' B' I' A B I A' B' JJ' (conga_sym_c A B I A' B' I' hCongABI) hCongABIA'B'JJ')
        with hZ2 | hX1
      · -- Out B' I' JJ'
        have hR1 : OS B A J C :=
          invert_one_side_c A B J C
            (out_one_side_c A B J C (Or.inl hQ7)
              (bet_out_c A J C (Ne.symm (fun h => hQ7 (h ▸ col_trivial_3_c A B))) hBetAJC))
        have hOSb : OS B' A' I' C' := invert_one_side_c A' B' I' C' hOS
        have hOSc : OS B' A' C' I' := one_side_symmetry_c B' A' I' C' hOSb
        have hOSd : OS B' A' C' JJ' := out_out_one_side_c B' A' C' I' JJ' hOSc hZ2
        have hOSe : OS B' A' C' J' := out_out_one_side_c B' A' C' JJ' J' hOSd (l6_6_c B' J' JJ' hOutB'J'JJ')
        have hR2 : OS B' A' J' C' := one_side_symmetry_c B' A' C' J' hOSe
        have hAJ : A ≠ J := fun h => hQ7 (h ▸ col_trivial_3_c A B)
        have hCongJBA : CongA J B A J' B' A' := conga_comm_c A B J A' B' J' hCongABJ
        have hZ3 : CongA J B C J' B' C' := l11_22b_c J B C A J' B' C' A' ⟨hR1, hR2, hCongJBA, hCongABC⟩
        have hR8A : CongA A B J AA' B' JJ' :=
          l11_10_c A B I A' B' I' A J AA' JJ' hCongABI (out_trivial_c B A P1) hOutBJI
            (l6_6_c B' A' AA' hOutB'A'AA') (l6_6_c B' I' JJ' hZ2)
        have hR8B : Cong A B AA' B' :=
          cong_right_commutativity_c A B B' AA' (cong_left_commutativity_c B A B' AA' (cong_symmetry_c B' AA' B A hCongB'AA'BA))
        have hR8C : Cong B J B' JJ' := cong_symmetry_c B' JJ' B J hCongB'JJ'BJ
        have hR8 : Cong A J AA' JJ' := cong2_conga_cong_c A B J AA' B' JJ' hR8A hR8B hR8C
        have hCongBCB'CC' : Cong B C B' CC' := cong_symmetry_c B' CC' B C hCongB'CC'BC
        have hLR8A : Cong A C AA' CC' := cong2_conga_cong_c A B C AA' B' CC' hQ15 hR8B hCongBCB'CC'
        have hOutB'CC'C' : Out B' CC' C' := l6_6_c B' C' CC' hOutB'C'CC'
        have hCongJ'B'C'JJ'B'CC' : CongA J' B' C' JJ' B' CC' :=
          out2_conga_c J' B' C' JJ' CC' (l6_6_c B' J' JJ' hOutB'J'JJ') hOutB'CC'C'
        have hLR9A : CongA J B C JJ' B' CC' := conga_trans_c J B C J' B' C' JJ' B' CC' hZ3 hCongJ'B'C'JJ'B'CC'
        have hLR9B : Cong J B JJ' B' := cong_right_commutativity_c J B B' JJ' (cong_left_commutativity_c B J B' JJ' hR8C)
        have hCongJCJJ'CC' : Cong J C JJ' CC' := cong2_conga_cong_c J B C JJ' B' CC' hLR9A hLR9B hCongBCB'CC'
        have hR10 : Bet AA' JJ' CC' := l4_6_c A J C AA' JJ' CC' hBetAJC ⟨hR8, hLR8A, hCongJCJJ'CC'⟩
        have hAA'B' : AA' ≠ B' := hOutB'A'AA'.2.1
        have hCC'B' : CC' ≠ B' := hOutB'C'CC'.2.1
        have hJJ'InAngle : InAngle JJ' AA' B' CC' :=
          ⟨hAA'B', hCC'B', Ne.symm hQ13, JJ', hR10, Or.inr (out_trivial_c B' JJ' (Ne.symm hQ13))⟩
        exact l11_25_c JJ' AA' B' CC' A' C' I' hJJ'InAngle hOutB'A'AA' hOutB'C'CC' hZ2
      · -- TS A' B' I' JJ'
        have hStepX1 : OS A' B' I' J' := one_side_symmetry_c A' B' J' I' hOSJ'I'
        have hStepX2 : OS B' A' I' J' := invert_one_side_c A' B' I' J' hStepX1
        have hStepX3 : OS B' A' I' JJ' := out_out_one_side_c B' A' I' J' JJ' hStepX2 hOutB'J'JJ'
        have hX2 : OS A' B' I' JJ' := invert_one_side_c B' A' I' JJ' hStepX3
        exact absurd hX2 (l9_9_c A' B' I' JJ' hX1)

theorem l11_30_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), LeA A B C D E F → CongA A B C A' B' C' → CongA D E F D' E' F' → LeA A' B' C' D' E' F' := by
  intro A B C D E F A' B' C' D' E' F' hLeA hCongABCA'B'C' hCongDEFD'E'F'
  obtain ⟨Q, hInAngleC, hCongABQDEF⟩ := l11_29_a_c A B C D E F hLeA
  have hInAngleCopy := hInAngleC
  have hAB : A ≠ B := hInAngleC.1
  have hQB : Q ≠ B := hInAngleC.2.1
  have hCB : C ≠ B := hInAngleC.2.2.1
  have hAB' : A' ≠ B' := hCongABCA'B'C'.2.2.1
  have hCB' : C' ≠ B' := hCongABCA'B'C'.2.2.2.1
  have hDE : D ≠ E := hCongABQDEF.2.2.1
  have hFE : F ≠ E := hCongABQDEF.2.2.2.1
  have hDE' : D' ≠ E' := hCongDEFD'E'F'.2.2.1
  have hFE' : F' ≠ E' := hCongDEFD'E'F'.2.2.2.1
  apply l11_29_b_c
  rcases or_bet_out_c A' B' C' with hBetA'B'C' | hOutB'A'C' | hNColA'B'C'
  · -- Bet A' B' C'
    obtain ⟨Q', hBetA'B'Q', hCongB'Q'A'B'⟩ := segment_construction A' B' A' B'
    have hB'Q' : B' ≠ Q' := by
      intro hEq
      subst hEq
      exact hAB' (cong_reverse_identity_c B' A' B' hCongB'Q'A'B')
    have hA'Q' : A' ≠ Q' := by
      intro hEq
      subst hEq
      exact hAB' (between_identity A' B' hBetA'B'Q')
    have hInAngleC'A'B'Q' : InAngle C' A' B' Q' :=
      in_angle_line_c A' B' Q' C' hCB' hAB' (Ne.symm hB'Q') hBetA'B'Q'
    have hBetABC : Bet A B C := bet_conga_bet_c A' B' C' A B C hBetA'B'C' (conga_sym_c A B C A' B' C' hCongABCA'B'C')
    have hLeAABCABQ : LeA A B C A B Q := l11_29_b_c A B C A B Q ⟨Q, hInAngleC, conga_refl_c A B Q hAB hQB⟩
    have hBetABQ : Bet A B Q := lea_line_c A B Q C hBetABC hLeAABCABQ
    have hBetDEF : Bet D E F := bet_conga_bet_c A B Q D E F hBetABQ hCongABQDEF
    have hBetD'E'F' : Bet D' E' F' := bet_conga_bet_c D E F D' E' F' hBetDEF hCongDEFD'E'F'
    have hCongA'B'Q'D'E'F' : CongA A' B' Q' D' E' F' :=
      conga_line_c A' B' Q' D' E' F' hAB' hB'Q' hDE' (Ne.symm hFE') hBetA'B'Q' hBetD'E'F'
    exact ⟨Q', hInAngleC'A'B'Q', hCongA'B'Q'D'E'F'⟩
  · -- Out B' A' C'
    obtain ⟨Q', hCongD'E'F'A'B'Q'⟩ := angle_construction_3_c D' E' F' A' B' hDE' hFE' hAB'
    have hQ'B' : Q' ≠ B' := hCongD'E'F'A'B'Q'.2.2.2.1
    have hInAngle : InAngle C' A' B' Q' :=
      col_in_angle_c A' B' Q' C' hAB' hQ'B' hCB' (Or.inl hOutB'A'C')
    exact ⟨Q', hInAngle, conga_sym_c D' E' F' A' B' Q' hCongD'E'F'A'B'Q'⟩
  · -- ¬ Col A' B' C'
    rcases or_bet_out_c D' E' F' with hBetD'E'F' | hOutE'D'F' | hNColD'E'F'
    · -- Bet D' E' F'
      obtain ⟨Q', hCongD'E'F'A'B'Q'⟩ := angle_construction_3_c D' E' F' A' B' hDE' hFE' hAB'
      have hQ'B' : Q' ≠ B' := hCongD'E'F'A'B'Q'.2.2.2.1
      have hBetA'B'Q' : Bet A' B' Q' := bet_conga_bet_c D' E' F' A' B' Q' hBetD'E'F' hCongD'E'F'A'B'Q'
      have hInAngle : InAngle C' A' B' Q' :=
        in_angle_line_c A' B' Q' C' hCB' hAB' hQ'B' hBetA'B'Q'
      exact ⟨Q', hInAngle, conga_sym_c D' E' F' A' B' Q' hCongD'E'F'A'B'Q'⟩
    · -- Out E' D' F'
      obtain ⟨Q', hCongD'E'F'A'B'Q'⟩ := angle_construction_3_c D' E' F' A' B' hDE' hFE' hAB'
      have hOutB'A'Q' : Out B' A' Q' := l11_21_a_c D' E' F' A' B' Q' hOutE'D'F' hCongD'E'F'A'B'Q'
      have hCongABQD'E'F' : CongA A B Q D' E' F' := conga_trans_c A B Q D E F D' E' F' hCongABQDEF hCongDEFD'E'F'
      have hOutBAQ : Out B A Q := l11_21_a_c D' E' F' A B Q hOutE'D'F' (conga_sym_c A B Q D' E' F' hCongABQD'E'F')
      have hOutBAC : Out B A C := in_angle_out_c A B Q C hOutBAQ hInAngleCopy
      have hOutB'A'C' : Out B' A' C' := l11_21_a_c A B C A' B' C' hOutBAC hCongABCA'B'C'
      have hInAngle : InAngle C' A' B' Q' :=
        out321_inangle_c A' B' Q' C' hOutB'A'Q'.2.1 hOutB'A'C'
      exact ⟨Q', hInAngle, conga_sym_c D' E' F' A' B' Q' hCongD'E'F'A'B'Q'⟩
    · -- ¬ Col D' E' F'
      obtain ⟨Q', hCongD'E'F'A'B'Q', hOSA'B'Q'C'⟩ := angle_construction_1_c D' E' F' A' B' C' hNColD'E'F' hNColA'B'C'
      have hCongABQA'B'Q' : CongA A B Q A' B' Q' :=
        conga_trans_c A B Q D E F A' B' Q' hCongABQDEF (conga_trans_c D E F D' E' F' A' B' Q' hCongDEFD'E'F' hCongD'E'F'A'B'Q')
      have hInAngle : InAngle C' A' B' Q' :=
        conga_preserves_in_angle_c A B Q C A' B' Q' C' hCongABQA'B'Q' hCongABCA'B'C' hInAngleCopy
          (one_side_symmetry_c A' B' Q' C' hOSA'B'Q'C')
      exact ⟨Q', hInAngle, conga_sym_c D' E' F' A' B' Q' hCongD'E'F'A'B'Q'⟩

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
theorem conga_lea_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA A B C D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  ⟨b5, (⟨(inangle3123_c b3 b4 b5 (conga_diff45_c b0 b1 b2 b3 b4 b5 b6) (conga_diff56_c b0 b1 b2 b3 b4 b5 b6)), b6⟩)⟩
theorem conga_lea456123_c :
    ∀ (A B C D E F : Tpoint), CongA A B C D E F → LeA D E F A B C :=
  fun b0 b1 b2 b3 b4 b5 b6 =>
  conga_lea_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b6)
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
theorem lea_out4_lea_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), LeA A B C D E F → Out B A A' → Out B C C' → Out E D D' → Out E F F' → LeA A' B C' D' E F' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 =>
  l11_30_c b0 b1 b2 b3 b4 b5 b6 b1 b7 b8 b4 b9 b10 (out2_conga_c b0 b1 b2 b6 b7 (l6_6 b11) (l6_6 b12)) (out2_conga_c b3 b4 b5 b8 b9 (l6_6 b13) (l6_6 b14))
theorem lea121345_c :
    ∀ (A B C D E : Tpoint), A ≠ B → C ≠ D → D ≠ E → LeA A B A C D E := sorry
theorem inangle_lea_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA A B P A B C := by
  intro b0 b1 b2 b3 b4
  exact ⟨b3, (⟨b4, ((by
  obtain ⟨H, H0⟩ := b4
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, _⟩ := H1
  exact conga_refl_c b0 b1 b3 H H2))⟩)⟩
theorem inangle_lea_1_c :
    ∀ (A B C P : Tpoint), InAngle P A B C → LeA P B C A B C :=
  fun b0 b1 b2 b3 b4 =>
  lea_comm_c b2 b1 b3 b2 b1 b0 (inangle_lea_c b2 b1 b0 b3 (l11_24_c b3 b0 b1 b2 b4))
theorem inangle_lta_c :
    ∀ (A B C P : Tpoint), ¬ Col P B C → InAngle P A B C → LtA A B P A B C := sorry

theorem in_angle_trans_c :
    ∀ (A B C D E : Tpoint), InAngle C A B D → InAngle D A B E → InAngle C A B E := by
  intro A B C D E hInAngleCABD hInAngleDABE
  have hAB : A ≠ B := hInAngleCABD.1
  have hCB : C ≠ B := hInAngleCABD.2.2.1
  have hEB : E ≠ B := hInAngleDABE.2.1
  have hInAngleCABDCopy := hInAngleCABD
  have hInAngleDABECopy := hInAngleDABE
  obtain ⟨_, _, _, CC, hBetACCD, hCCcase⟩ := hInAngleCABD
  obtain ⟨_, _, _, DD, hBetADDE, hDDcase⟩ := hInAngleDABE
  rcases hCCcase with hCCB | hOutBCCC
  · have hBetABD : Bet A B D := hCCB ▸ hBetACCD
    rcases hDDcase with hDDB | hOutBDDD
    · have hBetABE : Bet A B E := hDDB ▸ hBetADDE
      exact in_angle_line_c A B E C hCB hAB hEB hBetABE
    · have hBetABE : Bet A B E := bet_in_angle_bet_c A B E D hBetABD hInAngleDABECopy
      exact in_angle_line_c A B E C hCB hAB hEB hBetABE
  · rcases hDDcase with hDDB | hOutBDDD
    · have hBetABE : Bet A B E := hDDB ▸ hBetADDE
      exact in_angle_line_c A B E C hCB hAB hEB hBetABE
    · have hInAngleCABDD : InAngle C A B DD :=
        l11_25_c C A B D A DD C hInAngleCABDCopy (out_trivial_c B A hAB) hOutBDDD (out_trivial_c B C hCB)
      obtain ⟨_, _, _, CC', hBetACC'DD, hCC'case⟩ := hInAngleCABDD
      rcases hCC'case with hCC'B | hOutBCC'C
      · have hBetABDD : Bet A B DD := hCC'B ▸ hBetACC'DD
        have hBetABE : Bet A B E := between_exchange4_c A B DD E hBetABDD hBetADDE
        exact in_angle_line_c A B E C hCB hAB hEB hBetABE
      · have hBetACC'E : Bet A CC' E := between_exchange4_c A CC' DD E hBetACC'DD hBetADDE
        exact ⟨hAB, hEB, hCB, CC', hBetACC'E, Or.inr hOutBCC'C⟩
theorem lea_trans_c :
    ∀ (A B C A1 B1 C1 A2 B2 C2 : Tpoint), LeA A B C A1 B1 C1 → LeA A1 B1 C1 A2 B2 C2 → LeA A B C A2 B2 C2 := by
  intro A B C A1 B1 C1 A2 B2 C2 hLeA1 hLeA2
  obtain ⟨P1, hInAngleP1A1B1C1, hCongABCA1B1P1⟩ := hLeA1
  obtain ⟨P2, hInAngleP2A2B2C2, hCongA1B1C1A2B2P2⟩ := hLeA2
  have hAB : A ≠ B := hCongABCA1B1P1.1
  have hCB : C ≠ B := hCongABCA1B1P1.2.1
  have hA1B1 : A1 ≠ B1 := hInAngleP1A1B1C1.1
  have hC1B1 : C1 ≠ B1 := hInAngleP1A1B1C1.2.1
  have hA2B2 : A2 ≠ B2 := hInAngleP2A2B2C2.1
  have hC2B2 : C2 ≠ B2 := hInAngleP2A2B2C2.2.1
  rcases or_bet_out_c A B C with hBetABC | hOutBAC | H1
  · have hBetA1B1P1 : Bet A1 B1 P1 := bet_conga_bet_c A B C A1 B1 P1 hBetABC hCongABCA1B1P1
    have hBetA1B1C1 : Bet A1 B1 C1 := bet_in_angle_bet_c A1 B1 C1 P1 hBetA1B1P1 hInAngleP1A1B1C1
    have hBetA2B2P2 : Bet A2 B2 P2 := bet_conga_bet_c A1 B1 C1 A2 B2 P2 hBetA1B1C1 hCongA1B1C1A2B2P2
    have hBetA2B2C2 : Bet A2 B2 C2 := bet_in_angle_bet_c A2 B2 C2 P2 hBetA2B2P2 hInAngleP2A2B2C2
    exact l11_31_2_c A B C A2 B2 C2 hAB hCB hA2B2 hC2B2 hBetA2B2C2
  · exact l11_31_1_c A B C A2 B2 C2 hOutBAC hA2B2 hC2B2
  · rcases or_bet_out_c A2 B2 C2 with hBetA2B2C2 | hOutB2A2C2 | T12
    · exact l11_31_2_c A B C A2 B2 C2 hAB hCB hA2B2 hC2B2 hBetA2B2C2
    · have hOutB2A2P2 : Out B2 A2 P2 := in_angle_out_c A2 B2 C2 P2 hOutB2A2C2 hInAngleP2A2B2C2
      have hOutB1A1C1 : Out B1 A1 C1 :=
        l11_21_a_c A2 B2 P2 A1 B1 C1 hOutB2A2P2 (conga_sym_c A1 B1 C1 A2 B2 P2 hCongA1B1C1A2B2P2)
      have hOutB1A1P1 : Out B1 A1 P1 := in_angle_out_c A1 B1 C1 P1 hOutB1A1C1 hInAngleP1A1B1C1
      have hOutBAC2 : Out B A C :=
        l11_21_a_c A1 B1 P1 A B C hOutB1A1P1 (conga_sym_c A B C A1 B1 P1 hCongABCA1B1P1)
      exact l11_31_1_c A B C A2 B2 C2 hOutBAC2 hA2B2 hC2B2
    · obtain ⟨P, hCongABCA2B2P, hOSA2B2PC2⟩ := angle_construction_1_c A B C A2 B2 C2 H1 T12
      have hNColB2A2P2 : ¬ Col B2 A2 P2 := by
        have hP2A2 : P2 ≠ A2 := by
          intro hEq
          have hCongA2B2A2A1B1C1 : CongA A2 B2 A2 A1 B1 C1 :=
            conga_sym_c A1 B1 C1 A2 B2 A2 (hEq ▸ hCongA1B1C1A2B2P2)
          have hOutB1A1C1 : Out B1 A1 C1 := eq_conga_out_c A2 B2 A1 B1 C1 hCongA2B2A2A1B1C1
          have hOutB1A1P1 : Out B1 A1 P1 := in_angle_out_c A1 B1 C1 P1 hOutB1A1C1 hInAngleP1A1B1C1
          have hOutBAC2 : Out B A C :=
            l11_21_a_c A1 B1 P1 A B C hOutB1A1P1 (conga_sym_c A B C A1 B1 P1 hCongABCA1B1P1)
          exact H1 (col_permutation_4_c B A C (out_col_c B A C hOutBAC2))
        rcases or_bet_out_c A2 B2 P2 with hBetA2B2P2 | hOutB2A2P2 | hNColA2B2P2
        · exact absurd (bet_col_c A2 B2 C2 (bet_in_angle_bet_c A2 B2 C2 P2 hBetA2B2P2 hInAngleP2A2B2C2)) T12
        · exfalso
          have hOutB1A1C1 : Out B1 A1 C1 :=
            l11_21_a_c A2 B2 P2 A1 B1 C1 hOutB2A2P2 (conga_sym_c A1 B1 C1 A2 B2 P2 hCongA1B1C1A2B2P2)
          have hOutB1A1P1 : Out B1 A1 P1 := in_angle_out_c A1 B1 C1 P1 hOutB1A1C1 hInAngleP1A1B1C1
          have hOutBAC2 : Out B A C :=
            l11_21_a_c A1 B1 P1 A B C hOutB1A1P1 (conga_sym_c A B C A1 B1 P1 hCongABCA1B1P1)
          exact H1 (col_permutation_4_c B A C (out_col_c B A C hOutBAC2))
        · exact fun h => hNColA2B2P2 (col_permutation_4_c B2 A2 P2 h)
      have hT14 : OS A2 B2 P2 C2 := in_angle_one_side_c A2 B2 C2 P2 T12 hNColB2A2P2 hInAngleP2A2B2C2
      have hS1 : OS A2 B2 P P2 :=
        one_side_transitivity_c A2 B2 P C2 P2 hOSA2B2PC2 (one_side_symmetry_c A2 B2 P2 C2 hT14)
      have hCongA1B1P1A2B2P : CongA A1 B1 P1 A2 B2 P :=
        conga_trans_c A1 B1 P1 A B C A2 B2 P (conga_sym_c A B C A1 B1 P1 hCongABCA1B1P1) hCongABCA2B2P
      have hInAnglePA2B2P2 : InAngle P A2 B2 P2 :=
        conga_preserves_in_angle_c A1 B1 C1 P1 A2 B2 P2 P hCongA1B1C1A2B2P2 hCongA1B1P1A2B2P hInAngleP1A1B1C1 hS1
      have hInAnglePA2B2C2 : InAngle P A2 B2 C2 :=
        in_angle_trans_c A2 B2 P P2 C2 hInAnglePA2B2P2 hInAngleP2A2B2C2
      exact ⟨P, hInAnglePA2B2C2, hCongABCA2B2P⟩

theorem in_angle_asym_c :
    ∀ (A B C D : Tpoint), InAngle D A B C → InAngle C A B D → CongA A B C A B D := by
  intro A B C D h1 h2
  obtain ⟨hAB, hCB, hDB, CC, hACC, hCCcase⟩ := h1
  obtain ⟨_, _, _, DD, hADD, hDDcase⟩ := h2
  rcases hCCcase with hCCeqB | hOutCC
  · rcases hDDcase with hDDeqB | hOutDD
    · -- Case 1: CC = B, DD = B (fully degenerate: A,B,C and A,B,D both lines)
      rw [hCCeqB] at hACC
      rw [hDDeqB] at hADD
      exact conga_line_c A B C A B D hAB hCB.symm hAB hDB.symm hACC hADD
    · -- Case 2: CC = B (so Bet A B C is free), DD via Out B DD C
      rw [hCCeqB] at hACC
      obtain ⟨_, _, hSub⟩ := hOutDD
      rcases hSub with hSub | hSub
      · have hABDD := between_inner_transitivity_c A B DD C hACC hSub
        have hABD := between_exchange4_c A B DD D hABDD hADD
        exact conga_line_c A B C A B D hAB hCB.symm hAB hDB.symm hACC hABD
      · have hABDD := outer_transitivity_between_c A B C DD hACC hSub hCB.symm
        have hABD := between_exchange4_c A B DD D hABDD hADD
        exact conga_line_c A B C A B D hAB hCB.symm hAB hDB.symm hACC hABD
  · rcases hDDcase with hDDeqB | hOutDD
    · -- Case 3: Out B CC D, DD = B (so Bet A B D is free)
      rw [hDDeqB] at hADD
      obtain ⟨_, _, hSub⟩ := hOutCC
      rcases hSub with hSub | hSub
      · have hABCC := between_inner_transitivity_c A B CC D hADD hSub
        have hABC := between_exchange4_c A B CC C hABCC hACC
        exact conga_line_c A B C A B D hAB hCB.symm hAB hDB.symm hABC hADD
      · have hABCC := outer_transitivity_between_c A B D CC hADD hSub hDB.symm
        have hABC := between_exchange4_c A B CC C hABCC hACC
        exact conga_line_c A B C A B D hAB hCB.symm hAB hDB.symm hABC hADD
    · -- Case 4: Out B CC D and Out B DD C, genuinely (neither degenerate).
      -- Pasch on triangle C-D-A (CC on side CA, DD on side DA) gives X with
      -- Bet CC X D and Bet DD X C; chaining through out_bet_out_2 shows
      -- X witnesses Out B C D directly, closing the angle congruence via out2_conga.
      obtain ⟨X, hCCXD, hDDXC⟩ :=
        inner_pasch C D A CC DD (between_symmetry hACC) (between_symmetry hADD)
      have hOutBXC : Out B X C := out_bet_out_2_c DD X C B hOutDD hDDXC
      have hOutBXD : Out B X D := out_bet_out_2_c CC X D B hOutCC hCCXD
      have hOutBCD : Out B C D := l6_7_c B C X D (l6_6 hOutBXC) hOutBXD
      exact out2_conga_c A B C A D (out_trivial hAB) (l6_6 hOutBCD)
theorem lea_asym_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → LeA D E F A B C → CongA A B C D E F := by
  intro A B C D E F H H0
  rcases col_dec_c A B C with hCol | hNCol
  · -- Branch 1: Col A B C
    rcases bet_dec_c A B C with hBet | hNBet
    · -- Bet A B C
      obtain ⟨hAB, hCB, hDE, hFE⟩ := lea_distincts_c A B C D E F H
      obtain ⟨P, hInPDEF, hCongABCDEP⟩ := H
      have hBetDEP : Bet D E P := bet_conga_bet_c A B C D E P hBet hCongABCDEP
      have hBetDEF : Bet D E F := bet_in_angle_bet_c D E F P hBetDEP hInPDEF
      exact conga_line_c A B C D E F hAB hCB.symm hDE hFE.symm hBet hBetDEF
    · -- ¬ Bet A B C
      have hOutBAC : Out B A C := not_bet_out_c A B C hCol hNBet
      obtain ⟨P, hInPABC, hCongDEFABP⟩ := H0
      have hOutBAP : Out B A P := in_angle_out_c A B C P hOutBAC hInPABC
      have hOutEDF : Out E D F :=
        l11_21_a_c A B P D E F hOutBAP (conga_sym_c D E F A B P hCongDEFABP)
      exact l11_21_b_c A B C D E F hOutBAC hOutEDF
  · -- Branch 2: ¬ Col A B C  (the payoff branch, unlocked by l11_29_a_c)
    obtain ⟨Q, hInCABQ, hCongABQDEF⟩ := l11_29_a_c A B C D E F H
    obtain ⟨P, hInPABC, hCongDEFABP⟩ := H0
    have hAB : A ≠ B := hCongABQDEF.1
    have hDE : D ≠ E := hCongABQDEF.2.2.1
    have hFE : F ≠ E := hCongABQDEF.2.2.2.1
    have hCB : C ≠ B := hInPABC.2.1
    have hCongABQABP : CongA A B Q A B P :=
      conga_trans_c A B Q D E F A B P hCongABQDEF hCongDEFABP
    rcases or_bet_out_c A B Q with hBetABQ | hOutBAQ | hNColABQ
    · -- Bet A B Q
      have hBetABP : Bet A B P := bet_conga_bet_c A B Q A B P hBetABQ hCongABQABP
      have hBetABC : Bet A B C := bet_in_angle_bet_c A B C P hBetABP hInPABC
      have hBetDEF : Bet D E F := bet_conga_bet_c A B Q D E F hBetABQ hCongABQDEF
      exact conga_line_c A B C D E F hAB hCB.symm hDE hFE.symm hBetABC hBetDEF
    · -- Out B A Q
      have hOutEDF : Out E D F := l11_21_a_c A B Q D E F hOutBAQ hCongABQDEF
      have hOutBAP : Out B A P := l11_21_a_c D E F A B P hOutEDF hCongDEFABP
      have hOutBAC : Out B A C := in_angle_out_c A B Q C hOutBAQ hInCABQ
      exact l11_21_b_c A B C D E F hOutBAC hOutEDF
    · -- ¬ Col A B Q
      rcases or_bet_out_c A B P with hBetABP | hOutBAP | hNColABP
      · -- Bet A B P
        have hBetABC : Bet A B C := bet_in_angle_bet_c A B C P hBetABP hInPABC
        have hBetDEF : Bet D E F :=
          bet_conga_bet_c A B P D E F hBetABP (conga_sym_c D E F A B P hCongDEFABP)
        exact conga_line_c A B C D E F hAB hCB.symm hDE hFE.symm hBetABC hBetDEF
      · -- Out B A P
        have hOutBAQ : Out B A Q :=
          l11_21_a_c A B P A B Q hOutBAP (conga_sym_c A B Q A B P hCongABQABP)
        have hOutBAC : Out B A C := in_angle_out_c A B Q C hOutBAQ hInCABQ
        have hOutEDF : Out E D F :=
          l11_21_a_c A B P D E F hOutBAP (conga_sym_c D E F A B P hCongDEFABP)
        exact l11_21_b_c A B C D E F hOutBAC hOutEDF
      · -- ¬ Col A B P: the deepest case
        have hNColCAB : ¬ Col C A B := not_col_permutation_2_c A B C hNCol
        have hCopCABP : Coplanar C A B P :=
          coplanar_perm_21_c P A B C (inangle_coplanar_c P A B C hInPABC)
        have hCopCABQ : Coplanar C A B Q := inangle_coplanar_c C A B Q hInCABQ
        have hCopABPQ : Coplanar A B P Q :=
          coplanar_trans_1_c C A B P Q hNColCAB hCopCABP hCopCABQ
        rcases conga_cop_or_out_ts_c A B P Q hCopABPQ
            (conga_sym_c A B Q A B P hCongABQABP) with hOutBPQ | hTSABPQ
        · -- Out B P Q
          have hInCABP : InAngle C A B P :=
            l11_25_c C A B Q A P C hInCABQ (out_trivial hAB) hOutBPQ (out_trivial hCB)
          have hCongABCABP : CongA A B C A B P := in_angle_asym_c A B C P hInPABC hInCABP
          have hCongABPDEF : CongA A B P D E F :=
            conga_trans_c A B P A B Q D E F
              (conga_sym_c A B Q A B P hCongABQABP) hCongABQDEF
          exact conga_trans_c A B C A B P D E F hCongABCABP hCongABPDEF
        · -- TS A B P Q: contradiction with ¬Col A B C via one-sidedness
          have hOSABPC : OS A B P C :=
            in_angle_one_side_c A B C P hNCol (not_col_permutation_4_c A B P hNColABP) hInPABC
          have hOSABCQ : OS A B C Q :=
            in_angle_one_side_c A B Q C hNColABQ (not_col_permutation_4_c A B C hNCol) hInCABQ
          have hOSABPQ : OS A B P Q := one_side_transitivity_c A B P C Q hOSABPC hOSABCQ
          exact absurd hOSABPQ (l9_9_c A B P Q hTSABPQ)
theorem col_lta_bet_c :
    ∀ (A B C X Y Z : Tpoint), Col X Y Z → LtA A B C X Y Z → Bet X Y Z := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨x, x0⟩ := b7
  have Hd := x
  exact not_out_bet_c b3 b4 b5 b6 ((fun H3 => x0 (lea_asym_c b0 b1 b2 b3 b4 b5 Hd ((let H4 := lea_distincts_c b0 b1 b2 b3 b4 b5 x; (by
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, _⟩ := H8
  exact l11_31_1_c b3 b4 b5 b0 b1 b2 H3 H5 H7))))))
theorem col_lta_out_c :
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
  have H7 := col_lta_bet_c b0 b1 b2 b3 b4 b3 (col_trivial_3_c b3 b4) b6
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
    ∀ (A B C P P' : Tpoint), B ≠ P' → TS B P A C → Bet P B P' → InAngle P A B C ∨ InAngle P' A B C := by
  intro A B C P P' hBP' hTS hBetPBP'
  obtain ⟨T, hColTBP, hBetATC⟩ := hTS.2.2
  have hAB : A ≠ B := by
    intro hEq
    apply hTS.1
    rw [hEq]
    exact col_trivial_1_c B P
  have hCB : C ≠ B := by
    intro hEq
    apply hTS.2.1
    rw [hEq]
    exact col_trivial_1_c B P
  have hPB : P ≠ B := by
    intro hEq
    apply hTS.1
    rw [hEq]
    exact col_trivial_2_c A B
  rcases point_equality_decidability B T with hBT | hBTne
  · left
    have hBetABC : Bet A B C := hBT ▸ hBetATC
    exact ⟨hAB, hCB, hPB, B, hBetABC, Or.inl rfl⟩
  · rcases or_bet_out_c P B T with hBetPBT | hOutBPT | hNColPBT
    · right
      exact ⟨hAB, hCB, Ne.symm hBP', T, hBetATC,
        Or.inr ⟨Ne.symm hBTne, Ne.symm hBP', l5_2_c P B T P' hPB hBetPBT hBetPBP'⟩⟩
    · left
      exact ⟨hAB, hCB, hPB, T, hBetATC, Or.inr (l6_6_c B P T hOutBPT)⟩
    · exact absurd (col_permutation_3_c T B P hColTBP) hNColPBT
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
  have H2 := bet_neq12_neq x1 H1
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
  have H11 := bet_neq21_neq H3 H10
  have H12 := bet_neq21_neq b5 H8
  have H13 := cong_diff_4_c b0 E b2 b0 H10 H4
  exact H13))))
  have H6 := conga_left_comm_c b2 b0 b1 b2 b0 b1 (conga_refl_c b2 b0 b1 ((let H6 := not_col_distincts_c b0 b1 b2 b4; (let H7 := H6; (by
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  have H12 := bet_neq21_neq H3 H11
  have H13 := bet_neq21_neq b5 H9
  have H14 := cong_diff_4_c b0 E b2 b0 H11 H4
  exact Ne.symm H11)))) ((let H6 := not_col_distincts_c b0 b1 b2 b4; (let H7 := H6; (by
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  have H12 := bet_neq21_neq H3 H11
  have H13 := bet_neq21_neq b5 H9
  have H14 := cong_diff_4_c b0 E b2 b0 H11 H4
  exact Ne.symm H9)))))
  have H7 := l11_13_c b1 b0 b2 b2 b0 b1 b3 E ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21_neq H3 H12
  have H14 := bet_neq21_neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact H6)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21_neq H3 H12
  have H14 := bet_neq21_neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact b5)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21_neq H3 H12
  have H14 := bet_neq21_neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact Ne.symm b6)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21_neq H3 H12
  have H14 := bet_neq21_neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact H3)))) ((let H7 := not_col_distincts_c b0 b1 b2 b4; (let H8 := H7; (by
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := bet_neq21_neq H3 H12
  have H14 := bet_neq21_neq b5 H10
  have H15 := cong_diff_4_c b0 E b2 b0 H12 H4
  exact Ne.symm H15))))
  obtain ⟨H8, H9⟩ := H5
  exact ⟨(l11_30_c b0 b1 b2 b1 b0 E b0 b1 b2 b2 b0 b3 H8 (conga_refl_c b0 b1 b2 ((let H10 := not_col_distincts_c b0 b1 b2 b4; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨_, H15⟩ := H14
  have H16 := bet_neq21_neq H3 H15
  have H17 := bet_neq21_neq b5 H13
  have H18 := cong_diff_4_c b0 E b2 b0 H15 H4
  exact H13)))) ((let H10 := not_col_distincts_c b0 b1 b2 b4; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨H15, H16⟩ := H14
  have H17 := bet_neq21_neq H3 H16
  have H18 := bet_neq21_neq b5 H13
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
  intro b0 b1 b2 b3 b4 b5 H
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
    ∀ (A B C A1 B1 C1 A2 B2 C2 : Tpoint), LtA A B C A1 B1 C1 → LtA A1 B1 C1 A2 B2 C2 → LtA A B C A2 B2 C2 := by
  intro A B C A1 B1 C1 A2 B2 C2 hLtA1 hLtA2
  refine ⟨lea_trans_c A B C A1 B1 C1 A2 B2 C2 hLtA1.1 hLtA2.1, ?_⟩
  intro hCongABCA2B2C2
  have hA1B1 : A1 ≠ B1 := (lta_distincts_c A B C A1 B1 C1 hLtA1).2.2.1
  have hC1B1 : C1 ≠ B1 := (lta_distincts_c A B C A1 B1 C1 hLtA1).2.2.2.1
  have hLeAA2B2C2A1B1C1 : LeA A2 B2 C2 A1 B1 C1 :=
    l11_30_c A B C A1 B1 C1 A2 B2 C2 A1 B1 C1 hLtA1.1 hCongABCA2B2C2 (conga_refl_c A1 B1 C1 hA1B1 hC1B1)
  exact hLtA2.2 (lea_asym_c A1 B1 C1 A2 B2 C2 hLtA2.1 hLeAA2B2C2A1B1C1)
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
theorem acute_col_out_c :
    ∀ (A B C : Tpoint), Col A B C → Acute A B C → Out B A C := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact col_lta_out_c b0 b1 b2 x x1 x3 b3 x6
theorem col_obtuse_bet_c :
    ∀ (A B C : Tpoint), Col A B C → Obtuse A B C → Bet A B C := by
  intro b0 b1 b2 b3 b4
  obtain ⟨x, x0⟩ := b4
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact col_lta_bet_c x x1 x3 b0 b1 b2 b3 x6
theorem out_acute_c :
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
theorem bet_obtuse_c :
    ∀ (A B C : Tpoint), Bet A B C → A ≠ B → B ≠ C → Obtuse A B C := by
  intro b0 b1 b2 b3 b4 b5
  have HD := perp_exists_c b1 b0 b1
  have e := HD b4
  obtain ⟨x, x0⟩ := e
  have H0 := bet_neq12_neq b3 b4
  have H1 := perp_distinct_c b1 x b0 b1 x0
  have H2 := H1
  obtain ⟨H3, _⟩ := H2
  exact ⟨b0, (⟨b1, (⟨x, (⟨(perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))), (⟨(l11_31_2_c b0 b1 x b0 b1 b2 b4 (Ne.symm H3) b4 (Ne.symm b5) b3), ((fun H4 => (let HNCol := per_not_col_c b0 b1 x b4 H3 (perp_in_per_c b0 b1 x (perp_in_sym_c b1 x b0 b1 b1 (perp_perp_in_c b1 x b0 x0))); HNCol (bet_col_c b0 b1 x (bet_conga_bet_c b0 b1 b2 b0 b1 x b3 (conga_sym_c b0 b1 x b0 b1 b2 H4))))))⟩)⟩)⟩)⟩)⟩
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
    ∀ (A B C : Tpoint), ¬ Col A B C → Lt B A B C → LtA B C A B A C := by
  intro A B C hNCol hLt
  obtain ⟨_, hAB, hBC, hAC⟩ := not_col_distincts_c A B C hNCol
  obtain ⟨⟨C', hBetBC'C, hCongBABC'⟩, hNCong⟩ := hLt
  have hColBC'C : Col B C' C := bet_col_c B C' C hBetBC'C
  have hCneC' : C ≠ C' := by
    intro heq
    apply hNCong
    rw [heq]
    exact hCongBABC'
  have hC'neA : C' ≠ A := by
    intro heq
    rw [heq] at hColBC'C
    apply hNCol
    colr
  have hC'neB : C' ≠ B := by
    intro heq
    apply hAB
    rw [heq] at hCongBABC'
    exact (cong_identity B A B hCongBABC').symm
  have hInAngle : InAngle C' B A C :=
    ⟨Ne.symm hAB, Ne.symm hAC, hC'neA, C', hBetBC'C, Or.inr (out_trivial hC'neA)⟩
  have hNColC'CA : ¬ Col C' C A := by
    intro hColC'CA
    exact hNCol (by colr)
  have hBetCC'B : Bet C C' B := between_symmetry hBetBC'C
  obtain ⟨hLtA_A, hLtA_B⟩ := l11_41_c C' C A B hNColC'CA hBetCC'B hC'neB
  have hOS : OS B A C' C :=
    out_one_side_c B A C' C
      (Or.inr (fun hColBAC =>
        hNCol (col_permutation_5_c A C B (col_permutation_1_c B A C hColBAC))))
      (bet_out hC'neB hBetBC'C)
  have hNCongContra : ¬ CongA B A C' B A C := by
    intro hAssume
    have hColAC'C : Col A C' C := out_col (conga_os_out_c B A C' C hAssume hOS)
    exact hNCol (by colr)
  have hLtA0 : LtA B A C' B A C :=
    ⟨⟨C', hInAngle, conga_refl_c B A C' (Ne.symm hAB) hC'neA⟩, hNCongContra⟩
  have hLtA1 : LtA B C A A C' B :=
    conga_preserves_lta_c C' C A A C' B B C A A C' B
      (out2_conga_c C' C A B A
        (l6_6 (bet_out (Ne.symm hCneC') hBetCC'B))
        (out_trivial hAC))
      (conga_refl_c A C' B (Ne.symm hC'neA) (Ne.symm hC'neB))
      hLtA_B
  have hCongA1 : CongA B A C' B C' A :=
    l11_44_1_a_c A B C' hAB (Ne.symm hC'neA) hCongBABC'
  have hCongA2 : CongA B A C' A C' B := conga_right_comm_c B A C' B C' A hCongA1
  have hLtA2 : LtA B C A B A C' :=
    conga_preserves_lta_c B C A A C' B B C A B A C'
      (conga_refl_c B C A hBC hAC)
      (conga_sym_c B A C' A C' B hCongA2)
      hLtA1
  exact lta_trans_c B C A B A C' B A C hLtA2 hLtA0
theorem not_lta_and_conga_c :
    ∀ (A B C D E F : Tpoint), ¬ (LtA A B C D E F ∧ CongA A B C D E F) := by
  intro b0 b1 b2 b3 b4 b5 H
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
  intro b0 b1 b2 b3 b4 b5 b6 H0
  obtain ⟨_, H1⟩ := b6
  exact ((H1 H0)).elim
theorem lta_lea_c :
    ∀ (A B C D E F : Tpoint), LtA A B C D E F → LeA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨x, x0⟩ := b6
  exact x
theorem nlta_c :
    ∀ (A B C : Tpoint), ¬ LtA A B C A B C := by
  intro A B C hLtA
  obtain ⟨⟨P, hInAngle, _⟩, hNCong⟩ := hLtA
  exact hNCong (conga_refl_c A B C hInAngle.1 hInAngle.2.1)
theorem lea_nlta_c :
    ∀ (A B C D E F : Tpoint), LeA A B C D E F → ¬ LtA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro Hlta
  obtain ⟨x, x0⟩ := Hlta
  exact x0 (lea_asym_c b3 b4 b5 b0 b1 b2 x b6)
theorem lta_nlea_c :
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
    have H1 := col_lta_bet_c b1 b0 b2 b1 b2 b0 (col_permutation_5_c b1 b0 b2 (col_permutation_4_c b0 b1 b2 H0)) b3
    exact lt_left_comm_c b2 b1 b1 b0 (lt_left_comm_c b1 b2 b1 b0 (bet_lt1213_c b1 b2 b0 H3 H1))
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

theorem cong2_conga_obtuse_cong_conga2_c :
    ∀ (A B C A' B' C' : Tpoint), Obtuse A B C → CongA A B C A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' ∧ CongA B A C B' A' C' ∧ CongA B C A B' C' A' := sorry

theorem cong2_per2_cong_conga2_c :
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
theorem cong2_per2_cong_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong B A B' A' := sorry

theorem cong2_per2_cong_3_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong_3 A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ((let H3 := cong2_per2_cong_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9; ⟨(cong_symmetry (cong_symmetry (cong_commutativity H3))), (⟨b8, b9⟩)⟩))
theorem cong_lt_per2_lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry

theorem cong_le_per2_le_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Le B C B' C' → Le A C A' C' := sorry

theorem lt2_per2_lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Lt A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry

theorem le_lt_per2_lt_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Le A B A' B' → Lt B C B' C' → Lt A C A' C' := sorry

theorem le2_per2_le_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Le A B A' B' → Le B C B' C' → Le A C A' C' := sorry

theorem cong_lt_per2_lt_1_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Lt A B A' B' → Cong A C A' C' → Lt B' C' B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  exact nle_lt_c b1 b2 b4 b5 ((fun H3 => (let l := le_lt_per2_lt_c b2 b1 b0 b5 b4 b3 (l8_2_c b0 b1 b2 b6) (l8_2_c b3 b4 b5 b7) (le_comm_c b1 b2 b4 b5 H3) (lt_left_comm_c b0 b1 b4 b3 (lt_left_comm_c b1 b0 b4 b3 (lt_left_comm_c b0 b1 b4 b3 (lt_right_comm_c b0 b1 b3 b4 b8)))); (by
  obtain ⟨x, x0⟩ := l
  exact x0 (le_anti_symmetry_c b2 b0 b5 b3 x (le_comm_c b3 b5 b0 b2 (cong_le3412_c b0 b2 b3 b5 b9)))))))
theorem symmetry_preserves_conga_c :
    ∀ (A B C A' B' C' M : Tpoint), A ≠ B → C ≠ B → Midpoint M A A' → Midpoint M B B' → Midpoint M C C' → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 =>
  (let H4 := l7_13_c b6 b0 b1 b3 b4 (l7_2_c b6 b0 b3 b9) (l7_2_c b6 b1 b4 b10); (let H5 := l7_13_c b6 b1 b2 b4 b5 (l7_2_c b6 b1 b4 b10) (l7_2_c b6 b2 b5 b11); (let H6 := l7_13_c b6 b0 b2 b3 b5 (l7_2_c b6 b0 b3 b9) (l7_2_c b6 b2 b5 b11); cong3_conga_c b0 b1 b2 b3 b4 b5 b7 b8 (⟨H4, (⟨H6, H5⟩)⟩))))
theorem l11_57_c :
    ∀ (A B C A' B' C' : Tpoint), OS A A' B B' → Per B A A' → Per B' A' A → OS A A' C C' → Per C A A' → Per C' A' A → CongA B A C B' A' C' := sorry

theorem cop3_orth_at_orth_at_c :
    ∀ (A B C D E F U V X : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth_at X A B C U V → Orth_at X D E F U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  obtain ⟨x, x0⟩ := b13
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨b9, (⟨x1, (⟨(coplanar_pseudo_trans_c b3 b4 b5 b8 b0 b1 b2 x b10 b11 b12 x3), (⟨x5, ((let HCop := fun M => coplanar_pseudo_trans_c b3 b4 b5 M b0 b1 b2 x b10 b11 b12; (let H3 := fun M => coplanar_pseudo_trans_c b0 b1 b2 M b3 b4 b5 b9 (HCop b0 (coplanar_perm_23_c b0 b2 b1 b0 (coplanar_perm_23_c b0 b1 b2 b0 (coplanar_perm_11_c b0 b0 b2 b1 (coplanar_trivial_c b0 b2 b1))))) (HCop b1 (coplanar_perm_23_c b1 b2 b1 b0 (coplanar_perm_23_c b0 b1 b2 b1 (coplanar_perm_21_c b1 b1 b2 b0 (coplanar_trivial_c b1 b2 b0))))) (HCop b2 (coplanar_perm_23_c b2 b2 b1 b0 (coplanar_trivial_c b2 b1 b0))); fun P Q H4 H5 => x6 P Q (H3 P H4) H5)))⟩)⟩)⟩)⟩
theorem col2_orth_at_orth_at_c :
    ∀ (A B C P Q U V X : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth_at X A B C P Q → Orth_at X A B C U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨x, x0⟩ := b11
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨x, (⟨b8, (⟨x3, (⟨(col3_c b3 b4 b5 b6 b7 x1 b9 b10 x5), (fun D W HD HW => x6 D W HD (colx_c b5 b6 W b3 b4 b8 b9 b10 HW))⟩)⟩)⟩)⟩
theorem col_orth_at_orth_at_c :
    ∀ (A B C U V W X : Tpoint), U ≠ W → Col U V W → Orth_at X A B C U V → Orth_at X A B C U W :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  col2_orth_at_orth_at_c b0 b1 b2 b3 b4 b3 b5 b6 b7 (col_trivial_3_c b3 b4) b8 b9
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
theorem cop3_orth_orth_c :
    ∀ (A B C D E F U V : Tpoint), ¬ Col D E F → Coplanar A B C D → Coplanar A B C E → Coplanar A B C F → Orth A B C U V → Orth D E F U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  obtain ⟨x, x0⟩ := b12
  exact ⟨x, (cop3_orth_at_orth_at_c b0 b1 b2 b3 b4 b5 b6 b7 x b8 b9 b10 b11 x0)⟩
theorem col2_orth_orth_c :
    ∀ (A B C P Q U V : Tpoint), U ≠ V → Col P Q U → Col P Q V → Orth A B C P Q → Orth A B C U V := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  obtain ⟨x, x0⟩ := b10
  exact ⟨x, (col2_orth_at_orth_at_c b0 b1 b2 b3 b4 b5 b6 x b7 b8 b9 x0)⟩
theorem col_orth_orth_c :
    ∀ (A B C U V W : Tpoint), U ≠ W → Col U V W → Orth A B C U V → Orth A B C U W :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 =>
  col2_orth_orth_c b0 b1 b2 b3 b4 b3 b5 b6 (col_trivial_3_c b3 b4) b7 b8
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
theorem col_cop_orth_orth_at_c :
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
    ∀ (A B C D E P : Tpoint), ¬ Col A B C → Per A D P → Per B D P → Per C D P → Coplanar A B C E → Per E D P := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have o := point_equality_decidability b3 b5
  rcases o with x | x
  · rw [x] at *
    exact l8_5_c b4 b5
  · have e := symmetric_point_construction_c b5 b3
    obtain ⟨x0, x1⟩ := e
    exact ⟨x0, (⟨x1, (l11_60_aux_c b0 b1 b2 b4 b5 x0 b6 (per_double_cong_c b0 b3 b5 x0 b7 x1) (per_double_cong_c b1 b3 b5 x0 b8 x1) (per_double_cong_c b2 b3 b5 x0 b9 x1) b10)⟩)⟩
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
  fun _b0 _b1 _b2 b3 b4 b5 b6 b7 b8 b9 =>
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
theorem orth_at2_eq_c :
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
theorem col_cop_orth_at_eq_c :
    ∀ (A B C U V X Y : Tpoint), Orth_at X A B C U V → Coplanar A B C Y → Col U V Y → X = Y :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  orth_at2_eq_c b0 b1 b2 b3 b4 b5 b6 b7 (col_cop_orth_orth_at_c b0 b1 b2 b3 b4 b6 (⟨b5, b7⟩) b8 b9)
theorem orth_at_ncop1_c :
    ∀ (A B C U V X : Tpoint), U ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C U :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  (fun HCop => b6 (Eq.symm (col_cop_orth_at_eq_c b0 b1 b2 b3 b4 b5 b3 b7 HCop (col_trivial_3_c b3 b4))))
theorem orth_at_ncop2_c :
    ∀ (A B C U V X : Tpoint), V ≠ X → Orth_at X A B C U V → ¬ Coplanar A B C V :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  orth_at_ncop1_c b0 b1 b2 b4 b3 b5 b6 (orth_at_symmetry_c b0 b1 b2 b3 b4 b5 b7)
theorem orth_at_ncop_c :
    ∀ (A B C P X : Tpoint), Orth_at X A B C X P → ¬ Coplanar A B C P := by
  intro b0 b1 b2 b3 b4 b5
  have Hd := b5
  have Hd0 := orth_at_distincts_c b0 b1 b2 b4 b3 b4 Hd
  obtain ⟨_, H0⟩ := Hd0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact orth_at_ncop2_c b0 b1 b2 b4 b3 b4 (Ne.symm H2) b5
theorem l11_62_existence_c :
    ∀ (A B C P : Tpoint), ∃ (D : Tpoint), Coplanar A B C D ∧ ∀ (E : Tpoint), Coplanar A B C E → Per E D P := sorry

theorem l11_62_existence_bis_c :
    ∀ (A B C P : Tpoint), ¬ Coplanar A B C P → ∃ (X : Tpoint), Orth_at X A B C X P := sorry

theorem l11_63_aux_c :
    ∀ (A B C D E P : Tpoint), Coplanar A B C D → D ≠ E → Orth_at E A B C E P → ∃ (Q : Tpoint), OS D E P Q ∧ Orth A B C D Q := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have H' := b8
  obtain ⟨x, x0⟩ := H'
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  have HNCop := (fun H2 => x1 (col_cop_orth_at_eq_c b0 b1 b2 b4 b5 b4 b5 b8 H2 (col_trivial_2_c b4 b5)))
  have e := l10_15_c b3 b4 b3 b5 (col_trivial_3_c b3 b4) ((fun H2 => HNCop (col_cop2_cop_c b0 b1 b2 b3 b4 b5 b7 b6 x3 H2)))
  obtain ⟨x7, x8⟩ := e
  obtain ⟨x9, x10⟩ := x8
  exact ⟨x7, (⟨x10, ((let e0 := ex_ncol_cop_c b0 b1 b2 b3 b4 b7; (by
  obtain ⟨x11, x12⟩ := e0
  obtain ⟨x13, x14⟩ := x12
  have e1 := ex_perp_cop_c b3 b4 b3 x11 b7
  obtain ⟨x15, x16⟩ := e1
  obtain ⟨x17, x18⟩ := x16
  have H5 := (let H5 := not_col_distincts_c b3 b4 x11 x14; (let H6 := H5; (by
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, _⟩ := H8
  have H9 := not_col_distincts_c b0 b1 b2 x
  have H10 := H9
  obtain ⟨_, H11⟩ := H10
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  have H13 := perp_distinct_c b3 b4 x15 b3 x17
  have H14 := H13
  obtain ⟨_, H15⟩ := H14
  have H16 := perp_distinct_c b3 b4 x7 b3 x9
  have H17 := H16
  obtain ⟨_, _⟩ := H17
  exact per_not_col_c x15 b3 b4 H15 b7 (perp_in_per_c x15 b3 b4 (perp_in_sym_c b3 b4 x15 b3 b3 (perp_perp_in_c b3 b4 x15 x17))))))
  have H6 := coplanar_pseudo_trans_c b3 b4 x11 b0 b0 b1 b2 x b6 x3 x13 (coplanar_perm_1_c b0 b1 b0 b2 (col_coplanar_c b0 b1 b0 b2 (col_trivial_3_c b0 b1)))
  have H7 := coplanar_pseudo_trans_c b3 b4 x11 b1 b0 b1 b2 x b6 x3 x13 (coplanar_perm_1_c b0 b1 b1 b2 (col_coplanar_c b0 b1 b1 b2 (col_trivial_2_c b0 b1)))
  have H8 := coplanar_pseudo_trans_c b3 b4 x11 b2 b0 b1 b2 x b6 x3 x13 (coplanar_perm_4_c b0 b2 b2 b1 (col_coplanar_c b0 b2 b2 b1 (col_trivial_2_c b0 b2)))
  exact ⟨b3, (cop3_orth_at_orth_at_c x15 b3 b4 b0 b1 b2 b3 x7 b3 x (coplanar_pseudo_trans_c x15 b3 b4 b0 b3 b4 x11 x14 x18 (coplanar_perm_1_c b3 b4 b3 x11 (col_coplanar_c b3 b4 b3 x11 (col_trivial_3_c b3 b4))) (coplanar_perm_1_c b3 b4 b4 x11 (col_coplanar_c b3 b4 b4 x11 (col_trivial_2_c b3 b4))) H6) (coplanar_pseudo_trans_c x15 b3 b4 b1 b3 b4 x11 x14 x18 (coplanar_perm_1_c b3 b4 b3 x11 (col_coplanar_c b3 b4 b3 x11 (col_trivial_3_c b3 b4))) (coplanar_perm_1_c b3 b4 b4 x11 (col_coplanar_c b3 b4 b4 x11 (col_trivial_2_c b3 b4))) H7) (coplanar_pseudo_trans_c x15 b3 b4 b2 b3 b4 x11 x14 x18 (coplanar_perm_1_c b3 b4 b3 x11 (col_coplanar_c b3 b4 b3 x11 (col_trivial_3_c b3 b4))) (coplanar_perm_1_c b3 b4 b4 x11 (col_coplanar_c b3 b4 b4 x11 (col_trivial_2_c b3 b4))) H8) ((let H9 := not_col_distincts_c x15 b3 b4 H5; (let H10 := H9; (by
  obtain ⟨_, H11⟩ := H10
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  have H13 := not_col_distincts_c b3 b4 x11 x14
  have H14 := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  obtain ⟨_, _⟩ := H16
  have H17 := not_col_distincts_c b0 b1 b2 x
  have H18 := H17
  obtain ⟨_, H19⟩ := H18
  obtain ⟨_, H20⟩ := H19
  obtain ⟨_, _⟩ := H20
  have H21 := perp_distinct_c b3 b4 x7 b3 x9
  have H22 := H21
  obtain ⟨_, H23⟩ := H22
  exact l11_60_bis_c x15 b3 b4 b3 x7 H5 (Ne.symm H23) (coplanar_perm_1_c x15 b3 b3 b4 (col_coplanar_c x15 b3 b3 b4 (col_trivial_2_c x15 b3))) ((let e2 := ex_perp_cop_c b3 b4 b4 x11 b7; (by
  obtain ⟨x19, x20⟩ := e2
  obtain ⟨x21, x22⟩ := x20
  have H25 := perp_distinct_c b3 b4 x19 b4 x21
  have H26 := H25
  obtain ⟨_, H27⟩ := H26
  exact l11_61_c b4 x19 b5 b3 x15 x7 (Ne.symm b7) (Ne.symm H27) x1 (coplanar_trans_1_c x11 b4 b3 x19 x15 (not_col_permutation_5_c x11 b3 b4 (not_col_permutation_2_c b3 b4 x11 x14)) ((let H28 := perp_coplanar_c b3 b4 x19 b4 x21; (let H29 := perp_coplanar_c b3 b4 x15 b3 x17; (let H30 := perp_coplanar_c b3 b4 x7 b3 x9; (let H31 := os_coplanar_c b3 b4 b5 x7 x10; coplanar_perm_14_c b3 b4 x11 x19 x22))))) ((let H28 := perp_coplanar_c b3 b4 x19 b4 x21; (let H29 := perp_coplanar_c b3 b4 x15 b3 x17; (let H30 := perp_coplanar_c b3 b4 x7 b3 x9; (let H31 := os_coplanar_c b3 b4 b5 x7 x10; coplanar_perm_14_c b3 b4 x11 x15 x18)))))) (perp_in_per_c x19 b4 b3 (perp_in_sym_c b4 b3 x19 b4 b4 (perp_perp_in_c b4 b3 x19 (perp_left_comm_c b3 b4 x19 b4 x21)))) (perp_in_per_c x15 b3 b4 (perp_in_sym_c b3 b4 x15 b3 b3 (perp_perp_in_c b3 b4 x15 x17))) ((let HQ3 := os_coplanar_c b3 b4 b5 x7 x10; (let H28 := perp_coplanar_c b3 b4 x19 b4 x21; (let H29 := perp_coplanar_c b3 b4 x15 b3 x17; (let H30 := perp_coplanar_c b3 b4 x7 b3 x9; coplanar_perm_6_c b3 b4 b5 x7 HQ3))))) (l8_2_c b3 b4 b5 (x6 b3 b5 b6 (col_trivial_2_c b4 b5))) (x6 x19 b5 (coplanar_pseudo_trans_c b0 b1 b2 x19 b3 b4 x11 x14 H6 H7 H8 x22) (col_trivial_2_c b4 b5))))) (l8_2_c x7 b3 b3 (l8_5_c x7 b3)) (perp_in_per_c b4 b3 x7 (perp_in_left_comm_c b3 b4 b3 x7 b3 (perp_in_right_comm_c b3 b4 x7 b3 b3 (perp_perp_in_c b3 b4 x7 x9)))))))))⟩)))⟩)⟩
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

theorem mid2_orth_at2_cong_c :
    ∀ (A B C X Y P Q P' Q' : Tpoint), Orth_at X A B C X P → Orth_at Y A B C Y Q → Midpoint X P P' → Midpoint Y Q Q' → Cong P Q P' Q' := sorry

theorem orth_at2_tsp_ts_c :
    ∀ (A B C X Y P Q : Tpoint), P ≠ Q → Orth_at P A B C P X → Orth_at Q A B C Q Y → TSP A B C X Y → TS P Q X Y := sorry

theorem orth_dec_c :
    ∀ (A B C U V : Tpoint), Orth A B C U V ∨ ¬ Orth A B C U V := by
  intro b0 b1 b2 b3 b4
  first
    | Tfinish
    | (subst_vars; first | assumption | Tfinish | tauto)
    | tauto
theorem orth_at_dec_c :
    ∀ (A B C U V X : Tpoint), Orth_at X A B C U V ∨ ¬ Orth_at X A B C U V := by
  intro b0 b1 b2 b3 b4 b5
  have o := orth_dec_c b0 b1 b2 b3 b4
  rcases o with x | x
  · have o0 := cop_dec_c b0 b1 b2 b5
    rcases o0 with x0 | x0
    · have o1 := col_dec_c b3 b4 b5
      rcases o1 with x1 | x1
      · exact Or.inl (col_cop_orth_orth_at_c b0 b1 b2 b3 b4 b5 x x0 x1)
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
    ∀ (A B C X Y : Tpoint), TSP A B C X Y ∨ ¬ TSP A B C X Y := by
  intro b0 b1 b2 b3 b4
  first
    | Tfinish
    | (subst_vars; first | assumption | Tfinish | tauto)
    | tauto
theorem osp_dec_c :
    ∀ (A B C X Y : Tpoint), OSP A B C X Y ∨ ¬ OSP A B C X Y := by
  intro b0 b1 b2 b3 b4
  first
    | Tfinish
    | (subst_vars; first | assumption | Tfinish | tauto)
    | tauto
theorem ts2_inangle_c :
    ∀ (A B C P : Tpoint), TS A C B P → TS B P A C → InAngle P A B C := sorry

theorem os_ts_inangle_c :
    ∀ (A B C P : Tpoint), TS B P A C → OS B A C P → InAngle P A B C := by
  intro A B C P hTS hOS
  have hNCol : ¬ Col A B P := hTS.1
  have hNColBAC : ¬ Col B A C := one_side_not_col123_c B A C P hOS
  obtain ⟨P', hMidBPP'⟩ := symmetric_point_construction_c P B
  have hPB : P ≠ B := fun h => hNCol (h ▸ col_trivial_2_c A B)
  have hBP' : B ≠ P' := by
    intro hEq
    apply hPB
    rw [← hEq] at hMidBPP'
    exact cong_identity P B B hMidBPP'.2
  have hNColBAP : ¬ Col B A P := fun h => hNCol (col_permutation_4_c B A P h)
  have hNColBAP' : ¬ Col B A P' := by
    intro hColBAP'
    apply hNCol
    have hColPBP' : Col P B P' := bet_col_c P B P' hMidBPP'.1
    have hColBP'A : Col B P' A := col_permutation_5_c B A P' hColBAP'
    have hColBP'P : Col B P' P := col_permutation_1_c P B P' hColPBP'
    exact col_permutation_4_c B A P (col_transitivity_1_c B P' A P hBP' hColBP'A hColBP'P)
  rcases two_sides_in_angle_c A B C P P' hBP' hTS hMidBPP'.1 with hInAngleP | hInAngleP'
  · exact hInAngleP
  · exfalso
    have hNColABC : ¬ Col A B C := fun h => hNColBAC (col_permutation_4_c A B C h)
    have hOSABP'C : OS A B P' C := in_angle_one_side_c A B C P' hNColABC hNColBAP' hInAngleP'
    have hOSBAP'C : OS B A P' C := invert_one_side_c A B P' C hOSABP'C
    have hOSBAPP' : OS B A P P' :=
      one_side_transitivity_c B A P C P' (one_side_symmetry_c B A C P hOS) (one_side_symmetry_c B A P' C hOSBAP'C)
    have hTSBAPP' : TS B A P P' := bet_ts_c B A P P' hBP' hNColBAP hMidBPP'.1
    exact l9_9_c B A P P' hTSBAPP' hOSBAPP'

theorem os2_inangle_c :
    ∀ (A B C P : Tpoint), OS B A C P → OS B C A P → InAngle P A B C :=
  fun b0 b1 b2 b3 b4 b5 =>
  os_ts_inangle_c b0 b1 b2 b3 (l9_31_c b1 b0 b3 b2 (one_side_symmetry_c b1 b0 b2 b3 b4) (one_side_symmetry_c b1 b2 b0 b3 b5)) b4
theorem acute_conga_acute_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → CongA A B C D E F → Acute D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  acute_lea_acute_c b3 b4 b5 b0 b1 b2 b6 (conga_lea_c b3 b4 b5 b0 b1 b2 (conga_sym_c b0 b1 b2 b3 b4 b5 b7))
theorem acute_out2_acute_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Acute A B C → Acute A' B C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  acute_conga_acute_c b0 b1 b2 b3 b1 b4 b7 (out2_conga_c b0 b1 b2 b3 b4 b5 b6)
theorem conga_obtuse_obtuse_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → CongA A B C D E F → Obtuse D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  lea_obtuse_obtuse_c b3 b4 b5 b0 b1 b2 b6 (conga_lea_c b0 b1 b2 b3 b4 b5 b7)
theorem obtuse_out2_obtuse_c :
    ∀ (A B C A' C' : Tpoint), Out B A' A → Out B C' C → Obtuse A B C → Obtuse A' B C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  conga_obtuse_obtuse_c b0 b1 b2 b3 b1 b4 b7 (out2_conga_c b0 b1 b2 b3 b4 b5 b6)
theorem bet_lea_bet_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → LeA A B C D E F → Bet D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  exact bet_conga_bet_c b0 b1 b2 b3 b4 b5 b6 (lea_asym_c b0 b1 b2 b3 b4 b5 b7 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b7; (by
  obtain ⟨H, H0⟩ := Hlea0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  exact l11_31_2_c b3 b4 b5 b0 b1 b2 H3 H4 H H1 b6))))
theorem out_lea_out_c :
    ∀ (A B C D E F : Tpoint), Out E D F → LeA A B C D E F → Out B A C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  exact l11_21_a_c b3 b4 b5 b0 b1 b2 b6 (lea_asym_c b3 b4 b5 b0 b1 b2 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b7; (by
  obtain ⟨H, H0⟩ := Hlea0
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, _⟩ := H2
  exact l11_31_1_c b3 b4 b5 b0 b1 b2 b6 H H1))) b7)
theorem bet2_lta_lta_c :
    ∀ (A B C D E F A' D' : Tpoint), LtA A B C D E F → Bet A B A' → A' ≠ B → Bet D E D' → D' ≠ E → LtA D' E F A' B C := sorry

theorem lea123456_lta_lta_c :
    ∀ (A B C D E F G H I : Tpoint), LeA A B C D E F → LtA D E F G H I → LtA A B C G H I := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨(lea_trans_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 (lta_lea_c b3 b4 b5 b6 b7 b8 b10)), ((fun H0 => (by
  obtain ⟨x, x0⟩ := b10
  exact x0 (lea_asym_c b3 b4 b5 b6 b7 b8 x (l11_30_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b3 b4 b5 b9 H0 ((let Hlea0 := lea_distincts_c b0 b1 b2 b3 b4 b5 b9; (by
  obtain ⟨_, H2⟩ := Hlea0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  exact conga_refl_c b3 b4 b5 H4 H5))))))))⟩
theorem lea456789_lta_lta_c :
    ∀ (A B C D E F G H I : Tpoint), LtA A B C D E F → LeA D E F G H I → LtA A B C G H I := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨(lea_trans_c b0 b1 b2 b3 b4 b5 b6 b7 b8 (lta_lea_c b0 b1 b2 b3 b4 b5 b9) b10), ((fun H0 => (by
  obtain ⟨x, x0⟩ := b9
  exact x0 (lea_asym_c b0 b1 b2 b3 b4 b5 x (l11_30_c b3 b4 b5 b6 b7 b8 b3 b4 b5 b0 b1 b2 b10 ((let Hlea0 := lea_distincts_c b3 b4 b5 b6 b7 b8 b10; (by
  obtain ⟨H1, H2⟩ := Hlea0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact conga_refl_c b3 b4 b5 H1 H3))) (conga_sym_c b0 b1 b2 b6 b7 b8 H0))))))⟩
theorem acute_per_lta_c :
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
theorem obtuse_per_lta_c :
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
theorem acute_obtuse_lta_c :
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
  exact obtuse_per_lta_c b3 b4 b5 x x1 x3 b7 H5 (Ne.symm H7) x5)))
theorem lea_in_angle_c :
    ∀ (A B C P : Tpoint), LeA A B P A B C → OS A B C P → InAngle P A B C := by
  intro A B C P hLeA hOS
  obtain ⟨T, hInAngleT, hCongABPABT⟩ := hLeA
  have hCongABCABC : CongA A B C A B C := conga_refl_c A B C hInAngleT.1 hInAngleT.2.1
  have hCongABTABP : CongA A B T A B P := conga_sym_c A B P A B T hCongABPABT
  have hOSABPC : OS A B P C := one_side_symmetry_c A B C P hOS
  exact conga_preserves_in_angle_c A B C T A B C P hCongABCABC hCongABTABP hInAngleT hOSABPC

theorem acute_bet_obtuse_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Acute A B C → Obtuse A' B C := by
  intro A B C A' HBet HA'B Hacute
  obtain ⟨HAB, HCB⟩ := acute_distincts_c A B C Hacute
  rcases col_dec_c A B C with hCol | hNCol1
  · rcases bet_dec_c A B C with hBet2 | hNBet2
    · exfalso
      apply nlta_c A B C
      exact acute_obtuse_lta_c A B C A B C Hacute (bet_obtuse_c A B C hBet2 HAB (Ne.symm HCB))
    · have hOut := not_bet_out_c A B C hCol hNBet2
      exact bet_obtuse_c A' B C (between_symmetry_c C B A' ((l6_2_c A C A' B HAB HCB HA'B HBet).mpr hOut)) HA'B (Ne.symm HCB)
  · obtain ⟨D, hPerp, hOS⟩ := l10_15_c A B B C (col_trivial_2_c A B) hNCol1
    have hPerAB_D : Per A B D := perp_per_2_c B A D (perp_comm_c A B D B hPerp)
    have hBD : B ≠ D := Ne.symm (perp_not_eq_2_c A B D B hPerp)
    have hNCol2 : ¬ Col C B D := by
      intro hColCBD
      apply nlta_c A B C
      exact acute_per_lta_c A B C A B C Hacute HAB (Ne.symm HCB)
        (per_col_c A B D C hBD hPerAB_D (col_permutation_1_c C B D hColCBD))
    have hNColBCA : ¬ Col B C A := fun h => hNCol1 (col_permutation_2_c B C A h)
    have hQ1pre : TS B C A A' := bet_ts_c B C A A' (Ne.symm HA'B) hNColBCA HBet
    have hQ1 : TS B C A' A := l9_2_c B C A A' hQ1pre
    have hP7 : OS B A' C D := col2_os_os_c A B B A' C D (Ne.symm HA'B) (col_trivial_2_c A B) (bet_col_c A B A' HBet) hOS
    have hLtAABCABD : LtA A B C A B D := acute_per_lta_c A B C A B D Hacute HAB hBD hPerAB_D
    have hLeAABCABD : LeA A B C A B D := lta_lea_c A B C A B D hLtAABCABD
    have hInAngleCABD : InAngle C A B D := lea_in_angle_c A B D C hLeAABCABD (one_side_symmetry_c A B C D hOS)
    have hInAngleCDBA : InAngle C D B A := l11_24_c C A B D hInAngleCABD
    have hNColBDC : ¬ Col B D C := fun h => hNCol2 (col_permutation_2_c B D C h)
    have hNColBAC : ¬ Col B A C := fun h => hNCol1 (col_permutation_4_c B A C h)
    have hTS_CBDA : TS C B D A := in_angle_two_sides_c D B A C hNColBDC hNColBAC hInAngleCDBA
    have hTS_BCDA : TS B C D A := invert_two_sides_c C B D A hTS_CBDA
    have hOS_BCA'D : OS B C A' D := l9_8_1_c B C A' D A hQ1 hTS_BCDA
    have hT1A : InAngle D A' B C := os2_inangle_c A' B C D hP7 hOS_BCA'D
    have hCongDBADBA' : CongA D B A D B A' :=
      l11_18_1_c D B A A' HBet (Ne.symm HAB) (Ne.symm HA'B) (Ne.symm hBD) (l8_2_c A B D hPerAB_D)
    have hCongABDA'BD : CongA A B D A' B D := conga_comm_c D B A D B A' hCongDBADBA'
    have hT2 : LeA A B D A' B C := ⟨D, hT1A, hCongABDA'BD⟩
    have hNotCongABDA'BC : ¬ CongA A B D A' B C := by
      intro hCongABDA'BC
      have hCongA'BCA'BD : CongA A' B C A' B D :=
        conga_trans_c A' B C A B D A' B D (conga_sym_c A B D A' B C hCongABDA'BC) hCongABDA'BD
      have hPerA'BD : Per A' B D := l11_17_c A B D A' B D hPerAB_D hCongABDA'BD
      have hPerA'BC : Per A' B C := l11_17_c A' B D A' B C hPerA'BD (conga_sym_c A' B C A' B D hCongA'BCA'BD)
      have hOSA'BDC : OS A' B D C := one_side_symmetry_c A' B C D (invert_one_side_c B A' C D hP7)
      have hOutBDC : Out B D C := l11_19_c A' B D C hPerA'BD hPerA'BC hOSA'BDC
      exact hNCol2 (col_permutation_2_c B D C (out_col_c B D C hOutBDC))
    have hLtAABDA'BC : LtA A B D A' B C := ⟨hT2, hNotCongABDA'BC⟩
    exact ⟨A, B, D, hPerAB_D, hLtAABDA'BC⟩

theorem bet_obtuse_acute_c :
    ∀ (A B C A' : Tpoint), Bet A B A' → A' ≠ B → Obtuse A B C → Acute A' B C := sorry

theorem inangle_dec_c :
    ∀ (A B C P : Tpoint), InAngle P A B C ∨ ¬ InAngle P A B C := by
  intro b0 b1 b2 b3
  first
    | Tfinish
    | (subst_vars; first | assumption | Tfinish | tauto)
    | tauto
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
              · exact Or.inr ((fun H5 => HENBet (bet_lea_bet_c b0 b1 b2 b3 b4 b5 (not_out_bet_c b0 b1 b2 H3 H4) H5)))
          · rcases (col_dec_c b3 b4 b5) with H3 | H3
            · rcases (bet_dec_c b3 b4 b5) with H4 | H4
              · exact Or.inl (l11_31_2_c b0 b1 b2 b3 b4 b5 H (Ne.symm H0) H1 (Ne.symm H2) H4)
              · exact Or.inr ((fun H5 => HNColB (col_permutation_4_c b1 b0 b2 (out_col (out_lea_out_c b0 b1 b2 b3 b4 b5 (not_bet_out_c b3 b4 b5 H3 H4) H5)))))
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
  exact ⟨x, (⟨(os2_inangle_c b0 b1 b2 x (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2)) (cop_nts_os_c b1 b2 b0 x ((let H4 := os_coplanar_c b0 b1 x b2 x2; coplanar_perm_10_c b0 b1 x b2 H4)) H ((fun H4 => HNlea (conga_lea_c b0 b1 b2 b3 b4 b5 (l11_10_c b0 b1 x b3 b4 b5 b0 b2 b3 b5 (conga_sym_c b3 b4 b5 b0 b1 x x1) (out_trivial b6) (col_one_side_out_c b1 b0 b2 x (col_permutation_5_c b1 x b2 (col_permutation_4_c x b1 b2 H4)) (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2))) (out_trivial b8) (out_trivial (Ne.symm b9)))))) ((fun H4 => HNlea (l11_30_c b0 b1 b2 b0 b1 x b0 b1 b2 b3 b4 b5 (⟨b2, (⟨(os_ts_inangle_c b0 b1 x b2 H4 (one_side_symmetry_c b1 b0 b2 x (one_side_symmetry_c b1 b0 x b2 (invert_one_side_c b0 b1 x b2 x2)))), (conga_refl_c b0 b1 b2 b6 (Ne.symm b7))⟩)⟩) (conga_refl_c b0 b1 b2 b6 (Ne.symm b7)) (conga_sym_c b3 b4 b5 b0 b1 x x1)))))), x1⟩)⟩))))
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

theorem conga_acute_c :
    ∀ (A B C : Tpoint), CongA A B C A C B → Acute A B C := sorry

theorem cong_acute_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → Cong A B A C → Acute A B C := by
  intro b0 b1 b2 b3 b4 b5
  exact conga_acute_c b0 b1 b2 ((let H := cong_diff b3 b5; (let a := l11_51_c b0 b1 b2 b0 b2 b1 b3 H b4 b5 (cong_symmetry b5) (cong_symmetry (cong_symmetry (cong_right_commutativity (cong_reflexivity b1 b2)))); (by
  obtain ⟨x, x0⟩ := a
  obtain ⟨x1, x2⟩ := x0
  exact x1))))
theorem nlta_lea_c :
    ∀ (A B C D E F : Tpoint), ¬ LtA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LeA D E F A B C := sorry

theorem nlea_lta_c :
    ∀ (A B C D E F : Tpoint), ¬ LeA A B C D E F → A ≠ B → B ≠ C → D ≠ E → E ≠ F → LtA D E F A B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  exact ⟨((by
  rcases (lea_total_c b3 b4 b5 b0 b1 b2 b9 b10 b7 b8) with H3 | H3
  · exact H3
  · exact ((b6 H3)).elim)), ((fun H3 => b6 (conga_lea_c b0 b1 b2 b3 b4 b5 (conga_sym_c b3 b4 b5 b0 b1 b2 H3))))⟩
theorem triangle_strict_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → ¬ Bet A B C → Lt A C A D := sorry

theorem triangle_inequality_c :
    ∀ (A B C D : Tpoint), Bet A B D → Cong B C B D → Le A C A D := by
  intro b0 b1 b2 b3 b4 b5
  rcases (bet_dec_c b0 b1 b2) with H | H
  · rcases (point_equality_decidability b0 b1) with H0 | H0
    · rw [H0] at *
      exact cong_le3412_c b1 b3 b1 b2 (le_anti_symmetry_c b1 b3 b1 b2 (cong_le3412_c b1 b2 b1 b3 b5) (cong_le_c b1 b2 b1 b3 b5))
    · have H1 := construction_uniqueness H0 H b5 b4 ((by cong_r))
      rw [H1] at *
      exact le_reflexivity_c b0 b3
  · have Hlt := triangle_strict_inequality_c b0 b1 b2 b3
    have l := Hlt b4 b5 H
    obtain ⟨x, x0⟩ := l
    exact x
theorem triangle_strict_inequality_2_c :
    ∀ (A B C A' B' C' : Tpoint), Bet A' B' C' → Cong A B A' B' → Cong B C B' C' → ¬ Bet A B C → Lt A C A' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have e := segment_construction b0 b1 b1 b2
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact cong2_lt_lt_c b0 b2 b0 x b0 b2 b3 b5 (triangle_strict_inequality_c b0 b1 b2 x x1 (cong_symmetry x2) b9) (cong_reflexivity b0 b2) (l2_11 x1 b6 b7 (cong_transitivity x2 b8))
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

theorem os3_lta_c :
    ∀ (A B C D : Tpoint), OS A B C D → OS B C A D → OS A C B D → LtA B A C B D C := sorry

theorem bet_le_lt_c :
    ∀ (A B C D : Tpoint), Bet A D B → A ≠ D → D ≠ B → Le A C B C → Lt D C B C := sorry

theorem cong2_ncol_c :
    ∀ (P A B C : Tpoint), A ≠ B → B ≠ C → A ≠ C → Cong A P B P → Cong A P C P → ¬ Col A B C := sorry

theorem cong4_cop2_eq_c :
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

theorem reflectl_conga_c :
    ∀ (A B P P' : Tpoint), A ≠ B → B ≠ P → ReflectL P P' A B → CongA A B P A B P' := sorry

theorem conga_cop_out_reflectl_out_c :
    ∀ (A B C P T T' : Tpoint), ¬ Out B A C → Coplanar A B C P → CongA P B A P B C → Out B A T → ReflectL T T' B P → Out B C T' := sorry

theorem col_conga_cop_reflectl_col_c :
    ∀ (A B C P T T' : Tpoint), ¬ Out B A C → Coplanar A B C P → CongA P B A P B C → Col B A T → ReflectL T T' B P → Col B C T' := sorry

theorem conga2_cop2_col_c :
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
  exact cong3_cop2_col_c b1 b3 b4 b0 x (coplanar_perm_9_c b0 b1 b3 b4 b8) (coplanar_perm_12_c b3 b4 b1 x (col_cop_cop_c b3 b4 b1 b2 x (coplanar_perm_16_c b1 b2 b3 b4 b9) (Ne.symm H10) (col_permutation_5_c b1 x b2 (out_col x1)))) ((fun H16 => (by
  subst H16
  exact b5 x1))) (cong_symmetry x2) x3 x5
theorem conga2_cop2_col_1_c :
    ∀ (A B C P P' : Tpoint), ¬ Col A B C → CongA P B A P B C → CongA P' B A P' B C → Coplanar A B C P → Coplanar A B C P' → Col B P P' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  conga2_cop2_col_c b0 b1 b2 b3 b4 ((fun H => b5 (col_permutation_4_c b1 b0 b2 (out_col H)))) b6 b7 (coplanar_pseudo_trans_c b0 b1 b3 b4 b0 b1 b2 b5 (coplanar_perm_1_c b0 b1 b0 b2 (col_coplanar_c b0 b1 b0 b2 (col_trivial_3_c b0 b1))) (coplanar_perm_1_c b0 b1 b1 b2 (col_coplanar_c b0 b1 b1 b2 (col_trivial_2_c b0 b1))) b8 b9) (coplanar_pseudo_trans_c b1 b2 b3 b4 b0 b1 b2 b5 (coplanar_perm_1_c b0 b1 b1 b2 (col_coplanar_c b0 b1 b1 b2 (col_trivial_2_c b0 b1))) (coplanar_perm_4_c b0 b2 b2 b1 (col_coplanar_c b0 b2 b2 b1 (col_trivial_2_c b0 b2))) b8 b9)
theorem col_conga_conga_c :
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
theorem cop_inangle_ex_col_inangle_c :
    ∀ (A B C P Q : Tpoint), ¬ Out B A C → InAngle P A B C → Coplanar A B C Q → ∃ (R : Tpoint), InAngle R A B C ∧ P ≠ R ∧ Col P Q R := sorry

theorem col_inangle2_out_c :
    ∀ (A B C P Q : Tpoint), ¬ Bet A B C → InAngle P A B C → InAngle Q A B C → Col B P Q → Out B P Q := sorry

theorem inangle2_lea_c :
    ∀ (A B C P Q : Tpoint), InAngle P A B C → InAngle Q A B C → LeA P B Q A B C := sorry

theorem conga_inangle_per_acute_c :
    ∀ (A B C P : Tpoint), Per A B C → InAngle P A B C → CongA P B A P B C → Acute A B P := sorry

theorem conga_inangle2_per_acute_c :
    ∀ (A B C P Q : Tpoint), Per A B C → InAngle P A B C → CongA P B A P B C → InAngle Q A B C → Acute P B Q := sorry

theorem lta_os_ts_c :
    ∀ (A O B P : Tpoint), ¬ Col A O P → LtA A O P A O B → OS O A B P → TS O P A B := sorry

theorem bet_suppa_c :
    ∀ (A B C A' : Tpoint), A ≠ B → B ≠ C → B ≠ A' → Bet A B A' → SuppA A B C C B A' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b4, (⟨b3, (⟨b7, (conga_refl_c b2 b1 b3 (Ne.symm b5) (Ne.symm b6))⟩)⟩)⟩
theorem ex_suppa_c :
    ∀ (A B C : Tpoint), A ≠ B → B ≠ C → ∃ (D E F : Tpoint), SuppA A B C D E F := by
  intro b0 b1 b2 b3 b4
  have e := segment_construction b0 b1 b0 b1
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact ⟨b2, (⟨b1, (⟨x, (bet_suppa_c b0 b1 b2 x b3 b4 ((fun H4 => (by
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
  exact ⟨x, (⟨x1, (conga_trans_c b3 b4 b5 b2 b1 A' b0 b1 x H6 ((let H15 := bet_neq12_neq x1 H10; (let H16 := bet_neq12_neq H3 H0; (let H17 := cong_diff_3_c b1 x b2 b1 H10 x2; conga_left_comm_c A' b1 b2 b0 b1 x (l11_14_c A' b1 b2 b0 x (between_symmetry H3) H11 H0 x1 (Ne.symm H10) H17))))))⟩)⟩)))⟩
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
  exact ⟨x, (⟨x1, ((let H14 := bet_neq12_neq x1 H8; (let H15 := bet_neq12_neq H3 H0; (let H16 := cong_diff_3_c b4 x b3 b4 H8 x2; conga_right_comm_c b0 b1 b2 x b4 b5 (l11_13_c A' b1 b2 b3 b4 b5 b0 x (conga_sym_c b3 b4 b5 A' b1 b2 (conga_right_comm_c b3 b4 b5 b2 b1 A' H6)) (between_symmetry H3) H0 x1 (Ne.symm H16))))))⟩)⟩)))⟩
theorem conga2_suppa_suppa_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), CongA A B C A' B' C' → CongA D E F D' E' F' → SuppA A B C D E F → SuppA A' B' C' D' E' F' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  have H2 : SuppA b0 b1 b2 b9 b10 b11 := (by
  obtain ⟨H2, H3⟩ := b14
  exact ⟨H2, ((by
  obtain ⟨A0, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨A0, (⟨H5, (conga_trans_c b9 b10 b11 b3 b4 b5 b2 b1 A0 (conga_sym_c b3 b4 b5 b9 b10 b11 b13) H6)⟩)⟩))⟩)
  exact suppa_sym_c b9 b10 b11 b6 b7 b8 ((let H3 := suppa_sym_c b0 b1 b2 b9 b10 b11 H2; (by
  obtain ⟨H4, H5⟩ := H3
  exact ⟨H4, ((by
  obtain ⟨D0, H6⟩ := H5
  obtain ⟨H7, H8⟩ := H6
  exact ⟨D0, (⟨H7, (conga_trans_c b6 b7 b8 b0 b1 b2 b11 b10 D0 (conga_sym_c b0 b1 b2 b6 b7 b8 b12) H8)⟩)⟩))⟩)))
theorem suppa2_conga456_c :
    ∀ (A B C D E F D' E' F' : Tpoint), SuppA A B C D E F → SuppA A B C D' E' F' → CongA D E F D' E' F' := sorry

theorem suppa2_conga123_c :
    ∀ (A B C D E F A' B' C' : Tpoint), SuppA A B C D E F → SuppA A' B' C' D E F → CongA A B C A' B' C' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 =>
  suppa2_conga456_c b3 b4 b5 b0 b1 b2 b6 b7 b8 (suppa_sym_c b0 b1 b2 b3 b4 b5 b9) (suppa_sym_c b6 b7 b8 b3 b4 b5 b10)
theorem bet_out_suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → Bet A B C → Out E D F → SuppA A B C D E F :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
  ⟨b6, (⟨b2, (⟨b8, (l11_21_b_c b3 b4 b5 b2 b1 b2 b9 (out_trivial (Ne.symm b7)))⟩)⟩)⟩
theorem bet_suppa_out_c :
    ∀ (A B C D E F : Tpoint), Bet A B C → SuppA A B C D E F → Out E D F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have Hd := b7
  have Hd0 := suppa_distincts_c b0 b1 b2 b3 b4 b5 Hd
  obtain ⟨H1, H2⟩ := Hd0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact l11_21_a_c b2 b1 b2 b3 b4 b5 (out_trivial (Ne.symm H3)) (suppa2_conga456_c b0 b1 b2 b2 b1 b2 b3 b4 b5 (⟨H1, (⟨b2, (⟨b6, (conga_refl_c b2 b1 b2 (Ne.symm H3) (Ne.symm H3))⟩)⟩)⟩) b7)
theorem out_suppa_bet_c :
    ∀ (A B C D E F : Tpoint), Out B A C → SuppA A B C D E F → Bet D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have e := segment_construction b0 b1 b0 b1
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  exact bet_conga_bet_c b0 b1 x b3 b4 b5 x1 (suppa2_conga456_c b0 b1 b2 b0 b1 x b3 b4 b5 ((let H4 := out_distinct_c b1 b0 b2 b6; (let H5 := H4; (by
  obtain ⟨H6, _⟩ := H5
  have H7 := bet_neq12_neq x1 H6
  have H8 := cong_diff_3_c b1 x b0 b1 H6 x2
  exact suppa_sym_c b0 b1 x b0 b1 b2 (bet_out_suppa_c b0 b1 x b0 b1 b2 H6 H8 x1 b6))))) b7)
theorem per_suppa_per_c :
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
theorem per2_suppa_c :
    ∀ (A B C D E F : Tpoint), A ≠ B → B ≠ C → D ≠ E → E ≠ F → Per A B C → Per D E F → SuppA A B C D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have e := ex_suppa_c b0 b1 b2 b6 b7
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  exact conga2_suppa_suppa_c b0 b1 b2 x x1 x3 b0 b1 b2 b3 b4 b5 (conga_refl_c b0 b1 b2 b6 (Ne.symm b7)) ((let Hd := x4; (let Hd0 := suppa_distincts_c b0 b1 b2 x x1 x3 Hd; (by
  obtain ⟨_, H8⟩ := Hd0
  obtain ⟨_, H9⟩ := H8
  obtain ⟨H10, H11⟩ := H9
  exact l11_16_c x x1 x3 b3 b4 b5 (per_suppa_per_c b0 b1 b2 x x1 x3 b10 x4) H10 (Ne.symm H11) b11 b8 (Ne.symm b9))))) x4
theorem suppa_per_c :
    ∀ (A B C : Tpoint), SuppA A B C A B C → Per A B C := by
  intro b0 b1 b2 b3
  obtain ⟨_, H0⟩ := b3
  obtain ⟨A', H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  exact l8_2_c b2 b1 b0 (l11_18_2_c b2 b1 b0 A' H2 (conga_left_comm_c b0 b1 b2 b2 b1 A' H3))
theorem acute_suppa_obtuse_c :
    ∀ (A B C D E F : Tpoint), Acute A B C → SuppA A B C D E F → Obtuse D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact conga_obtuse_obtuse_c b2 b1 A' b3 b4 b5 ((let H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  exact obtuse_sym_c A' b1 b2 (acute_bet_obtuse_c b0 b1 b2 A' H3 H9 b6)))) (conga_sym_c b3 b4 b5 b2 b1 A' H4)
theorem obtuse_suppa_acute_c :
    ∀ (A B C D E F : Tpoint), Obtuse A B C → SuppA A B C D E F → Acute D E F := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨A', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  exact acute_conga_acute_c b2 b1 A' b3 b4 b5 ((let H5 := conga_distinct_c b3 b4 b5 b2 b1 A' H4; (by
  obtain ⟨_, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  exact acute_sym_c A' b1 b2 (bet_obtuse_acute_c b0 b1 b2 A' H3 H9 b6)))) (conga_sym_c b3 b4 b5 b2 b1 A' H4)
theorem lea_suppa2_lea_c :
    ∀ (A B C D E F A' B' C' D' E' F' : Tpoint), SuppA A B C A' B' C' → SuppA D E F D' E' F' → LeA A B C D E F → LeA D' E' F' A' B' C' := sorry

theorem lta_suppa2_lta_c :
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
  exact lta_comm_c D0 b4 b5 A0 b1 b2 (bet2_lta_lta_c b0 b1 b2 b3 b4 b5 A0 D0 b14 H5 H19 H8 H15)))))
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
      · exact Or.inl (conga2_suppa_suppa_c b0 b1 b2 x x1 x3 b0 b1 b2 b3 b4 b5 (conga_refl_c b0 b1 b2 H (Ne.symm H0)) H4 x4)
      · exact Or.inr ((fun H5 => H4 (suppa2_conga456_c b0 b1 b2 x x1 x3 b3 b4 b5 x4 H5)))
theorem acute_one_side_aux_c :
    ∀ (P A O B : Tpoint), OS O A P B → Acute A O P → Perp O A B O → OS O B A P := sorry

theorem acute_one_side_aux0_c :
    ∀ (P A O B : Tpoint), Col A O P → Acute A O P → Perp O A B O → OS O B A P := sorry

theorem acute_cop_perp_one_side_c :
    ∀ (P A O B : Tpoint), Acute A O P → Perp O A B O → Coplanar A B O P → OS O B A P := sorry

theorem acute_not_obtuse_c :
    ∀ (A B C : Tpoint), Acute A B C → ¬ Obtuse A B C := sorry

#print axioms GeocoqTranslate.Tarski.Base.l11_3_c
#print axioms GeocoqTranslate.Tarski.Base.l11_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_3_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_4_1_c
#print axioms GeocoqTranslate.Tarski.Base.l11_4_2_c
#print axioms GeocoqTranslate.Tarski.Base.conga_refl_c
#print axioms GeocoqTranslate.Tarski.Base.conga_sym_c
#print axioms GeocoqTranslate.Tarski.Base.l11_10_c
#print axioms GeocoqTranslate.Tarski.Base.out2_conga_c
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
#print axioms GeocoqTranslate.Tarski.Base.conga_cop_or_out_ts_c
#print axioms GeocoqTranslate.Tarski.Base.conga_os_out_c
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
#print axioms GeocoqTranslate.Tarski.Base.out321_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.inangle1123_c
#print axioms GeocoqTranslate.Tarski.Base.out341_inangle_c
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
#print axioms GeocoqTranslate.Tarski.Base.bet_conga_bet_c
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
#print axioms GeocoqTranslate.Tarski.Base.conga_lea_c
#print axioms GeocoqTranslate.Tarski.Base.conga_lea456123_c
#print axioms GeocoqTranslate.Tarski.Base.lea_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lta_comm_c
#print axioms GeocoqTranslate.Tarski.Base.lea_out4_lea_c
#print axioms GeocoqTranslate.Tarski.Base.lea121345_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_lea_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_lea_1_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_lta_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_trans_c
#print axioms GeocoqTranslate.Tarski.Base.lea_trans_c
#print axioms GeocoqTranslate.Tarski.Base.in_angle_asym_c
#print axioms GeocoqTranslate.Tarski.Base.lea_asym_c
#print axioms GeocoqTranslate.Tarski.Base.col_lta_bet_c
#print axioms GeocoqTranslate.Tarski.Base.col_lta_out_c
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
#print axioms GeocoqTranslate.Tarski.Base.acute_col_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_obtuse_bet_c
#print axioms GeocoqTranslate.Tarski.Base.out_acute_c
#print axioms GeocoqTranslate.Tarski.Base.bet_obtuse_c
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
#print axioms GeocoqTranslate.Tarski.Base.lta_lea_c
#print axioms GeocoqTranslate.Tarski.Base.nlta_c
#print axioms GeocoqTranslate.Tarski.Base.lea_nlta_c
#print axioms GeocoqTranslate.Tarski.Base.lta_nlea_c
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
#print axioms GeocoqTranslate.Tarski.Base.cong2_conga_obtuse_cong_conga2_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2_cong_conga2_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2_cong_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_per2_cong_3_c
#print axioms GeocoqTranslate.Tarski.Base.cong_lt_per2_lt_c
#print axioms GeocoqTranslate.Tarski.Base.cong_le_per2_le_c
#print axioms GeocoqTranslate.Tarski.Base.lt2_per2_lt_c
#print axioms GeocoqTranslate.Tarski.Base.le_lt_per2_lt_c
#print axioms GeocoqTranslate.Tarski.Base.le2_per2_le_c
#print axioms GeocoqTranslate.Tarski.Base.cong_lt_per2_lt_1_c
#print axioms GeocoqTranslate.Tarski.Base.symmetry_preserves_conga_c
#print axioms GeocoqTranslate.Tarski.Base.l11_57_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_orth_at_orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.col2_orth_at_orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.col_orth_at_orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_chara_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_orth_orth_c
#print axioms GeocoqTranslate.Tarski.Base.col2_orth_orth_c
#print axioms GeocoqTranslate.Tarski.Base.col_orth_orth_c
#print axioms GeocoqTranslate.Tarski.Base.orth_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.orth_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop_orth_orth_at_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_c
#print axioms GeocoqTranslate.Tarski.Base.l11_60_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_61_c
#print axioms GeocoqTranslate.Tarski.Base.l11_61_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_unicity_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_unicity_bis_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at2_eq_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop_orth_at_eq_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_ncop_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l11_62_existence_bis_c
#print axioms GeocoqTranslate.Tarski.Base.l11_63_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l11_63_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_3_c
#print axioms GeocoqTranslate.Tarski.Base.mid2_orth_at2_cong_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at2_tsp_ts_c
#print axioms GeocoqTranslate.Tarski.Base.orth_dec_c
#print axioms GeocoqTranslate.Tarski.Base.orth_at_dec_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.osp_dec_c
#print axioms GeocoqTranslate.Tarski.Base.ts2_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.os_ts_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.os2_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.acute_conga_acute_c
#print axioms GeocoqTranslate.Tarski.Base.acute_out2_acute_c
#print axioms GeocoqTranslate.Tarski.Base.conga_obtuse_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_out2_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.bet_lea_bet_c
#print axioms GeocoqTranslate.Tarski.Base.out_lea_out_c
#print axioms GeocoqTranslate.Tarski.Base.bet2_lta_lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea123456_lta_lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea456789_lta_lta_c
#print axioms GeocoqTranslate.Tarski.Base.acute_per_lta_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_per_lta_c
#print axioms GeocoqTranslate.Tarski.Base.acute_obtuse_lta_c
#print axioms GeocoqTranslate.Tarski.Base.lea_in_angle_c
#print axioms GeocoqTranslate.Tarski.Base.acute_bet_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.bet_obtuse_acute_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lea_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lta_dec_c
#print axioms GeocoqTranslate.Tarski.Base.lea_total_c
#print axioms GeocoqTranslate.Tarski.Base.or_lta2_conga_c
#print axioms GeocoqTranslate.Tarski.Base.angle_partition_c
#print axioms GeocoqTranslate.Tarski.Base.acute_chara_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_chara_c
#print axioms GeocoqTranslate.Tarski.Base.conga_acute_c
#print axioms GeocoqTranslate.Tarski.Base.cong_acute_c
#print axioms GeocoqTranslate.Tarski.Base.nlta_lea_c
#print axioms GeocoqTranslate.Tarski.Base.nlea_lta_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_inequality_2_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_inequality_2_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_strict_reverse_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.triangle_reverse_inequality_c
#print axioms GeocoqTranslate.Tarski.Base.os3_lta_c
#print axioms GeocoqTranslate.Tarski.Base.bet_le_lt_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_ncol_c
#print axioms GeocoqTranslate.Tarski.Base.cong4_cop2_eq_c
#print axioms GeocoqTranslate.Tarski.Base.t18_18_aux_c
#print axioms GeocoqTranslate.Tarski.Base.t18_18_c
#print axioms GeocoqTranslate.Tarski.Base.t18_19_c
#print axioms GeocoqTranslate.Tarski.Base.acute_trivial_c
#print axioms GeocoqTranslate.Tarski.Base.acute_not_per_c
#print axioms GeocoqTranslate.Tarski.Base.angle_bisector_c
#print axioms GeocoqTranslate.Tarski.Base.reflectl_conga_c
#print axioms GeocoqTranslate.Tarski.Base.conga_cop_out_reflectl_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_conga_cop_reflectl_col_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_cop2_col_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_cop2_col_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_conga_conga_c
#print axioms GeocoqTranslate.Tarski.Base.cop_inangle_ex_col_inangle_c
#print axioms GeocoqTranslate.Tarski.Base.col_inangle2_out_c
#print axioms GeocoqTranslate.Tarski.Base.inangle2_lea_c
#print axioms GeocoqTranslate.Tarski.Base.conga_inangle_per_acute_c
#print axioms GeocoqTranslate.Tarski.Base.conga_inangle2_per_acute_c
#print axioms GeocoqTranslate.Tarski.Base.lta_os_ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.ex_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_right_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_left_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_comm_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_sym_c
#print axioms GeocoqTranslate.Tarski.Base.conga2_suppa_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa2_conga456_c
#print axioms GeocoqTranslate.Tarski.Base.suppa2_conga123_c
#print axioms GeocoqTranslate.Tarski.Base.bet_out_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.bet_suppa_out_c
#print axioms GeocoqTranslate.Tarski.Base.out_suppa_bet_c
#print axioms GeocoqTranslate.Tarski.Base.per_suppa_per_c
#print axioms GeocoqTranslate.Tarski.Base.per2_suppa_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_per_c
#print axioms GeocoqTranslate.Tarski.Base.acute_suppa_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.obtuse_suppa_acute_c
#print axioms GeocoqTranslate.Tarski.Base.lea_suppa2_lea_c
#print axioms GeocoqTranslate.Tarski.Base.lta_suppa2_lta_c
#print axioms GeocoqTranslate.Tarski.Base.suppa_dec_c
#print axioms GeocoqTranslate.Tarski.Base.acute_one_side_aux_c
#print axioms GeocoqTranslate.Tarski.Base.acute_one_side_aux0_c
#print axioms GeocoqTranslate.Tarski.Base.acute_cop_perp_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.acute_not_obtuse_c
end GeocoqTranslate.Tarski.Base
