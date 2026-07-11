import GeocoqTranslate.Tarski_dev.Ch15b

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

theorem grid_exchange_axes_c :
    ∀ (O E S U1 U2 : Tpoint), Cs O E S U1 U2 → Cs O E S U2 U1 := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨x, x0⟩ := b5
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  exact ⟨x, (⟨x3, (⟨x1, (l8_2_c b3 b2 b4 x4)⟩)⟩)⟩
theorem Cs_not_Col_c :
    ∀ (O E S U1 U2 : Tpoint), Cs O E S U1 U2 → ¬ Col U1 S U2 := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H, H0⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  have H5 := cong_diff H H3
  have H6 := cong_diff H H1
  have H7 := per_distinct_c b3 b2 b4 H4 (swap_diff_c b2 b3 H6)
  exact per_not_col_c b3 b2 b4 (Ne.symm H6) H5 H4
theorem exists_grid_c :
    ∃ (O E E' S U1 U2 : Tpoint), ¬ Col O E E' ∧ Cs O E S U1 U2 := by
  have e := lower_dim_ex
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  have H1 := x4
  have H2 := not_col_distincts_c x x1 x3 H1
  have H3 := H2
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, _⟩ := H6
  have e0 := ex_per_cong_c x1 x x x3 x x1 (Ne.symm H5) H5 ((by colr)) (not_col_permutation_5_c x1 x3 x (not_col_permutation_1_c x x1 x3 H1))
  obtain ⟨x5, x6⟩ := e0
  obtain ⟨H7, H8⟩ := x6
  obtain ⟨H9, _⟩ := H8
  exact ⟨x, (⟨x1, (⟨x3, (⟨x, (⟨x1, (⟨x5, (⟨H1, (⟨H5, (⟨(le_anti_symmetry_c x x1 x x1 (le_reflexivity_c x x1) (le_reflexivity_c x x1)), (⟨(cong_3421_c x5 x x x1 H9), (l8_2_c x5 x x1 H7)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem exists_grid_spec_c :
    ∃ (S U1 U2 : Tpoint), Cs PA PB S U1 U2 := by
  have H := lower_dim
  have H0 := not_col_distincts_c PA PB PC H
  have H1 := H0
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  have e := ex_per_cong_c PB PA PA PC PA PB (Ne.symm H3) H3 ((by colr)) (not_col_permutation_5_c PB PC PA (not_col_permutation_1_c PA PB PC H))
  obtain ⟨x, x0⟩ := e
  obtain ⟨H5, H6⟩ := x0
  obtain ⟨H7, _⟩ := H6
  exact ⟨PA, (⟨PB, (⟨x, (⟨H3, (⟨(le_anti_symmetry_c PA PB PA PB (le_reflexivity_c PA PB) (le_reflexivity_c PA PB)), (⟨(cong_3421_c x PA PA PB H7), (l8_2_c x PA PB H5)⟩)⟩)⟩)⟩)⟩)⟩
theorem coord_exchange_axes_c :
    ∀ (O E S U1 U2 P X Y : Tpoint), Cd O E S U1 U2 P X Y → Cd O E S U2 U1 P Y X := sorry

theorem Cd_Col_c :
    ∀ (O E S U1 U2 P X Y : Tpoint), Cd O E S U1 U2 P X Y → Col O E X ∧ Col O E Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  obtain ⟨x, x0⟩ := b8
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  exact ((by
  obtain ⟨x5, x6⟩ := x3
  exact fun H2 => (by
  obtain ⟨x7, x8⟩ := H2
  obtain ⟨x9, x10⟩ := x6
  exact ((by
  obtain ⟨x11, x12⟩ := x9
  exact fun HCong1 => (by
  obtain ⟨x13, x14⟩ := x8
  exact ((by
  obtain ⟨x15, x16⟩ := x13
  exact fun HCong2 => ⟨(l4_13_c b2 b3 x5 b0 b1 b6 ((by
  rcases x12 with H5 | H5
  · obtain ⟨H6, _⟩ := H5
    exact H6
  · obtain ⟨H6, H7⟩ := H5
    subst H7
    exact H6)) (cong_3_sym_c b0 b1 b6 b2 b3 x5 HCong1)), (l4_13_c b2 b4 x7 b0 b1 b7 ((by
  rcases x16 with H5 | H5
  · obtain ⟨H6, _⟩ := H5
    exact H6
  · obtain ⟨H6, H7⟩ := H5
    subst H7
    exact H6)) (cong_3_sym_c b0 b1 b7 b2 b4 x7 HCong2))⟩)) x14))) x10))) x4
theorem exists_projp_c :
    ∀ (A B P : Tpoint), A ≠ B → ∃ (P' : Tpoint), Projp P P' A B := by
  intro b0 b1 b2 b3
  rcases (col_dec_c b0 b1 b2) with HNC | HNC
  · exact ⟨b2, (⟨b3, (Or.inr (⟨HNC, rfl⟩))⟩)⟩
  · have e := l8_18_existence_c b0 b1 b2 HNC
    obtain ⟨x, x0⟩ := e
    exact ⟨x, (⟨b3, (Or.inl x0)⟩)⟩
theorem exists_coord_c :
    ∀ (O E S U P : Tpoint), S ≠ U → Cong O E S U → ∃ (PX : Tpoint), ∃ (X : Tpoint), Projp P PX S U ∧ Cong_3 O E X S U PX := by
  intro b0 b1 b2 b3 b4 b5 b6
  have e := exists_projp_c b2 b3 b4 b5
  obtain ⟨x, x0⟩ := e
  have HCol := (by
  obtain ⟨x1, x2⟩ := x0
  rcases x2 with H0 | H0
  · obtain ⟨H1, _⟩ := H0
    exact H1
  · obtain ⟨H1, H2⟩ := H0
    subst H2
    exact H1)
  have e0 := l4_14_c b2 b3 x b0 b1 HCol ((by cong_r))
  obtain ⟨x1, x2⟩ := e0
  exact ⟨x, (⟨x1, (⟨x0, (cong_3_sym_c b2 b3 x b0 b1 x1 x2)⟩)⟩)⟩
theorem coordinates_of_point_c :
    ∀ (O E S U1 U2 P : Tpoint), Cs O E S U1 U2 → ∃ (X : Tpoint), ∃ (Y : Tpoint), Cd O E S U1 U2 P X Y := sorry

theorem point_of_coordinates_origin_c :
    ∀ (O E S U1 U2 : Tpoint), Cs O E S U1 U2 → Cd O E S U1 U2 S O O := sorry

theorem point_of_coordinates_on_an_axis_c :
    ∀ (O E S U1 U2 X : Tpoint), Cs O E S U1 U2 → Col O E X → O ≠ X → ∃ (P : Tpoint), Cd O E S U1 U2 P X O := sorry

theorem point_of_coordinates_c :
    ∀ (O E S U1 U2 X Y : Tpoint), Cs O E S U1 U2 → Col O E X → Col O E Y → ∃ (P : Tpoint), Cd O E S U1 U2 P X Y := sorry

theorem eq_points_coordinates_c :
    ∀ (O E S U1 U2 P1 X1 Y1 P2 X2 Y2 : Tpoint), Cd O E S U1 U2 P1 X1 Y1 → Cd O E S U1 U2 P2 X2 Y2 → (P1 = P2 ↔ (X1 = X2 ∧ Y1 = Y2)) := sorry

theorem l16_9_1_c :
    ∀ (O E E' X Y XY XMY : Tpoint), Col O E X → Col O E Y → Is_length O E E' X Y XY → LeP O E E' Y X → Diff O E E' X Y XMY → XY = XMY := sorry

theorem length_eq_or_opp_c :
    ∀ (O E E' A B L1 L2 : Tpoint), Length O E E' A B L1 → Diff O E E' A B L2 → L1 = L2 ∨ Opp O E E' L1 L2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have HNC := (let HL3 := diff_ar2_c b0 b1 b2 b3 b4 b6 b8; (by
  obtain ⟨H, H0⟩ := HL3
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, _⟩ := H1
  exact H))
  have HColA := (let HL3 := diff_ar2_c b0 b1 b2 b3 b4 b6 b8; (by
  obtain ⟨_, H0⟩ := HL3
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, _⟩ := H2
  exact H1))
  have HColB := (let HL3 := diff_ar2_c b0 b1 b2 b3 b4 b6 b8; (by
  obtain ⟨_, H0⟩ := HL3
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, _⟩ := H1
  exact H2))
  rcases (col_2_le_or_ge_c b0 b1 b2 b3 b4 HNC HColA HColB) with HLe | HLe
  · exact Or.inr (diff_opp_c b0 b1 b2 b4 b3 b5 b6 ((let e := diff_exists_c b0 b1 b2 b4 b3 HNC HColB HColA; (by
  obtain ⟨x, x0⟩ := e
  have H := l16_9_1_c b0 b1 b2 b4 b3 b5 x HColB HColA (Or.inl (length_sym_c b0 b1 b2 b3 b4 b5 b7)) HLe x0
  subst H
  exact x0))) b8)
  · exact Or.inl (l16_9_1_c b0 b1 b2 b3 b4 b5 b6 HColA HColB (Or.inl b7) HLe b8)
theorem l16_9_2_c :
    ∀ (O E E' X Y XY XMY XY2 XMY2 : Tpoint), Col O E X → Col O E Y → Is_length O E E' X Y XY → Diff O E E' X Y XMY → Prod O E E' XY XY XY2 → Prod O E E' XMY XMY XMY2 → XY2 = XMY2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  have HNC := (let HXMY0 := diff_ar2_c b0 b1 b2 b3 b4 b6 b12; (by
  obtain ⟨H, H0⟩ := HXMY0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, _⟩ := H1
  exact H))
  have H := b11
  rcases H with HXY' | HXY'
  · rcases (length_eq_or_opp_c b0 b1 b2 b3 b4 b5 b6 HXY' b12) with HOpp1 | HOpp1
    · subst HOpp1
      exact prod_uniqueness_c b5 b5 b7 b8 b13 b14
    · exact prod_uniqueness_c b5 b5 b7 b8 b13 ((let e := opp_exists_c b1 ((by colr)); (by
  obtain ⟨x, x0⟩ := e
  exact prod_assoc1_c b1 b2 b6 x b5 b5 b6 b8 (opp_prod_c b0 b1 b2 x b6 b5 x0 (opp_comm_c b5 b6 HOpp1)) (prod_comm_c b0 b1 b2 b5 x b6 (opp_prod_c b0 b1 b2 x b5 b6 x0 HOpp1)) b14)))
  · obtain ⟨H0, _⟩ := HXY'
    have H1 := not_col_distincts_c b0 b1 b2 HNC
    have H2 := H1
    obtain ⟨_, H3⟩ := H2
    obtain ⟨H4, H5⟩ := H3
    obtain ⟨_, _⟩ := H5
    have H6 := H4 H0
    exact (H6).elim
theorem cong_3_2_cong_4_c :
    ∀ (O E I J S U X Y : Tpoint), O ≠ E → Col O E I → Col O E J → Cong_3 O E I S U X → Cong_3 O E J S U Y → Cong_4 O E I J S U X Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  obtain ⟨x, x0⟩ := b11
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := b12
  obtain ⟨x5, x6⟩ := x4
  exact ⟨x3, (⟨x1, (⟨x5, (⟨x2, (⟨x6, (l4_16 (⟨b9, (⟨(⟨x3, (⟨x1, x2⟩)⟩), (⟨x5, x6⟩)⟩)⟩) b8)⟩)⟩)⟩)⟩)⟩
theorem cong_3_3_cong_5_c :
    ∀ (O E I J K S U X Y Z : Tpoint), O ≠ E → Col O E I → Col O E J → Col O E K → Cong_3 O E I S U X → Cong_3 O E J S U Y → Cong_3 O E K S U Z → Cong_5 O E I J K S U X Y Z := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  obtain ⟨x, x0⟩ := b14
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := b15
  obtain ⟨x5, x6⟩ := x4
  obtain ⟨x7, x8⟩ := b16
  obtain ⟨x9, x10⟩ := x8
  exact ⟨x7, (⟨x1, (⟨x5, (⟨x9, (⟨x2, (⟨x6, (⟨x10, (⟨(l4_16 (⟨b11, (⟨(⟨x7, (⟨x1, x2⟩)⟩), (⟨x5, x6⟩)⟩)⟩) b10), (⟨(l4_16 (⟨b11, (⟨(⟨x7, (⟨x1, x2⟩)⟩), (⟨x9, x10⟩)⟩)⟩) b10), (l4_16 (⟨b12, (⟨(⟨x7, (⟨x5, x6⟩)⟩), (⟨x9, x10⟩)⟩)⟩) b10)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem square_distance_formula_aux_c :
    ∀ (O E E' S U1 U2 P PX PY Q QX PXQX : Tpoint), Cd O E S U1 U2 P PX PY → Cd O E S U1 U2 Q QX PY → P ≠ Q → ¬ Col O E E' → Col O E PX → Col O E QX → Col O E PY → Cs O E S U1 U2 → Length O E E' PX QX PXQX → Length O E E' Q P PXQX := sorry

theorem square_distance_formula_c :
    ∀ (O E E' S U1 U2 P Q PX PY QX QY PQ PQ2 PXMQX PYMQY PXMQX2 PYMQY2 F : Tpoint), Cd O E S U1 U2 P PX PY → Cd O E S U1 U2 Q QX QY → Is_length O E E' P Q PQ → Prod O E E' PQ PQ PQ2 → Diff O E E' PX QX PXMQX → Prod O E E' PXMQX PXMQX PXMQX2 → Diff O E E' PY QY PYMQY → Prod O E E' PYMQY PYMQY PYMQY2 → Sum O E E' PXMQX2 PYMQY2 F → PQ2 = F := sorry

theorem characterization_of_congruence_c :
    ∀ (O E E' S U1 U2 A AX AY B BX BY C CX CY D DX DY AXMBX AXMBX2 AYMBY AYMBY2 AB2 CXMDX CXMDX2 CYMDY CYMDY2 CD2 : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → Cd O E S U1 U2 D DX DY → Diff O E E' AX BX AXMBX → Prod O E E' AXMBX AXMBX AXMBX2 → Diff O E E' AY BY AYMBY → Prod O E E' AYMBY AYMBY AYMBY2 → Sum O E E' AXMBX2 AYMBY2 AB2 → Diff O E E' CX DX CXMDX → Prod O E E' CXMDX CXMDX CXMDX2 → Diff O E E' CY DY CYMDY → Prod O E E' CYMDY CYMDY CYMDY2 → Sum O E E' CXMDX2 CYMDY2 CD2 → (Cong A B C D ↔ AB2 = CD2) := sorry

theorem bet_betCood_aux_c :
    ∀ (O E S U1 U2 A AX AY B BX BY C CX CY : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → Bet A B C → Bet AX BX CX := sorry

theorem bet_betCood_c :
    ∀ (O E S U1 U2 A AX AY B BX BY C CX CY : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → Bet A B C → Bet AX BX CX ∧ Bet AY BY CY :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 =>
  ⟨(bet_betCood_aux_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17), (bet_betCood_aux_c b0 b1 b2 b4 b3 b5 b7 b6 b8 b10 b9 b11 b13 b12 (coord_exchange_axes_c b0 b1 b2 b3 b4 b5 b6 b7 b14) (coord_exchange_axes_c b0 b1 b2 b3 b4 b8 b9 b10 b15) (coord_exchange_axes_c b0 b1 b2 b3 b4 b11 b12 b13 b16) b17)⟩
theorem characterization_of_betweenness_aux_c :
    ∀ (O E E' S U1 U2 A AX AY B BX BY C CX CY BXMAX CXMAX AB AC IAC T : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → ¬ Col O E E' → Col O E AX → Col O E BX → Col O E CX → Col O E BXMAX → Col O E CXMAX → Col O E T → Col O E AB → Col O E AC → Col O E IAC → Diff O E E' BX AX BXMAX → Diff O E E' CX AX CXMAX → Length O E E' A B AB → Length O E E' A C AC → Prod O E E' T AC AB → Prod O E E' IAC AC E → Bet A B C → A ≠ B → A ≠ C → B ≠ C → Prod O E E' T CXMAX BXMAX := sorry

theorem characterization_of_betweenness_c :
    ∀ (O E E' S U1 U2 A AX AY B BX BY C CX CY BXMAX BYMAY CXMAX CYMAY : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → Diff O E E' BX AX BXMAX → Diff O E E' BY AY BYMAY → Diff O E E' CX AX CXMAX → Diff O E E' CY AY CYMAY → (Bet A B C ↔ ∃ (T : Tpoint), O ≠ E ∧ Col O E T ∧ LeP O E E' O T ∧ LeP O E E' T E ∧ Prod O E E' T CXMAX BXMAX ∧ Prod O E E' T CYMAY BYMAY) := sorry

theorem same_abscissa_col_c :
    ∀ (O E S U1 U2 A AX AY B BY C CY : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B AX BY → Cd O E S U1 U2 C AX CY → Col A B C := sorry

theorem characterization_of_collinearity_c :
    ∀ (O E E' S U1 U2 A AX AY B BX BY C CX CY AXMBX AYMBY BXMCX BYMCY XProd YProd : Tpoint), Cd O E S U1 U2 A AX AY → Cd O E S U1 U2 B BX BY → Cd O E S U1 U2 C CX CY → Diff O E E' AX BX AXMBX → Diff O E E' AY BY AYMBY → Diff O E E' BX CX BXMCX → Diff O E E' BY CY BYMCY → Prod O E E' AXMBX BYMCY XProd → Prod O E E' AYMBY BXMCX YProd → (Col A B C ↔ XProd = YProd) := sorry

#print axioms GeocoqTranslate.Tarski.Base.grid_exchange_axes_c
#print axioms GeocoqTranslate.Tarski.Base.Cs_not_Col_c
#print axioms GeocoqTranslate.Tarski.Base.exists_grid_c
#print axioms GeocoqTranslate.Tarski.Base.exists_grid_spec_c
#print axioms GeocoqTranslate.Tarski.Base.coord_exchange_axes_c
#print axioms GeocoqTranslate.Tarski.Base.Cd_Col_c
#print axioms GeocoqTranslate.Tarski.Base.exists_projp_c
#print axioms GeocoqTranslate.Tarski.Base.exists_coord_c
#print axioms GeocoqTranslate.Tarski.Base.coordinates_of_point_c
#print axioms GeocoqTranslate.Tarski.Base.point_of_coordinates_origin_c
#print axioms GeocoqTranslate.Tarski.Base.point_of_coordinates_on_an_axis_c
#print axioms GeocoqTranslate.Tarski.Base.point_of_coordinates_c
#print axioms GeocoqTranslate.Tarski.Base.eq_points_coordinates_c
#print axioms GeocoqTranslate.Tarski.Base.l16_9_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_eq_or_opp_c
#print axioms GeocoqTranslate.Tarski.Base.l16_9_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_2_cong_4_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_3_cong_5_c
#print axioms GeocoqTranslate.Tarski.Base.square_distance_formula_aux_c
#print axioms GeocoqTranslate.Tarski.Base.square_distance_formula_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_congruence_c
#print axioms GeocoqTranslate.Tarski.Base.bet_betCood_aux_c
#print axioms GeocoqTranslate.Tarski.Base.bet_betCood_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_betweenness_aux_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_betweenness_c
#print axioms GeocoqTranslate.Tarski.Base.same_abscissa_col_c
#print axioms GeocoqTranslate.Tarski.Base.characterization_of_collinearity_c
end GeocoqTranslate.Tarski.Base