import GeocoqTranslate.Tarski_dev.CoplanarPermExtra

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem cop_cong_on_bissect_c :
    ∀ (A B M P X : Tpoint), Coplanar A B X P → Midpoint M A B → Perp_at M A B P M → Cong X A X B → Col M P X := by
  intro A B M P X H H0 H1 H2
  have H3 := (let H3 := perp_in_distinct_c M A B P M H1; (let H4 := H3; (by
  obtain ⟨H5, _⟩ := H4
  have H6 := midpoint_distinct_1_c M A B H5 H0
  have H7 := H6
  obtain ⟨_, _⟩ := H7
  exact cong_perp_or_mid_c A B M X H5 H0 ((by cong_r)))))
  rcases H3 with H4 | H4
  · subst H4
    exact col_trivial_3_c X P
  · obtain ⟨_, H5⟩ := H4
    have H6 := perp_in_perp_c A B P M M H1
    have H7 := perp_in_perp_c X M A B M H5
    have H8 := midpoint_col_c A M B H0
    exact cop_perp2_col_c M P X A B ((let H9 := perp_coplanar_c X M A B H7; (let H10 := perp_coplanar_c A B P M H6; coplanar_perm_1_c A B X P H))) (perp_comm_c P M B A (perp_comm_c M P A B (perp_left_comm_c P M A B (perp_sym_c A B P M H6)))) (perp_comm_c X M B A (perp_comm_c M X A B (perp_comm_c X M B A (perp_right_comm_c X M A B H7))))

theorem cong_cop_mid_perp_col_c :
    ∀ (A B M P X : Tpoint), Coplanar A B X P → Cong A X B X → Midpoint M A B → Perp A B P M → Col M P X := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have hCol := midpoint_col_c b0 b2 b1 b7
  exact cop_cong_on_bissect_c b0 b1 b2 b3 b4 b5 b7 (l8_15_1_c b0 b1 b3 b2 ((by colr)) b8) ((by cong_r))

theorem cop_image_in2_col_c :
    ∀ (A B P P' Q Q' M : Tpoint), Coplanar A B P Q → ReflectL_at M P P' A B → ReflectL_at M Q Q' A B → Col M P Q := sorry

theorem l10_10_spec_c :
    ∀ (A B P Q P' Q' : Tpoint), ReflectL P' P A B → ReflectL Q' Q A B → Cong P Q P' Q' := by
  intro A B P Q P' Q' hRP hRQ
  rcases eq_dec_points_c A B with hAB | hAB
  · subst B
    have hPP' : P' = P := image_spec_eq_c A P' P hRP
    have hQQ' : Q' = Q := image_spec_eq_c A Q' Q hRQ
    subst hPP'; subst hQQ'
    exact cong_reflexivity_c P' Q'
  · have hHH0 := hRP
    have hHH1 := hRQ
    obtain ⟨⟨X, hMidXPP', hColABX⟩, hOrP⟩ := hRP
    obtain ⟨⟨Y, hMidYQQ', hColABY⟩, hOrQ⟩ := hRQ
    obtain ⟨Z, hMidZXY⟩ := midpoint_existence_c X Y
    have hColABZ : Col A B Z := by
      rcases eq_dec_points_c X Y with hXY | hXY
      · subst hXY
        have hZX : Z = X := l7_3_c Z X hMidZXY
        subst hZX
        exact hColABX
      · have hColXZY : Col X Z Y := bet_col_c X Z Y (midpoint_bet_c X Z Y hMidZXY)
        colr
    obtain ⟨R, hMidZPR⟩ := symmetric_point_construction_c P Z
    obtain ⟨R', hMidZP'R'⟩ := symmetric_point_construction_c P' Z
    rcases hOrP with hPerpP | hEqP
    · rcases hOrQ with hPerpQ | hEqQ
      · -- LEAF 1: both P,P' and Q,Q' are genuine (non-degenerate) reflections
        have hReflPP' : Reflect P P' A B :=
          l10_4_c A B P' P ((is_image_is_image_spec_c P P' A B hAB).mpr hHH0)
        have hReflRR' : Reflect R R' A B :=
          midpoint_preserves_image_c A B P P' R R' Z hAB hColABZ hReflPP' hMidZPR hMidZP'R'
        have hReflLRR' : ReflectL R R' A B :=
          (is_image_is_image_spec_c R' R A B hAB).mp hReflRR'
        have hRneR' : R ≠ R' := by
          intro heq
          have hMidZP'R : Midpoint Z P' R := heq ▸ hMidZP'R'
          have hPP' : P' = P := l7_9_c P' P Z R hMidZP'R hMidZPR
          rw [hPP'] at hPerpP
          exact (perp_distinct_c A B P P hPerpP).2 rfl
        have hMidYRR' : Midpoint Y R R' :=
          symmetry_preserves_midpoint_c P X P' R Y R' Z hMidZPR hMidZXY hMidZP'R' hMidXPP'
        have hCongQ'R'QR : Cong Q' R' Q R := l7_13_c Y Q' R' Q R hMidYQQ' hMidYRR'
        have hCongP'ZPZ : Cong P' Z P Z := is_image_spec_col_cong_c A B P' P Z hHH0 hColABZ
        have hCongQ'ZQZ : Cong Q' Z Q Z := is_image_spec_col_cong_c A B Q' Q Z hHH1 hColABZ
        have hCongRZPZ : Cong R Z P Z :=
          cong_right_commutativity_c R Z Z P (cong_4321_c P Z Z R (midpoint_cong_c P Z R hMidZPR))
        have hCongR'ZP'Z : Cong R' Z P' Z :=
          cong_right_commutativity_c R' Z Z P' (cong_4321_c P' Z Z R' (midpoint_cong_c P' Z R' hMidZP'R'))
        have hArg1step : Cong R Z P' Z :=
          cong_transitivity_c R Z P Z P' Z hCongRZPZ (cong_symmetry_c P' Z P Z hCongP'ZPZ)
        have hArg1 : Cong R Z R' Z :=
          cong_transitivity_c R Z P' Z R' Z hArg1step (cong_symmetry_c R' Z P' Z hCongR'ZP'Z)
        have hArg2 : Cong Z P Z P' := cong_4321_c P' Z P Z hCongP'ZPZ
        have hArg3 : Cong R Q R' Q' := cong_4321_c Q' R' Q R hCongQ'R'QR
        have hArg4 : Cong Z Q Z Q' := cong_4321_c Q' Z Q Z hCongQ'ZQZ
        have hArg5 : Bet R Z P := between_symmetry_c P Z R (midpoint_bet_c P Z R hMidZPR)
        have hArg6 : Bet R' Z P' := between_symmetry_c P' Z R' (midpoint_bet_c P' Z R' hMidZP'R')
        have hArg7 : R ≠ Z := by
          intro heq
          have h1 : Cong P Z Z Z := heq ▸ hMidZPR.2
          have hPZ : P = Z := cong_identity P Z Z h1
          have h2 : Cong P' Z Z Z := hPZ ▸ hCongP'ZPZ
          have hP'Z : P' = Z := cong_identity P' Z Z h2
          have h3 : Cong P' Z Z R' := hMidZP'R'.2
          have h4 : Cong Z Z Z R' := hP'Z ▸ h3
          have h5 : Cong Z R' Z Z := cong_symmetry_c Z Z Z R' h4
          have hZR' : Z = R' := cong_identity Z R' Z h5
          exact hRneR' (heq.trans hZR')
        exact five_segment R R' Z Z P P' Q Q' hArg1 hArg2 hArg3 hArg4 hArg5 hArg6 hArg7
      · -- LEAF 2: Q = Q' (degenerate on the Q side)
        have hYQ : Y = Q := by
          have h := hMidYQQ'
          rw [← hEqQ] at h
          exact l7_3_c Y Q h
        have hCongFinal : Cong P Q P' Q' := by
          rw [← hEqQ, ← hYQ]
          exact is_image_spec_col_cong_c A B P P' Y (l10_4_spec_c A B P' P hHH0) hColABY
        exact hCongFinal
    · -- LEAF 3: P = P' (degenerate on the P side)
      have hXP : X = P := by
        have h := hMidXPP'
        rw [← hEqP] at h
        exact l7_3_c X P h
      have hColABP : Col A B P := by rw [← hXP]; exact hColABX
      have hCongQPQ'P : Cong Q P Q' P :=
        is_image_spec_col_cong_c A B Q Q' P (l10_4_spec_c A B Q' Q hHH1) hColABP
      have hCongFinal : Cong P Q P' Q' := by
        rw [← hEqP]
        exact cong_commutativity_c Q P Q' P hCongQPQ'P
      exact hCongFinal

theorem l10_10_c :
    ∀ (A B P Q P' Q' : Tpoint), Reflect P' P A B → Reflect Q' Q A B → Cong P Q P' Q' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have o := point_equality_decidability b0 b1
  rcases o with H1 | H1
  · have H1' := H1.symm
    subst H1'
    rcases b6 with H4 | H4
    · obtain ⟨H5, _⟩ := H4
      rcases b7 with H6 | H6
      · obtain ⟨H7, _⟩ := H6
        have H8 := (let H8 := rfl; H5 H8)
        have H10 := (let H10 := rfl; H7 H10)
        exact (H8).elim
      · obtain ⟨H7, _⟩ := H6
        have H8 := H5 H7
        exact (H8).elim
    · rcases b7 with H5 | H5
      · obtain ⟨H6, _⟩ := H5
        obtain ⟨H7, _⟩ := H4
        have H8 := H6 H7
        exact (H8).elim
      · obtain ⟨_, H6⟩ := H4
        obtain ⟨_, H7⟩ := H5
        exact l7_13_c b1 b2 b3 b4 b5 (l7_2_c b1 b2 b4 H6) (l7_2_c b1 b3 b5 H7)
  · exact l10_10_spec_c b0 b1 b2 b3 b4 b5
      ((is_image_is_image_spec_c b2 b4 b0 b1 H1).1 b6)
      ((is_image_is_image_spec_c b3 b5 b0 b1 H1).1 b7)

theorem image_preserves_bet_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Bet A B C → Bet A' B' C' := by
  intro A B C A' B' C' X Y H H0 H1 H2
  have o := point_equality_decidability X Y
  rcases o with x | x
  · subst x
    have H7 := image_spec_eq_c X A A' H
    have H8 := image_spec_eq_c X B B' H0
    have H9 := image_spec_eq_c X C C' H1
    subst H9
    subst H8
    subst H7
    exact H2
  · exact l4_6 H2 (⟨(l10_10_spec_c X Y A B A' B' (l10_4_spec_c X Y A A' H) (l10_4_spec_c X Y B B' H0)), (⟨(l10_10_spec_c X Y A C A' C' (l10_4_spec_c X Y A A' H) (l10_4_spec_c X Y C C' H1)), (l10_10_spec_c X Y B C B' C' (l10_4_spec_c X Y B B' H0) (l10_4_spec_c X Y C C' H1))⟩)⟩)

theorem image_gen_preserves_bet_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Bet A B C → Bet A' B' C' := sorry

theorem image_preserves_col_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Col A B C → Col A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  rcases b11 with x | x
  · exact bet_col_c b3 b4 b5 (image_preserves_bet_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 x)
  · rcases x with x0 | x0
    · have hBet := image_preserves_bet_c b1 b2 b0 b4 b5 b3 b6 b7 b9 b10 b8 x0
      have hCol := bet_col_c b4 b5 b3 hBet
      exact (by colr)
    · have hBet := image_preserves_bet_c b2 b0 b1 b5 b3 b4 b6 b7 b10 b8 b9 x0
      have hCol := bet_col_c b5 b3 b4 hBet
      exact (by colr)

theorem image_gen_preserves_col_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Col A B C → Col A' B' C' := sorry

theorem image_gen_preserves_ncol_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → ¬ Col A B C → ¬ Col A' B' C' := by
  intro A B C A' B' C' X Y H H0 H1 H2
  exact (fun H3 => H2 (image_gen_preserves_col_c A' B' C' A B C X Y (l10_4_c X Y A A' H) (l10_4_c X Y B B' H0) (l10_4_c X Y C C' H1) H3))

theorem image_gen_preserves_inter_c :
    ∀ (A B C D I A' B' C' D' I' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Reflect D D' X Y → ¬ Col A B C → C ≠ D → Col A B I → Col C D I → Col A' B' I' → Col C' D' I' → Reflect I I' X Y := by
  intro A B C D I A' B' C' D' I' X Y H H0 H1 H2 H3 H4 H5 H6 H7 H8
  have e := l10_6_existence_c X Y I
  obtain ⟨x, x0⟩ := e
  have H9 := l6_21_c A' B' C' D' I' x (image_gen_preserves_ncol_c A B C A' B' C' X Y H H0 H1 H3) ((fun H9 => (by
  subst H9
  exact H4 (l10_2_uniqueness_c X Y C' C D H1 H2)))) H7 (image_gen_preserves_col_c A B I A' B' x X Y H H0 x0 H5) H8 (image_gen_preserves_col_c C D I C' D' x X Y H1 H2 x0 H6)
  subst H9
  exact x0

theorem intersection_with_image_gen_c :
    ∀ (A B C A' B' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → ¬ Col A B A' → Col A B C → Col A' B' C → Col C X Y := by
  intro A B C A' B' X Y H H0 H1 H2 H3
  exact l10_8_c X Y C ((let H4 := l10_4_c X Y A A' H; (let H5 := image_gen_preserves_ncol_c A B A' A' B' A X Y H H0 H4 H1; (let H6 := not_col_distincts_c A' B' A H5; (let H7 := H6; (by
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, _⟩ := H10
  have H11 := not_col_distincts_c A B A' H1
  have H12 := H11
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, _⟩ := H14
  exact image_gen_preserves_inter_c A B A' B' C A' B' A B C X Y H H0 H4 (l10_4_c X Y B B' H0) H1 H9 H2 H3 H3 H2))))))

theorem image_preserves_midpoint_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Midpoint A B C → Midpoint A' B' C' := by
  intro A B C A' B' C' X Y hRA hRB hRC hMid
  refine ⟨?_, ?_⟩
  · exact image_preserves_bet_c B A C B' A' C' X Y hRB hRA hRC hMid.1
  · have hOuter : Cong B' A' B A := l10_10_spec_c X Y B' A' B A hRB hRA
    have hInner : Cong A C A' C' :=
      l10_10_spec_c X Y A C A' C' (l10_4_spec_c X Y A A' hRA) (l10_4_spec_c X Y C C' hRC)
    have hStep : Cong B A A' C' := cong_transitivity_c B A A C A' C' hMid.2 hInner
    exact cong_transitivity_c B' A' B A A' C' hOuter hStep

theorem image_spec_preserves_per_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Per A B C → Per A' B' C' := by
  intro A B C A' B' C' X Y hRA hRB hRC hPer
  rcases eq_dec_points_c X Y with hXY | hXY
  · subst Y
    have hAA' : A = A' := image_spec_eq_c X A A' hRA
    have hBB' : B = B' := image_spec_eq_c X B B' hRB
    have hCC' : C = C' := image_spec_eq_c X C C' hRC
    rw [← hAA', ← hBB', ← hCC']
    exact hPer
  · obtain ⟨C1, hMidBCC1⟩ := symmetric_point_construction_c C B
    obtain ⟨C1', hRC1⟩ := l10_6_existence_spec_c X Y C1
    refine ⟨C1', image_preserves_midpoint_c B C C1 B' C' C1' X Y hRB hRC hRC1 hMidBCC1, ?_⟩
    obtain ⟨C2, hMidBCC2, hCongACAC2⟩ := hPer
    have hC2C1 : C2 = C1 := symmetric_point_uniqueness_c C B C2 C1 hMidBCC2 hMidBCC1
    rw [hC2C1] at hCongACAC2
    have hOuter : Cong A' C' A C := l10_10_spec_c X Y A' C' A C hRA hRC
    have hInner : Cong A C1 A' C1' :=
      l10_10_spec_c X Y A C1 A' C1' (l10_4_spec_c X Y A A' hRA) (l10_4_spec_c X Y C1 C1' hRC1)
    have hStep : Cong A C A' C1' := cong_transitivity_c A C A C1 A' C1' hCongACAC2 hInner
    exact cong_transitivity_c A' C' A C A' C1' hOuter hStep

theorem image_preserves_per_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Per A B C → Per A' B' C' := by
  intro A B C A' B' C' X Y H H0 H1 H2
  have o := point_equality_decidability X Y
  rcases o with H3 | H3
  · rcases H with H4 | H4
    · rcases H0 with H5 | H5
      · rcases H1 with H6 | H6
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
        · obtain ⟨_, _⟩ := H6
          obtain ⟨H7, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
      · rcases H1 with H6 | H6
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
        · obtain ⟨_, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨H7, _⟩ := H4
          exact ((H7 H3)).elim
    · rcases H0 with H5 | H5
      · rcases H1 with H6 | H6
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
        · obtain ⟨_, _⟩ := H6
          obtain ⟨H7, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
      · rcases H1 with H6 | H6
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H7 H3)).elim
        · obtain ⟨H7, H8⟩ := H6
          obtain ⟨H9, H10⟩ := H5
          obtain ⟨H11, H12⟩ := H4
          subst H11
          exact midpoint_preserves_per_c A B C A' B' C' X H2 (l7_2_c X A' A H12) (l7_2_c X B' B H10) (l7_2_c X C' C H8)
  · rcases H with H4 | H4
    · rcases H0 with H5 | H5
      · rcases H1 with H6 | H6
        · obtain ⟨_, H7⟩ := H6
          obtain ⟨_, H8⟩ := H5
          obtain ⟨_, H9⟩ := H4
          exact image_spec_preserves_per_c A B C A' B' C' X Y H9 H8 H7 H2
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim
      · rcases H1 with H6 | H6
        · obtain ⟨_, _⟩ := H6
          obtain ⟨H7, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim
    · rcases H0 with H5 | H5
      · rcases H1 with H6 | H6
        · obtain ⟨_, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨H7, _⟩ := H4
          exact ((H3 H7)).elim
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim
      · rcases H1 with H6 | H6
        · obtain ⟨_, _⟩ := H6
          obtain ⟨H7, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim
        · obtain ⟨H7, _⟩ := H6
          obtain ⟨_, _⟩ := H5
          obtain ⟨_, _⟩ := H4
          exact ((H3 H7)).elim

theorem l10_12_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Cong B C B' C' → Cong A C A' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have o := point_equality_decidability b1 b2
  rcases o with H3 | H3
  · subst H3
    have H5 : Cong b4 b5 b1 b1 := (by cong_r)
    have H6 := cong_identity b4 b5 b1 H5
    subst H6
    exact b8
  · have o0 := point_equality_decidability b0 b1
    rcases o0 with H4 | H4
    · subst H4
      have H7 : Cong b3 b4 b0 b0 := (by cong_r)
      have H8 := cong_identity b3 b4 b0 H7
      subst H8
      exact b9
    · have H5 := midpoint_existence_c b1 b4
      obtain ⟨X, H6⟩ := H5
      have mp := symmetric_point_construction_c b3 X
      obtain ⟨A1, H7⟩ := mp
      have mp0 := symmetric_point_construction_c b5 X
      obtain ⟨C1, H8⟩ := mp0
      have H9 : Cong_3 b3 b4 b5 A1 b1 C1 := ⟨(l7_13_c X b3 b4 A1 b1 (l7_2_c X b3 A1 H7) H6), (⟨(l7_13_c X b3 b5 A1 C1 (l7_2_c X b3 A1 H7) (l7_2_c X b5 C1 H8)), (l7_13_c X b4 b5 b1 C1 H6 (l7_2_c X b5 C1 H8))⟩)⟩
      have H10 := l8_10_c b3 b4 b5 A1 b1 C1 b7 H9
      obtain ⟨H11, H12⟩ := H9
      obtain ⟨H13, H14⟩ := H12
      have H15 : Cong b0 b1 A1 b1 := (by cong_r)
      have H16 : Cong b1 b2 b1 C1 := (by cong_r)
      have H17 := midpoint_existence_c b2 C1
      obtain ⟨Y, H18⟩ := H17
      have H19 := cong_midpoint_image_c b1 Y b2 C1 H16 H18
      have H20 := l10_6_existence_c b1 Y A1
      obtain ⟨A2, H21⟩ := H20
      have H22 := l10_10_c b1 Y b2 A2 C1 A1 H19 H21
      have H23 := image_triv_c b1 Y
      have H24 := image_preserves_per_c A1 b1 C1 A2 b1 b2 b1 Y H21 H23 H19 H10
      have H25aux := l10_10_c b1 Y A2 b1 A1 b1 H21 H23
      have H25 : Cong b0 b1 A2 b1 := (by cong_r)
      have H26 := midpoint_existence_c b0 A2
      obtain ⟨Z, H27⟩ := H26
      have H28aux : Cong b1 b0 b1 A2 := (by cong_r)
      have H28 := cong_midpoint_image_c b1 Z b0 A2 H28aux H27
      have He29 := symmetric_point_construction_c b2 b1
      obtain ⟨C0, H29⟩ := He29
      have H30 := per_double_cong_c b0 b1 b2 C0 b6 H29
      have H31 := per_double_cong_c A2 b1 b2 C0 H24 H29
      have H33cong : Cong Z b2 Z C0 := by
        rcases point_equality_decidability b0 A2 with He | He
        · have H27' : Midpoint Z b0 b0 := by rw [← He] at H27; exact H27
          have hZ := l7_3_c Z b0 H27'
          subst hZ
          exact H30
        · have hMcol := midpoint_col_c b0 Z A2 H27
          have hCol : Col b0 A2 Z := (by colr)
          exact l4_17_c b0 A2 Z b2 C0 He hCol H30 H31
      have H32 := is_image_rev_c C0 b2 Z b1 (cong_midpoint_image_c Z b1 b2 C0 H33cong H29)
      have H33 := l10_10_c b1 Z b0 b2 A2 C0 H28 H32
      have HFinal : Cong b0 b2 b3 b5 := by cong_r
      exact HFinal
theorem l10_16_c :
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → Cong A B A' B' → ∃ (C' : Tpoint), Cong_3 A B C A' B' C' ∧ OS A' B' P C' := sorry

theorem cong_cop_image_col_c :
    ∀ (A B P P' X : Tpoint), P ≠ P' → Reflect P P' A B → Cong P X P' X → Coplanar A B P X → Col A B X := sorry

theorem cong_cop_per2_1_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ Midpoint B X Y := sorry

theorem cong_cop_per2_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ ReflectL X Y A B := sorry

theorem cong_cop_per2_gen_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ Reflect X Y A B := sorry

theorem ex_perp_cop_c :
    ∀ (A B C P : Tpoint), A ≠ B → ∃ (Q : Tpoint), Perp A B Q C ∧ Coplanar A B P Q := by
  intro b0 b1 b2 b3 b4
  have o := col_dec_c b0 b1 b2
  rcases o with x | x
  · have o0 := col_dec_c b0 b1 b3
    rcases o0 with x0 | x0
    · have e := not_col_exists_c b0 b1 b4
      obtain ⟨x1, x2⟩ := e
      have e0 := l10_15_c b0 b1 b2 x1 x x2
      obtain ⟨x3, x4⟩ := e0
      obtain ⟨x5, x6⟩ := x4
      exact ⟨x3, (⟨x5, (⟨b3, (Or.inl (⟨x0, (col_trivial_3_c b3 x3)⟩))⟩)⟩)⟩
    · have e := l10_15_c b0 b1 b2 b3 x x0
      obtain ⟨x1, x2⟩ := e
      obtain ⟨x3, x4⟩ := x2
      exact ⟨x1, (⟨x3, (os_coplanar_c b0 b1 b3 x1 x4)⟩)⟩
  · have e := l8_18_existence_c b0 b1 b2 x
    obtain ⟨x0, x1⟩ := e
    obtain ⟨x2, x3⟩ := x1
    exact ⟨x0, (⟨(perp_comm_c b1 b0 b2 x0 (perp_comm_c b0 b1 x0 b2 (perp_comm_c b1 b0 b2 x0 (perp_left_comm_c b0 b1 b2 x0 x3)))), (⟨x0, (Or.inl (⟨x2, (col_trivial_2_c b3 x0)⟩))⟩)⟩)⟩
theorem hilbert_s_version_of_pasch_aux_c :
    ∀ (A B C I P : Tpoint), Coplanar A B C P → ¬ Col A I P → ¬ Col B C P → Bet B I C → B ≠ I → I ≠ C → B ≠ C → ∃ (X : Tpoint), Col I P X ∧ ((Bet A X B ∧ A ≠ X ∧ X ≠ B ∧ A ≠ B) ∨ (Bet A X C ∧ A ≠ X ∧ X ≠ C ∧ A ≠ C)) := sorry

theorem hilbert_s_version_of_pasch_c :
    ∀ (A B C P Q : Tpoint), Coplanar A B C P → ¬ Col C Q P → ¬ Col A B P → BetS A Q B → ∃ (X : Tpoint), Col P Q X ∧ (BetS A X C ∨ BetS B X C) := sorry

theorem two_sides_cases_c :
    ∀ (O P A B : Tpoint), ¬ Col O A B → OS O P A B → TS O A P B ∨ TS O B P A := by
  intro O P A B H H0
  have H1 := cop_one_or_two_sides_c O A P B ((let H1 := os_coplanar_c O P A B H0; coplanar_perm_2_c O P A B H1)) ((by
  obtain ⟨R, H1⟩ := H0
  obtain ⟨H2, _⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, _⟩ := H4
  exact not_col_permutation_5_c P A O (not_col_permutation_2_c A O P H3))) (not_col_permutation_5_c B A O (not_col_permutation_3_c O A B H))
  rcases H1 with H2 | H2
  · exact Or.inl H2
  · exact Or.inr (l9_31_c O P B A (one_side_symmetry_c O P A B H0) (one_side_symmetry_c O A P B H2))

theorem not_par_two_sides_c :
    ∀ (A B C D I : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ∃ (X : Tpoint), ∃ (Y : Tpoint), Col C D X ∧ Col C D Y ∧ TS A B X Y := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have HX : ∃ X, Col b2 b3 X ∧ b4 ≠ X :=
    ⟨b2, col_trivial_3_c b2 b3, fun H => by subst H; exact b8 b6⟩
  obtain ⟨x, x1, x2⟩ := HX
  have e := symmetric_point_construction_c x b4
  obtain ⟨x3, x4⟩ := e
  have H11 := midpoint_col_c x b4 x3 x4
  have hColx3 : Col b2 b3 x3 := by colr
  have H8 := midpoint_distinct_2_c b4 x x3 x2 x4
  obtain ⟨H9, H10⟩ := H8
  have notColX : ¬ Col x b0 b1 := by
    intro H12
    exact x2 (l6_21_c b0 b1 b2 b3 b4 x b8 b5 b6 (by colr) b7 x1)
  have notColX3 : ¬ Col x3 b0 b1 := by
    intro H12
    exact H10 (l6_21_c b0 b1 b2 b3 b4 x3 b8 b5 b6 (by colr) b7 hColx3)
  exact ⟨x, x3, x1, hColx3, notColX, notColX3, b4, (by colr), x4.1⟩

theorem cop_not_par_other_side_c :
    ∀ (A B C D I P : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ¬ Col A B P → Coplanar A B C P → ∃ (Q : Tpoint), Col C D Q ∧ TS A B P Q := sorry

theorem cop_not_par_same_side_c :
    ∀ (A B C D I P : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ¬ Col A B P → Coplanar A B C P → ∃ (Q : Tpoint), Col C D Q ∧ OS A B P Q := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have e := not_par_two_sides_c b0 b1 b2 b3 b4 b6 b7 b8 b9
  obtain ⟨x, x0⟩ := e
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  have H2 := coplanar_trans_1_c b2 b0 b1 b5 x (not_col_permutation_5_c b2 b1 b0 (not_col_permutation_3_c b0 b1 b2 b9)) ((let H2 := ts_coplanar_c b0 b1 x x1 x6; coplanar_perm_12_c b0 b1 b2 b5 b11)) (⟨b4, (Or.inr (Or.inr (⟨(by colr), b7⟩)))⟩)
  rcases (one_side_dec_c b0 b1 b5 x) with HTS2 | HTS2
  · exact ⟨x, (⟨x3, HTS2⟩)⟩
  · have H3 := not_col_distincts_c b0 b1 b5 b10
    have H4 := H3
    obtain ⟨_, H5⟩ := H4
    obtain ⟨_, H6⟩ := H5
    obtain ⟨_, _⟩ := H6
    have H7 := not_col_distincts_c b0 b1 b2 b9
    have H8 := H7
    obtain ⟨_, H9⟩ := H8
    obtain ⟨_, H10⟩ := H9
    obtain ⟨_, _⟩ := H10
    have HTS3 := cop_nos_ts_c b0 b1 b5 x H2 (not_col_permutation_5_c b5 b1 b0 (not_col_permutation_3_c b0 b1 b5 b10)) ((fun H11 => (by
  obtain ⟨H12, H13⟩ := x6
  obtain ⟨_, _⟩ := H13
  have H14 := H12 H11
  exact (H14).elim))) HTS2
    exact ⟨x1, (⟨x5, (⟨x, (⟨HTS3, (invert_two_sides_c b1 b0 x1 x (invert_two_sides_c b0 b1 x1 x (l9_2_c b0 b1 x x1 x6)))⟩)⟩)⟩)⟩
theorem all_coplanar_c :
    ∀ (A B C D : Tpoint), Coplanar A B C D := sorry

theorem per2_col_c :
    ∀ (A B C X : Tpoint), Per A X C → X ≠ C → Per B X C → Col A B X := sorry

theorem perp2_col_c :
    ∀ (X Y Z A B : Tpoint), Perp X Y A B → Perp X Z A B → Col X Y Z :=
  fun b0 b1 b2 b3 b4 => cop_perp2_col_c b0 b1 b2 b3 b4 (all_coplanar_c b3 b4 b1 b2)

#print axioms GeocoqTranslate.Tarski.Base.cop_cong_on_bissect_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_mid_perp_col_c
#print axioms GeocoqTranslate.Tarski.Base.cop_image_in2_col_c
#print axioms GeocoqTranslate.Tarski.Base.l10_10_spec_c
#print axioms GeocoqTranslate.Tarski.Base.l10_10_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.image_gen_preserves_bet_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.image_gen_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.image_gen_preserves_ncol_c
#print axioms GeocoqTranslate.Tarski.Base.image_gen_preserves_inter_c
#print axioms GeocoqTranslate.Tarski.Base.intersection_with_image_gen_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_midpoint_c
#print axioms GeocoqTranslate.Tarski.Base.image_spec_preserves_per_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_per_c
#print axioms GeocoqTranslate.Tarski.Base.l10_12_c
#print axioms GeocoqTranslate.Tarski.Base.l10_16_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_image_col_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_per2_1_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_per2_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_per2_gen_c
#print axioms GeocoqTranslate.Tarski.Base.ex_perp_cop_c
#print axioms GeocoqTranslate.Tarski.Base.hilbert_s_version_of_pasch_aux_c
#print axioms GeocoqTranslate.Tarski.Base.hilbert_s_version_of_pasch_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_cases_c
#print axioms GeocoqTranslate.Tarski.Base.not_par_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.cop_not_par_other_side_c
#print axioms GeocoqTranslate.Tarski.Base.cop_not_par_same_side_c
#print axioms GeocoqTranslate.Tarski.Base.all_coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.per2_col_c
#print axioms GeocoqTranslate.Tarski.Base.perp2_col_c
end GeocoqTranslate.Tarski.Base
