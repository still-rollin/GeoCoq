import GeocoqTranslate.Tarski_dev.Ch08

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem col__coplanar_c (A B C D : Tpoint) (H : Col A B C) : Coplanar A B C D :=
  ⟨C, (Or.inl (⟨H, (col_trivial_3_c C D)⟩))⟩

theorem ncop__ncol_c (A B C D : Tpoint) (H : ¬ Coplanar A B C D) : ¬ Col A B C :=
  (fun H0 => H (col__coplanar_c A B C D H0))

theorem ts__coplanar_c (A B C D : Tpoint) (H : TS A B C D) : Coplanar A B C D := by
  obtain ⟨x, x0⟩ := H
  obtain ⟨x1, x2⟩ := x0
  obtain ⟨x3, x4⟩ := x2
  obtain ⟨x5, x6⟩ := x4
  exact ⟨x3, (Or.inl (⟨(col_permutation_5_c A x3 B (col_permutation_4_c x3 A B x5)), (col_permutation_5_c C x3 D (bet_col_c C x3 D x6))⟩))⟩

theorem perp__coplanar_c (A B C D : Tpoint) (H : Perp A B C D) : Coplanar A B C D := by
  obtain ⟨x, x0⟩ := H
  obtain ⟨_, H0⟩ := x0
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, _⟩ := H3
  exact ⟨x, (Or.inl (⟨(col_permutation_1_c x A B H2), (col_permutation_1_c x C D H4)⟩))⟩

theorem coplanar_perm_1_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar A B D C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨H1, (col_permutation_5_c D x C (col_permutation_1_c C D x H2))⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H2, H3⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H2, H3⟩))))⟩

theorem coplanar_perm_2_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar A C B D := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨H1, H2⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H2, H3⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H2, (col_permutation_4_c B C x H3)⟩))))⟩

theorem coplanar_perm_4_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar A D B C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨H1, (col_permutation_4_c C D x H2)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H2, (col_permutation_4_c B D x H3)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H2, H3⟩)))⟩

theorem coplanar_perm_6_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B A C D := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨(col_permutation_5_c B x A (col_permutation_1_c A B x H1)), H2⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H3, H2⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H3, H2⟩))))⟩

theorem coplanar_perm_8_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B C A D := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨(col_permutation_4_c A B x H1), H2⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H3, (col_permutation_4_c A C x H2)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H3, H2⟩)))⟩

theorem coplanar_perm_9_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B C D A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨(col_permutation_4_c A B x H1), H2⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H3, (col_permutation_4_c A C x H2)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H3, (col_permutation_5_c D x A (col_permutation_1_c A D x H2))⟩)))⟩

theorem coplanar_perm_12_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C A B D := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨H2, H1⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c C x A (col_permutation_1_c A C x H2)), H3⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c B C x H3), H2⟩))))⟩

theorem coplanar_perm_16_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C D A B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨H2, H1⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c A C x H2), (col_permutation_4_c B D x H3)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c B C x H3), (col_permutation_4_c A D x H2)⟩))))⟩

theorem coplanar_perm_17_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C D B A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨H2, (col_permutation_5_c B x A (col_permutation_1_c A B x H1))⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c A C x H2), (col_permutation_4_c B D x H3)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c B C x H3), (col_permutation_4_c A D x H2)⟩))))⟩

theorem coplanar_perm_18_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D A B C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨(col_permutation_4_c C D x H2), H1⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c B D x H3), H2⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c D x A (col_permutation_1_c A D x H2)), H3⟩)))⟩

theorem coplanar_perm_19_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D A C B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨(col_permutation_4_c C D x H2), H1⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c B D x H3), H2⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c D x A (col_permutation_1_c A D x H2)), (col_permutation_5_c C x B (col_permutation_1_c B C x H3))⟩)))⟩

theorem coplanar_perm_21_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D B C A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨(col_permutation_4_c C D x H2), (col_permutation_4_c A B x H1)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c D x B (col_permutation_1_c B D x H3)), (col_permutation_5_c C x A (col_permutation_1_c A C x H2))⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c A D x H2), H3⟩))))⟩

theorem ts_distincts_c (A B P Q : Tpoint) (h : TS A B P Q) :
    A ≠ B ∧ A ≠ P ∧ A ≠ Q ∧ B ≠ P ∧ B ≠ Q ∧ P ≠ Q := by
  obtain ⟨hnc1, hnc2, T, hColT, hBet⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; apply hnc1; rw [e]; exact col_trivial_2_c _ _
  · intro e; apply hnc1; rw [← e]; exact col_trivial_1_c _ _
  · intro e; apply hnc2; rw [← e]; exact col_trivial_1_c _ _
  · intro e; apply hnc1; rw [← e]; exact col_trivial_3_c _ _
  · intro e; apply hnc2; rw [← e]; exact col_trivial_3_c _ _
  · intro e
    rw [← e] at hBet
    have hPT := between_identity P T hBet
    apply hnc1
    rw [hPT]
    exact hColT

theorem l9_2_c (A B P Q : Tpoint) (h : TS A B P Q) : TS A B Q P := by
  obtain ⟨hPnCol, hQnCol, T, hTCol, hBet⟩ := h
  refine ⟨hQnCol, hPnCol, T, hTCol, ?_⟩
  exact between_symmetry_c P T Q hBet

theorem mid_preserves_col_c (A B C M A' B' C' : Tpoint)
    (hCol : Col A B C) (h₁ : Midpoint M A A')
    (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') : Col A' B' C' := by
  rcases hCol with H3 | H3
  · have H4 := l7_15_c A B C A' B' C' M h₁ h₂ h₃ H3
    exact bet_col_c A' B' C' H4
  · rcases H3 with H4 | H4
    · have H5 := l7_15_c B C A B' C' A' M h₂ h₃ h₁ H4
      exact col_permutation_2_c B' C' A' (bet_col_c B' C' A' H5)
    · have H5 := l7_15_c C A B C' A' B' M h₃ h₁ h₂ H4
      exact col_permutation_1_c C' A' B' (bet_col_c C' A' B' H5)

theorem per_mid_per_c (A B X Y M : Tpoint)
    (hAB : A ≠ B) (h₁ : Per X A B)
    (h₂ : Midpoint M A B) (h₃ : Midpoint M X Y) :
    Cong A X B Y ∧ Per Y B A := by
  have hCg1 : Cong A X B Y := l7_13_c M A X B Y (l7_2_c M A B h₂) (l7_2_c M X Y h₃)
  obtain ⟨B', hMidAB', hCgXB⟩ := h₁
  obtain ⟨hBetBAB', hCgBAAB'⟩ := hMidAB'
  obtain ⟨A', hMidBA'⟩ := symmetric_point_construction_c A B
  obtain ⟨hBetABA', hCgABBA'⟩ := hMidBA'
  have hCg2 : Cong B X A Y := l7_13_c M B X A Y h₂ (l7_2_c M X Y h₃)
  have hCgAB'BA' : Cong A B' B A' :=
    cong_transitivity_c A B' B A B A'
      (cong_symmetry_c B A A B' hCgBAAB')
      (cong_left_commutativity_c A B B A' hCgABBA')
  have hOFSC : OFSC B A B' X A B A' Y :=
    ⟨hBetBAB', hBetABA', cong_pseudo_reflexivity B A, hCgAB'BA', hCg2, hCg1⟩
  have hCgB'XA'Y : Cong B' X A' Y :=
    five_segment_with_def_c B A B' X A B A' Y hOFSC (Ne.symm hAB)
  have c1 : Cong Y A X B :=
    cong_commutativity_c A Y B X (cong_symmetry_c B X A Y hCg2)
  have c2 : Cong Y A X B' := cong_transitivity_c Y A X B X B' c1 hCgXB
  have c3 : Cong X B' A' Y :=
    cong_transitivity_c X B' B' X A' Y (cong_pseudo_reflexivity X B') hCgB'XA'Y
  have c4 : Cong Y A A' Y := cong_transitivity_c Y A X B' A' Y c2 c3
  exact ⟨hCg1, A', ⟨hBetABA', hCgABBA'⟩, cong_right_commutativity_c Y A A' Y c4⟩

theorem sym_preserve_diff_c (A B M A' B' : Tpoint)
    (hAB : A ≠ B) (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') :
    A' ≠ B' := by
  intro H2
  subst H2
  have H4 := l7_9_c A B M A' h₁ h₂
  exact ((hAB H4)).elim

theorem l9_4_1_aux_c (P Q A C R S M : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := by
  rcases eq_dec_points_c R S with hRS | hRS
  · subst hRS
    have hMR : M = R := l7_3_c M R hMid
    subst hMR
    obtain ⟨hNColAPQ, hNColCPQ, T, hColTPQ, hBetATC⟩ := h₁
    have hTM : T = M := by
      rcases eq_dec_points_c M T with hMT | hMT
      · exact hMT.symm
      · have hPerpMTAM : Perp M T A M :=
          perp_col2_c P Q M T A M hPerpA hMT
            (col_permutation_1_c M P Q hR) (col_permutation_1_c T P Q hColTPQ)
        have hPerpMTCM : Perp M T C M :=
          perp_col2_c P Q M T C M hPerpC hMT
            (col_permutation_1_c M P Q hR) (col_permutation_1_c T P Q hColTPQ)
        have hPerTMA : Per T M A :=
          perp_in_per_c T M A
            (perp_in_comm_c M T A M M (perp_perp_in_c M T A hPerpMTAM))
        have hPerTMC : Per T M C :=
          perp_in_per_c T M C
            (perp_in_comm_c M T C M M (perp_perp_in_c M T C hPerpMTCM))
        exact (l8_6_c A M T C (l8_2_c T M A hPerTMA) (l8_2_c T M C hPerTMC) hBetATC).symm
    rw [hTM] at hBetATC
    intro U C' hMidUC'
    constructor
    · intro hOutUA
      obtain ⟨hUM, hAM, hOrUA⟩ := hOutUA
      have hCM : C ≠ M := (perp_distinct_c P Q C M hPerpC).2
      have hC'M : C' ≠ M := by
        intro hC'M
        exact hUM (symmetric_point_uniqueness_c M M U M
          (l7_2_c M U M (hC'M ▸ hMidUC')) (l7_3_2_c M))
      have hBetUMC : Bet U M C := by
        rcases hOrUA with hc | hc
        · exact between_exchange3_c A U M C (between_symmetry_c M U A hc) hBetATC
        · exact outer_transitivity_between2_c U A M C (between_symmetry_c M A U hc) hBetATC hAM
      exact ⟨hCM, hC'M, l5_2_c U M C C' hUM hBetUMC hMidUC'.1⟩
    · intro hOutCC'
      obtain ⟨hCM, hC'M, hOrCC'⟩ := hOutCC'
      have hUM : U ≠ M := by
        intro hUM
        exact hC'M (is_midpoint_id_c M C' (hUM ▸ hMidUC')).symm
      have hAM : A ≠ M := (perp_distinct_c P Q A M hPerpA).2
      have hBetAMC' : Bet A M C' := by
        rcases hOrCC' with hc | hc
        · exact outer_transitivity_between_c A M C C' hBetATC hc (Ne.symm hCM)
        · exact between_inner_transitivity_c A M C' C hBetATC hc
      exact ⟨hUM, hAM,
        l5_2_c C' M U A hC'M (between_symmetry_c U M C' hMidUC'.1)
          (between_symmetry_c A M C' hBetAMC')⟩
  · obtain ⟨D, hBetRDA, hCongSCRD⟩ := hLe
    have hCS : C ≠ S := fun h => (perp_distinct_c P Q C S hPerpC).2 h
    have hRD : R ≠ D := by
      intro h
      subst h
      exact hCS (cong_identity S C R hCongSCRD).symm
    obtain ⟨hNColAPQ, hNColCPQ, T, hColTPQ, hBetATC⟩ := h₁
    have hPQ : P ≠ Q := by
      intro h; subst h; exact hNColAPQ (col_trivial_2_c A P)
    have hh1 : Perp C S S R :=
      perp_sym_c S R C S
        (perp_col2_c P Q S R C S hPerpC (Ne.symm hRS)
          (col_permutation_1_c S P Q hS) (col_permutation_1_c R P Q hR))
    have hh2 : Perp A R S R :=
      perp_sym_c S R A R
        (perp_col2_c P Q S R A R hPerpA (Ne.symm hRS)
          (col_permutation_1_c S P Q hS) (col_permutation_1_c R P Q hR))
    have hh3 : Col S R T :=
      col3_c P Q S R T hPQ
        (col_permutation_1_c S P Q hS) (col_permutation_1_c R P Q hR)
        (col_permutation_1_c T P Q hColTPQ)
    have hh4 : Bet C T A := between_symmetry_c A T C hBetATC
    obtain ⟨M', hMidM'SR, hMidM'CD⟩ :=
      l8_24_c S R C A D T hh1 hh2 hh3 hh4 hBetRDA hCongSCRD
    have hMidM'RS : Midpoint M' R S := l7_2_c M' S R hMidM'SR
    have hMM' : M = M' := l7_17_c R S M M' hMid hMidM'RS
    rw [← hMM'] at hMidM'CD
    intro U C' hMidUC'
    constructor
    · intro hOutUA
      obtain ⟨hUR, hAR, hOrRUA⟩ := hOutUA
      have hC'S : C' ≠ S := sym_preserve_diff_c U R M C' S hUR hMidUC' hMid
      refine ⟨hCS, hC'S, ?_⟩
      rcases hOrRUA with hc | hc
      · rcases l5_3_c R U D A hc hBetRDA with hc2 | hc2
        · exact Or.inr (l7_15_c R U D S C' C M hMid hMidUC' (l7_2_c M C D hMidM'CD) hc2)
        · exact Or.inl (l7_15_c R D U S C C' M hMid (l7_2_c M C D hMidM'CD) hMidUC' hc2)
      · exact Or.inl (l7_15_c R D U S C C' M hMid (l7_2_c M C D hMidM'CD) hMidUC'
          (between_exchange4_c R D A U hBetRDA hc))
    · intro hOutCC'
      obtain ⟨hCS', hC'S', hOrCC'⟩ := hOutCC'
      have hUR : U ≠ R :=
        sym_preserve_diff_c C' S M U R hC'S'
          (l7_2_c M U C' hMidUC') (l7_2_c M R S hMid)
      have hAR : A ≠ R := (perp_distinct_c P Q A R hPerpA).2
      refine ⟨hUR, hAR, ?_⟩
      rcases hOrCC' with hc | hc
      · exact l5_1_c R D U A hRD
          (l7_15_c S C C' R D U M (l7_2_c M R S hMid) hMidM'CD (l7_2_c M U C' hMidUC') hc)
          hBetRDA
      · exact Or.inl (between_exchange4_c R U D A
          (l7_15_c S C' C R U D M (l7_2_c M R S hMid) (l7_2_c M U C' hMidUC') hMidM'CD hc)
          hBetRDA)

theorem per_col_eq_c (A B C : Tpoint)
    (h₁ : Per A B C) (hCol : Col A B C) (hBC : B ≠ C) : A = B := by
  obtain ⟨C', hMid, hCong⟩ := h₁
  obtain ⟨hBet, hCg⟩ := hMid
  have hCAC' : Col C A C' :=
    col_transitivity_1_c C B A C' (Ne.symm hBC)
      (col_permutation_3_c A B C hCol) (bet_col_c C B C' hBet)
  rcases l7_20_c A C C' hCAC' hCong with hCC' | hM
  · rw [← hCC'] at hBet hCg
    exact absurd (l7_3_c B C ⟨hBet, hCg⟩) hBC
  · exact l7_17_c C C' A B hM ⟨hBet, hCg⟩

theorem l9_4_1_c (P Q A C R S M : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := by
  rcases le_cases_c S C R A with hLe | hLe
  · exact l9_4_1_aux_c P Q A C R S M hLe h₁ hR hPerpA hS hPerpC hMid
  · intro U C' hMidUC'
    have hSpecific := l9_4_1_aux_c P Q C A S R M hLe (l9_2_c P Q A C h₁) hS hPerpC hR hPerpA
      (l7_2_c M R S hMid) C' U (l7_2_c M U C' hMidUC')
    exact (Iff.intro (l6_6_c R U A) (l6_6_c R A U)).trans
      (hSpecific.symm.trans (Iff.intro (l6_6_c S C' C) (l6_6_c S C C')))

theorem mid_two_sides_c (A B M X Y : Tpoint)
    (h₁ : Midpoint M A B) (hNCol : ¬ Col A B X) (h₂ : Midpoint M X Y) :
    TS A B X Y := by
  obtain ⟨hBetAMB, _⟩ := h₁
  obtain ⟨hBetXMY, hCongXM⟩ := h₂
  have hColMAB : Col M A B := col_permutation_4_c A M B (Or.inl hBetAMB)
  have hNColX : ¬ Col X A B := fun hc => hNCol (col_permutation_1_c X A B hc)
  have hMY : M ≠ Y := by
    intro e
    rw [← e] at hCongXM
    have hXM := cong_identity X M M hCongXM
    apply hNColX
    rw [hXM]
    exact hColMAB
  have hNColY : ¬ Col Y A B := by
    intro hc
    apply hNCol
    exact colx_c M Y X A B hMY (col_permutation_1_c M A B hColMAB)
      (col_permutation_1_c Y A B hc)
      (col_permutation_5_c M X Y (col_permutation_4_c X M Y (Or.inl hBetXMY)))
  exact ⟨hNColX, hNColY, M, hColMAB, hBetXMY⟩

theorem col_preserves_two_sides_c (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h : TS A B X Y) :
    TS C D X Y := by
  obtain ⟨hXAB, hYAB, T, hTAB, hBet⟩ := h
  have hAB : A ≠ B := by
    intro heq
    subst heq
    exact hXAB (col_trivial_2_c X A)
  refine ⟨?_, ?_, T, ?_, hBet⟩
  · intro hXCD
    apply hXAB
    apply col_permutation_2_c
    exact colx_c C D X A B hCD h₁ h₂ (col_permutation_5_c C X D (col_permutation_4_c X C D hXCD))
  · intro hYCD
    apply hYAB
    apply col_permutation_2_c
    exact colx_c C D Y A B hCD h₁ h₂ (col_permutation_5_c C Y D (col_permutation_4_c Y C D hYCD))
  · exact col3_c A B T C D hAB (col_permutation_1_c T A B hTAB) h₁ h₂

theorem out_out_two_sides_c (A B X Y U V I : Tpoint)
    (hAB : A ≠ B) (h₁ : TS A B X Y)
    (hCol1 : Col I A B) (hCol2 : Col I X Y)
    (hOut1 : Out I X U) (hOut2 : Out I Y V) : TS A B U V := by
  obtain ⟨hNX, hNY, T, hTC, hBet⟩ := h₁
  obtain ⟨hXI, hUI, horX⟩ := hOut1
  obtain ⟨hYI, hVI, horY⟩ := hOut2
  have hIU : I ≠ U := Ne.symm hUI
  have hIV : I ≠ V := Ne.symm hVI
  have hABI : Col A B I := col_permutation_1_c I A B hCol1
  have hNU : ¬ Col U A B := by
    intro hU
    have hIUX : Col I U X := by
      rcases horX with hb | hb
      · exact col_permutation_5_c I X U (bet_col_c I X U hb)
      · exact bet_col_c I U X hb
    have hABU : Col A B U := col_permutation_1_c U A B hU
    exact hNX (col3_c I U X A B hIU hIUX
      (col_permutation_1_c A I U (col_transitivity_1_c A B I U hAB hABI hABU))
      (col_permutation_1_c B I U (col_transitivity_1_c B A I U (Ne.symm hAB)
        (col_permutation_4_c A B I hABI) (col_permutation_4_c A B U hABU))))
  have hNV : ¬ Col V A B := by
    intro hV
    have hIVY : Col I V Y := by
      rcases horY with hb | hb
      · exact col_permutation_5_c I Y V (bet_col_c I Y V hb)
      · exact bet_col_c I V Y hb
    have hABV : Col A B V := col_permutation_1_c V A B hV
    exact hNY (col3_c I V Y A B hIV hIVY
      (col_permutation_1_c A I V (col_transitivity_1_c A B I V hAB hABI hABV))
      (col_permutation_1_c B I V (col_transitivity_1_c B A I V (Ne.symm hAB)
        (col_permutation_4_c A B I hABI) (col_permutation_4_c A B V hABV))))
  have hXY : X ≠ Y := by
    intro hxy
    rw [hxy] at hBet
    have hYT : Y = T := between_identity Y T hBet
    rw [← hYT] at hTC
    exact hNY hTC
  have hIT : I = T := l6_21_c A B X Y I T
    (fun hc => hNX (col_permutation_2_c A B X hc)) hXY
    (col_permutation_1_c I A B hCol1) (col_permutation_1_c T A B hTC)
    (col_permutation_1_c I X Y hCol2)
    (col_permutation_5_c X T Y (bet_col_c X T Y hBet))
  rw [← hIT] at hBet
  exact ⟨hNU, hNV, I, hCol1,
    bet_out_out_bet_c X I Y U V hBet ⟨hXI, hUI, horX⟩ ⟨hYI, hVI, horY⟩⟩

theorem l9_3_c (P Q A C M R B : Tpoint)
    (h₁ : TS P Q A C) (hM : Col M P Q)
    (hMid : Midpoint M A C) (hR : Col R P Q)
    (hOut : Out R A B) : TS P Q B C := by
  obtain ⟨hNColA, hNColC, T, hColT, hBetATC⟩ := h₁
  have hAC : A ≠ C := by
    intro h; subst h
    apply hNColA
    have hTA := between_identity A T hBetATC
    rw [hTA]; exact hColT
  have hTM : T = M := l6_21_c P Q A C T M
    (fun hc => hNColA (col_permutation_2_c P Q A hc)) hAC
    (col_permutation_1_c T P Q hColT) (col_permutation_1_c M P Q hM)
    (col_permutation_5_c A T C (bet_col_c A T C hBetATC))
    (col_permutation_5_c A M C (bet_col_c A M C (midpoint_bet_c A M C hMid)))
  rw [hTM] at hBetATC
  have hRB : R ≠ B := Ne.symm hOut.2.1
  have hColRAB : Col R A B := by
    rcases hOut.2.2 with hc | hc
    · exact bet_col_c R A B hc
    · exact col_permutation_5_c R B A (bet_col_c R B A hc)
  have hNColB : ¬ Col B P Q := by
    intro hColBPQ
    have hColRBA : Col R B A := col_permutation_5_c R A B hColRAB
    have hColPQA : Col P Q A := colx_c R B A P Q hRB
      (col_permutation_1_c R P Q hR) (col_permutation_1_c B P Q hColBPQ) hColRBA
    exact hNColA (col_permutation_2_c P Q A hColPQA)
  refine ⟨hNColB, hNColC, ?_⟩
  have hMA : M ≠ A := by
    intro h; subst h
    exact hAC (is_midpoint_id_c M C hMid)
  have hBetCMA : Bet C M A := between_symmetry_c A M C (midpoint_bet_c A M C hMid)
  rcases hOut.2.2 with hRAB | hRBA
  · rcases point_equality_decidability M R with hMReq | hMR
    · subst hMReq
      exact ⟨M, hM, between_symmetry_c C M B (outer_transitivity_between_c C M A B hBetCMA hRAB hMA)⟩
    · obtain ⟨B', hMidBB'⟩ := symmetric_point_construction_c B M
      obtain ⟨R', hMidRR'⟩ := symmetric_point_construction_c R M
      have hBetB'CR' : Bet B' C R' :=
        l7_15_c B A R B' C R' M hMidBB' hMid hMidRR' (between_symmetry_c R A B hRAB)
      have hBetBMB' : Bet B M B' := midpoint_bet_c B M B' hMidBB'
      have hBetR'CB' : Bet R' C B' := between_symmetry_c B' C R' hBetB'CR'
      obtain ⟨X, hMXR', hCXB⟩ := inner_pasch B R' B' M C hBetBMB' hBetR'CB'
      refine ⟨X, ?_, between_symmetry_c C X B hCXB⟩
      have hMR' : M ≠ R' := by
        intro hEq
        exact hMR (is_midpoint_id_c M R (hEq ▸ l7_2_c M R R' hMidRR'))
      have hColMRR' : Col M R R' :=
        col_permutation_4_c R M R' (bet_col_c R M R' (midpoint_bet_c R M R' hMidRR'))
      have hColPQR' : Col P Q R' := colx_c M R R' P Q hMR
        (col_permutation_1_c M P Q hM) (col_permutation_1_c R P Q hR) hColMRR'
      have hColMR'X : Col M R' X := col_permutation_5_c M X R' (bet_col_c M X R' hMXR')
      exact col_permutation_2_c P Q X (colx_c M R' X P Q hMR'
        (col_permutation_1_c M P Q hM) hColPQR' hColMR'X)
  · obtain ⟨X, hBXC, hMXR⟩ := inner_pasch R C A B M hRBA hBetCMA
    refine ⟨X, ?_, hBXC⟩
    rcases point_equality_decidability M R with hMReq | hMR
    · subst hMReq
      exact (between_identity M X hMXR) ▸ hM
    · rcases point_equality_decidability R X with hRXeq | hRX
      · rw [← hRXeq]; exact hR
      · rcases point_equality_decidability X M with hXMeq | hXM
        · rw [hXMeq]; exact hM
        · have hColMRX : Col M R X := col_permutation_5_c M X R (bet_col_c M X R hMXR)
          exact col_permutation_2_c P Q X (colx_c M R X P Q hMR
            (col_permutation_1_c M P Q hM) (col_permutation_1_c R P Q hR) hColMRX)

theorem l9_4_2_aux_c (P Q A C R S U V : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := by
  obtain ⟨hNColA, hNColC, T, hColT, hBetATC⟩ := h₁
  have hPQ : P ≠ Q := by
    intro h; subst h; exact hNColA (col_trivial_2_c A P)
  rcases eq_dec_points_c R S with hRS | hRS
  · subst hRS
    have hRT : R = T := by
      rcases eq_dec_points_c R T with h | hne
      · exact h
      · exfalso
        have hPerpRTAR : Perp R T A R :=
          perp_col2_c P Q R T A R hPerpA hne
            (col_permutation_1_c R P Q hR) (col_permutation_1_c T P Q hColT)
        have hPerpRTCR : Perp R T C R :=
          perp_col2_c P Q R T C R hPerpC hne
            (col_permutation_1_c R P Q hR) (col_permutation_1_c T P Q hColT)
        have hPerTRA : Per T R A :=
          perp_in_per_c T R A
            (perp_in_comm_c R T A R R (perp_perp_in_c R T A hPerpRTAR))
        have hPerTRC : Per T R C :=
          perp_in_per_c T R C
            (perp_in_comm_c R T C R R (perp_perp_in_c R T C hPerpRTCR))
        exact hne (l8_6_c A R T C (l8_2_c T R A hPerTRA) (l8_2_c T R C hPerTRC) hBetATC)
    rw [← hRT] at hBetATC hColT
    exact out_out_two_sides_c P Q A C U V R hPQ ⟨hNColA, hNColC, R, hColT, hBetATC⟩
      hR
      (col_permutation_4_c A R C (bet_col_c A R C hBetATC))
      (l6_6_c R U A hOutU) (l6_6_c R V C hOutV)
  · obtain ⟨M, hMidMRS⟩ := midpoint_existence_c R S
    have hMPQ : Col M P Q := by
      have hBetRMS := midpoint_bet_c R M S hMidMRS
      rcases eq_dec_points_c R M with hRM | hRM
      · rw [← hRM]; exact hR
      · have hColRMS : Col R M S := bet_col_c R M S hBetRMS
        exact col_permutation_2_c P Q M (colx_c R S M P Q hRS
          (col_permutation_1_c R P Q hR) (col_permutation_1_c S P Q hS)
          (col_permutation_5_c R M S hColRMS))
    have hIff := l9_4_1_aux_c P Q A C R S M hLe ⟨hNColA, hNColC, T, hColT, hBetATC⟩ hR hPerpA hS hPerpC hMidMRS
    obtain ⟨U', hMidUU'⟩ := symmetric_point_construction_c U M
    have hOutSCU' : Out S C U' := (hIff U U' hMidUU').mp hOutU
    have hOutSU'C : Out S U' C := l6_6_c S C U' hOutSCU'
    have hOutSCV : Out S C V := l6_6_c S V C hOutV
    have hOutSU'V : Out S U' V := l6_7_c S U' C V hOutSU'C hOutSCV
    have hNColRSU : ¬ Col R S U := by
      intro hColU
      have hColRUA : Col R U A := by
        rcases hOutU.2.2 with hc | hc
        · exact bet_col_c R U A hc
        · exact col_permutation_5_c R A U (bet_col_c R A U hc)
      have hRU : R ≠ U := Ne.symm hOutU.1
      have hColRSA : Col R S A := colx_c R U A R S hRU
        (col_trivial_3_c R S) hColU hColRUA
      have hColPQA2 : Col P Q A := colx_c R S A P Q hRS
        (col_permutation_1_c R P Q hR) (col_permutation_1_c S P Q hS) hColRSA
      exact hNColA (col_permutation_2_c P Q A hColPQA2)
    have hTSRSUU' : TS R S U U' := mid_two_sides_c R S M U U' hMidMRS hNColRSU hMidUU'
    have hColRSP : Col R S P := col3_c P Q R S P hPQ
      (col_permutation_1_c R P Q hR) (col_permutation_1_c S P Q hS) (col_trivial_3_c P Q)
    have hColRSQ : Col R S Q := col3_c P Q R S Q hPQ
      (col_permutation_1_c R P Q hR) (col_permutation_1_c S P Q hS) (col_trivial_2_c P Q)
    have hTSPQUU' : TS P Q U U' := col_preserves_two_sides_c R S P Q U U' hPQ hColRSP hColRSQ hTSRSUU'
    have hTSPQU'U : TS P Q U' U := l9_2_c P Q U U' hTSPQUU'
    have hFinal : TS P Q V U :=
      l9_3_c P Q U' U M S V hTSPQU'U hMPQ (l7_2_c M U U' hMidUU') hS hOutSU'V
    exact l9_2_c P Q V U hFinal

theorem l9_4_2_c (P Q A C R S U V : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := by
  have H6 := le_cases_c S C R A
  rcases H6 with H7 | H7
  · exact l9_4_2_aux_c P Q A C R S U V H7 h₁ hR hPerpA hS hPerpC hOutU hOutV
  · exact l9_2_c P Q V U ((let H8 := l9_2_c P Q A C h₁; l9_4_2_aux_c P Q C A S R V U H7 H8 hS hPerpC hR hPerpA hOutV hOutU))

theorem l9_5_c (P Q A C R B : Tpoint)
    (h₁ : TS P Q A C) (hR : Col R P Q) (hOut : Out R A B) : TS P Q B C := by
  have hNColAPQ : ¬ Col A P Q := h₁.1
  have hNColCPQ : ¬ Col C P Q := h₁.2.1
  have hPQ : P ≠ Q := (not_col_distincts_c A P Q hNColAPQ).2.2.1
  have hNColPQA : ¬ Col P Q A := fun h => hNColAPQ (by colr)
  have hNColPQC : ¬ Col P Q C := fun h => hNColCPQ (by colr)
  obtain ⟨A', hColPQA', hPerpPQAA'⟩ := l8_18_existence_c P Q A hNColPQA
  obtain ⟨C', hColPQC', hPerpPQCC'⟩ := l8_18_existence_c P Q C hNColPQC
  have hColA'PQ : Col A' P Q := by show Col A' P Q; colr
  have hColC'PQ : Col C' P Q := by show Col C' P Q; colr
  have hColRAB : Col R A B := out_col_c R A B hOut
  have hRB : R ≠ B := Ne.symm hOut.2.1
  have hNColPQB : ¬ Col P Q B := by
    intro hColPQB
    have hColPQR : Col P Q R := by show Col P Q R; colr
    have hColRBA : Col R B A := by show Col R B A; colr
    exact hNColPQA (colx_c R B A P Q hRB hColPQR hColPQB hColRBA)
  obtain ⟨B', hColPQB', hPerpPQBB'⟩ := l8_18_existence_c P Q B hNColPQB
  obtain ⟨M, hMidMA'C'⟩ := midpoint_existence_c A' C'
  obtain ⟨D, hMidMAD⟩ := symmetric_point_construction_c A M
  have hIff := l9_4_1_c P Q A C A' C' M h₁ hColA'PQ hPerpPQAA' hColC'PQ hPerpPQCC'
    hMidMA'C' A D hMidMAD
  have hAA' : A ≠ A' := (perp_distinct_c P Q A A' hPerpPQAA').2
  have hOutA'AA : Out A' A A := out_trivial_c A' A hAA'
  have hOutC'CD : Out C' C D := hIff.mp hOutA'AA
  have hOutC'DC : Out C' D C := l6_6_c C' C D hOutC'CD
  have hTSPQAD : TS P Q A D :=
    l9_4_2_c P Q A C A' C' A D h₁ hColA'PQ hPerpPQAA' hColC'PQ hPerpPQCC' hOutA'AA hOutC'DC
  have hColA'MC' : Col A' M C' := bet_col_c A' M C' (midpoint_bet_c A' M C' hMidMA'C')
  have hColMPQ : Col M P Q := by
    rcases point_equality_decidability A' C' with hA'C' | hA'C'
    · have hMidMA'A' : Midpoint M A' A' := hA'C' ▸ hMidMA'C'
      have hMA' : M = A' := l7_3_c M A' hMidMA'A'
      rw [hMA']
      exact hColA'PQ
    · show Col M P Q
      colr
  have hTSPQBD : TS P Q B D := l9_3_c P Q A D M R B hTSPQAD hColMPQ hMidMAD hR hOut
  have hColC'DC : Col C' D C := out_col_c C' D C hOutC'DC
  have hColC'CD : Col C' C D := by
    show Col C' C D
    colr
  have hPerpPQC'D : Perp P Q C' D :=
    perp_col1_c P Q C' C D hOutC'DC.1.symm (perp_right_comm_c P Q C C' hPerpPQCC') hColC'CD
  have hPerpPQDC' : Perp P Q D C' := perp_right_comm_c P Q C' D hPerpPQC'D
  have hBB' : B ≠ B' := (perp_distinct_c P Q B B' hPerpPQBB').2
  have hOutB'BB : Out B' B B := out_trivial_c B' B hBB'
  have hOutC'CD2 : Out C' C D := l6_6_c C' D C hOutC'DC
  have hColB'PQ : Col B' P Q := by
    show Col B' P Q
    colr
  exact l9_4_2_c P Q B D B' C' B C hTSPQBD hColB'PQ hPerpPQBB' hColC'PQ hPerpPQDC' hOutB'BB hOutC'CD2

theorem not_two_sides_id_c (A P Q : Tpoint) : ¬ TS P Q A A := by
  intro H
  obtain ⟨_, H0⟩ := H
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨T, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  have H6 := between_identity A T H5
  subst H6
  exact H1 H4

theorem outer_pasch_c (A B C P Q : Tpoint) (h₁ : Bet A C P) (h₂ : Bet B Q C) :
    ∃ X, Bet A X B ∧ Bet P Q X := by
  rcases col_dec_c P Q C with hColPQC | hNColPQC
  · rcases bet_dec_c P Q C with hBetPQC | hNBetPQC
    · exact ⟨A, between_trivial2_c A B, between_exchange4_c P Q C A hBetPQC (between_symmetry_c A C P h₁)⟩
    · have hOutQPC : Out Q P C := l6_4_2_c P C Q ⟨hColPQC, hNBetPQC⟩
      rcases hOutQPC.2.2 with hBetQPC | hBetQCP
      · exact ⟨B, between_trivial_c A B,
          between_exchange3_c C P Q B (between_symmetry_c Q P C hBetQPC) (between_symmetry_c B Q C h₂)⟩
      · exact ⟨B, between_trivial_c A B,
          outer_transitivity_between2_c P C Q B (between_symmetry_c Q C P hBetQCP)
            (between_symmetry_c B Q C h₂) hOutQPC.2.1⟩
  · rcases point_equality_decidability B Q with hBQeq | hBQ
    · refine ⟨B, between_trivial_c A B, ?_⟩
      rw [hBQeq]
      exact between_trivial_c P Q
    · have hAP : A ≠ P := by
        intro e
        have hBetACA : Bet A C A := e ▸ h₁
        have hAC : A = C := between_identity A C hBetACA
        have hCP2 : C = P := hAC.symm.trans e
        exact hNColPQC (hCP2 ▸ col_trivial_3_c P Q)
      have hPQ : P ≠ Q := by
        intro e
        exact hNColPQC (e ▸ col_trivial_1_c P C)
      have hPB : P ≠ B := by
        intro e
        have hBetPQC : Bet P Q C := e ▸ h₂
        exact hNColPQC (bet_col_c P Q C hBetPQC)
      have hNColCPQ : ¬ Col C P Q := fun h => hNColPQC (by colr)
      have hNColBPQ : ¬ Col B P Q := by
        intro hColBPQ
        have hColBQC : Col B Q C := bet_col_c B Q C h₂
        have hColPQB2 : Col P Q B := by show Col P Q B; colr
        exact hNColPQC (colx_c B Q C P Q hBQ hColPQB2 (col_trivial_2_c P Q) hColBQC)
      have hTSPQCB : TS P Q C B :=
        ⟨hNColCPQ, hNColBPQ, Q, col_trivial_3_c Q P, between_symmetry_c B Q C h₂⟩
      have hCP : C ≠ P := by
        intro e
        exact hNColCPQ (e ▸ col_trivial_1_c P Q)
      have hOutPCA : Out P C A := ⟨hCP, hAP, Or.inl (between_symmetry_c A C P h₁)⟩
      have hTSPQAB : TS P Q A B := l9_5_c P Q C B P A hTSPQCB (col_trivial_1_c P Q) hOutPCA
      obtain ⟨hNColAPQ2, hNColBPQ2, X, hColXPQ, hBetAXB⟩ := hTSPQAB
      obtain ⟨T, hBetXTP, hBetCTB⟩ :=
        inner_pasch B P A X C (between_symmetry_c A X B hBetAXB) (between_symmetry_c A C P h₁)
      have hBC : B ≠ C := by
        intro e
        have hTSPQBB : TS P Q B B := e ▸ hTSPQCB
        exact not_two_sides_id_c B P Q hTSPQBB
      have hNColXPB : ¬ Col X P B := by
        intro hColXPB
        have hXP : X ≠ P := by
          intro e
          have hBetAPB : Bet A P B := e ▸ hBetAXB
          have hColAPB : Col A P B := bet_col_c A P B hBetAPB
          have hColACP : Col A C P := bet_col_c A C P h₁
          have hColAPC : Col A P C := by show Col A P C; colr
          have hColABC : Col A B C := col_transitivity_1_c A P B C hAP hColAPB hColAPC
          have hColBQC2 : Col B Q C := bet_col_c B Q C h₂
          have hColCBQ : Col C B Q := by show Col C B Q; colr
          have hColABQ : Col A B Q :=
            colx_c C B Q A B hBC.symm hColABC (col_trivial_2_c A B) hColCBQ
          have hABne : A ≠ B := by
            intro e2
            have hBetAPA : Bet A P A := e2 ▸ hBetAPB
            exact hAP (between_identity A P hBetAPA)
          have hColAPQ : Col A P Q :=
            colx_c A B Q A P hABne (col_trivial_3_c A P) hColAPB hColABQ
          exact hNColAPQ2 hColAPQ
        have hColPXQ : Col P X Q := by show Col P X Q; colr
        have hColPXB : Col P X B := by show Col P X B; colr
        have hColPQB : Col P Q B := col_transitivity_1_c P X Q B hXP.symm hColPXQ hColPXB
        have hColBPQ2 : Col B P Q := by show Col B P Q; colr
        exact hNColBPQ2 hColBPQ2
      have hColXTP : Col X T P := bet_col_c X T P hBetXTP
      have hColXPT : Col X P T := by show Col X P T; colr
      have hColCTB : Col C T B := bet_col_c C T B hBetCTB
      have hColBCT : Col B C T := by show Col B C T; colr
      have hColBQC3 : Col B Q C := bet_col_c B Q C h₂
      have hColBCQ2 : Col B C Q := by show Col B C Q; colr
      have hEqTQ : T = Q := l6_21_c X P B C T Q hNColXPB hBC hColXPT hColXPQ hColBCT hColBCQ2
      exact ⟨X, hBetAXB, between_symmetry_c X Q P (hEqTQ ▸ hBetXTP)⟩

theorem os_distincts_c (A B X Y : Tpoint) (h : OS A B X Y) :
    A ≠ B ∧ A ≠ X ∧ A ≠ Y ∧ B ≠ X ∧ B ≠ Y := by
  obtain ⟨Z, HTS1, HTS2⟩ := h
  have HTS3 := ts_distincts_c A B X Z HTS1
  have HTS4 := ts_distincts_c A B Y Z HTS2
  obtain ⟨hAB1, hAX, _, hBX, _, _⟩ := HTS3
  obtain ⟨_, hAY, _, hBY, _, _⟩ := HTS4
  exact ⟨hAB1, hAX, hAY, hBX, hBY⟩

theorem invert_one_side_c (A B P Q : Tpoint) (h : OS A B P Q) : OS B A P Q := by
  obtain ⟨R, h1, h2⟩ := h
  obtain ⟨nc1, nc2, T, hcolT, hbet⟩ := h1
  obtain ⟨nc1', nc2', T', hcolT', hbet'⟩ := h2
  exact ⟨R,
    ⟨not_col_permutation_5_c P A B nc1, not_col_permutation_5_c R A B nc2,
     T, col_permutation_5_c T A B hcolT, hbet⟩,
    ⟨not_col_permutation_5_c Q A B nc1', not_col_permutation_5_c R A B nc2',
     T', col_permutation_5_c T' A B hcolT', hbet'⟩⟩

theorem l9_8_1_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : TS P Q B C) :
    OS P Q A B :=
  ⟨C, (⟨h₁, h₂⟩)⟩

theorem l9_8_2_c (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : OS P Q A B) :
    TS P Q B C := by
  have h1copy := h₁
  obtain ⟨hNColAPQ, hNColCPQ, T, hColTPQ, hBetATC⟩ := h1copy
  have h2copy := h₂
  obtain ⟨D, hTSAD, hTSBD⟩ := h2copy
  have hTSADcopy := hTSAD
  have hTSBDcopy := hTSBD
  obtain ⟨hNColAPQ2, hNColDPQ, X, hColXPQ, hBetAXD⟩ := hTSADcopy
  obtain ⟨hNColBPQ, hNColDPQ2, Y, hColYPQ, hBetBYD⟩ := hTSBDcopy
  have hAD : A ≠ D := fun e => not_two_sides_id_c A P Q (e ▸ hTSAD)
  have hBD : B ≠ D := fun e => not_two_sides_id_c B P Q (e ▸ hTSBD)
  obtain ⟨M, hBetYMA, hBetXMB⟩ := inner_pasch B A D Y X hBetBYD hBetAXD
  rcases col_dec_c A B D with hColABD | hNColABD
  · have hColADX : Col A D X := by
      have hColAXD : Col A X D := bet_col_c A X D hBetAXD
      show Col A D X; colr
    have hColADY : Col A D Y := by
      have hColBYD2 : Col B Y D := bet_col_c B Y D hBetBYD
      have hColDBA : Col D B A := by show Col D B A; colr
      have hColDBY : Col D B Y := by show Col D B Y; colr
      have hColDAY : Col D A Y := col_transitivity_1_c D B A Y hBD.symm hColDBA hColDBY
      show Col A D Y; colr
    have hColPQX : Col P Q X := by show Col P Q X; colr
    have hColPQY : Col P Q Y := by show Col P Q Y; colr
    have hNColPQA : ¬ Col P Q A := fun h => hNColAPQ2 (by colr)
    have hXeqY : X = Y := l6_21_c P Q A D X Y hNColPQA hAD hColPQX hColPQY hColADX hColADY
    have hDX : D ≠ X := fun e => hNColDPQ (e ▸ hColXPQ)
    have hAX : A ≠ X := fun e => hNColAPQ2 (e ▸ hColXPQ)
    have hBX : B ≠ X := fun e => hNColBPQ (e ▸ hColXPQ)
    have hDXA : Bet D X A := between_symmetry_c A X D hBetAXD
    rcases point_equality_decidability M Y with hMYeq | hMYne
    · have hBetBXD : Bet B X D := hXeqY ▸ hBetBYD
      have hDXB : Bet D X B := between_symmetry_c B X D hBetBXD
      rcases hColABD with hBetABD | hBetBDA | hBetDAB
      · have hBet1 : Bet X B A :=
          between_exchange3_c D X B A hDXB (between_symmetry_c A B D hBetABD)
        exact l9_5_c P Q A C X B h₁ hColXPQ ⟨hAX, hBX, Or.inr hBet1⟩
      · rcases l5_1_c D X B A hDX hDXB hDXA with hDBA | hDAB
        · exact absurd (between_equality_c D B A hDBA hBetBDA).symm hBD
        · exact absurd (between_equality_c D A B hDAB (between_symmetry_c B D A hBetBDA)).symm hAD
      · have hBet3 := l5_2_c D X A B hDX hDXA hDXB
        exact l9_5_c P Q A C X B h₁ hColXPQ ⟨hAX, hBX, hBet3⟩
    · have hAY2 : A ≠ Y := fun e => hNColAPQ2 (e ▸ hColYPQ)
      have hOutYAM2 : Out Y A M := ⟨hAY2, hMYne, Or.inr hBetYMA⟩
      have hInner2 : TS P Q M C := l9_5_c P Q A C Y M h₁ hColYPQ hOutYAM2
      rcases point_equality_decidability M X with hMXeq | hMXne
      · exact absurd (hMXeq.trans hXeqY) hMYne
      · have hOutXMB2 : Out X M B := ⟨hMXne, hBX, Or.inl hBetXMB⟩
        exact l9_5_c P Q M C X B hInner2 hColXPQ hOutXMB2
  · have hAY : A ≠ Y := fun e => hNColAPQ2 (e ▸ hColYPQ)
    have hOutYAM : Out Y A M := by
      refine ⟨hAY, ?_, Or.inr hBetYMA⟩
      intro eMY
      have hBetBMD : Bet B M D := eMY ▸ hBetBYD
      have hColYPQeqM : Col M P Q := eMY ▸ hColYPQ
      have hBM : B ≠ M := fun eBM => hNColBPQ (eBM ▸ hColYPQeqM)
      have hColBMD : Col B M D := bet_col_c B M D hBetBMD
      have hColBMX : Col B M X := bet_col_c B M X (between_symmetry_c X M B hBetXMB)
      have hColBDX : Col B D X := col_transitivity_1_c B M D X hBM hColBMD hColBMX
      have hXD : X ≠ D := fun e => hNColDPQ (e ▸ hColXPQ)
      have hColDXA : Col D X A := bet_col_c D X A (between_symmetry_c A X D hBetAXD)
      have hColDXB : Col D X B := by show Col D X B; colr
      have hColDAB : Col D A B := col_transitivity_1_c D X A B hXD.symm hColDXA hColDXB
      exact hNColABD (show Col A B D by colr)
    have hBX : B ≠ X := fun e => hNColBPQ (e ▸ hColXPQ)
    have hOutXMB : Out X M B := by
      refine ⟨?_, hBX, Or.inl hBetXMB⟩
      intro eMX
      have hBetAMD : Bet A M D := eMX ▸ hBetAXD
      have hColXPQeqM : Col M P Q := eMX ▸ hColXPQ
      have hAM : A ≠ M := fun eAM => hNColAPQ2 (eAM ▸ hColXPQeqM)
      have hColAMD : Col A M D := bet_col_c A M D hBetAMD
      have hColAMY : Col A M Y := bet_col_c A M Y (between_symmetry_c Y M A hBetYMA)
      have hColADY : Col A D Y := col_transitivity_1_c A M D Y hAM hColAMD hColAMY
      have hDY : D ≠ Y := fun e => hNColDPQ (e ▸ hColYPQ)
      have hColDYA : Col D Y A := by show Col D Y A; colr
      have hColDYB : Col D Y B := bet_col_c D Y B (between_symmetry_c B Y D hBetBYD)
      have hColDAB2 : Col D A B := col_transitivity_1_c D Y A B hDY hColDYA hColDYB
      exact hNColABD (show Col A B D by colr)
    have hInner : TS P Q M C := l9_5_c P Q A C Y M h₁ hColYPQ hOutYAM
    exact l9_5_c P Q M C X B hInner hColXPQ hOutXMB

theorem l9_9_c (P Q A B : Tpoint) (h : TS P Q A B) : ¬ OS P Q A B := by
  intro h2
  exact not_two_sides_id_c B P Q (l9_8_2_c P Q A B B h h2)

theorem l9_9_bis_c (P Q A B : Tpoint) (h : OS P Q A B) : ¬ TS P Q A B := by
  intro H0
  obtain ⟨C, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  have H4 := l9_8_1_c P Q A B C H2 H3
  have H5 := l9_9_c P Q A B H0
  exact ((H5 H4)).elim

theorem one_side_chara_c (P Q A B : Tpoint) (h : OS P Q A B) :
    ∀ X, Col X P Q → ¬ Bet A X B := by
  have hcopy := h
  obtain ⟨R, ⟨hNColA, _, _⟩, ⟨hNColB, _, _⟩⟩ := hcopy
  intro X hColXPQ hBetAXB
  exact l9_9_bis_c P Q A B h ⟨hNColA, hNColB, ⟨X, hColXPQ, hBetAXB⟩⟩

theorem l9_10_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) : ∃ C, TS P Q A C := by
  obtain ⟨A', hA'⟩ := symmetric_point_construction_c A P
  refine ⟨A', ?_, ?_, P, ?_, ?_⟩
  · exact hNCol
  · intro hCol
    apply hNCol
    apply col_permutation_2_c
    apply col_transitivity_1_c P A'
    · intro hEq
      rw [← hEq] at hA'
      have hMid := l7_2_c P A P hA'
      have hEq2 := is_midpoint_id_c P A hMid
      rw [← hEq2] at hNCol
      exact hNCol (col_trivial_1_c P Q)
    · exact col_permutation_4_c A' P Q hCol
    · right; right
      exact midpoint_bet_c A P A' hA'
  · exact col_trivial_1_c P Q
  · exact midpoint_bet_c A P A' hA'

theorem one_side_reflexivity_c (P Q A : Tpoint) (hNCol : ¬ Col A P Q) :
    OS P Q A A := by
  obtain ⟨C, hMid⟩ := symmetric_point_construction_c A P
  obtain ⟨hBet, hCong⟩ := hMid
  have hNC : ¬ Col C P Q := by
    intro h0
    rcases eq_dec_points_c C P with hCP | hCP
    · rw [hCP] at hCong
      have hAP : A = P := cong_identity A P P hCong
      exact hNCol (by rw [hAP]; exact col_trivial_1_c P Q)
    · exact hNCol (col_permutation_4_c P A Q
        (col_transitivity_1_c P C A Q (Ne.symm hCP)
          (col_permutation_1_c A P C (bet_col_c A P C hBet))
          (col_permutation_4_c C P Q h0)))
  exact ⟨C, ⟨hNCol, hNC, P, col_trivial_1_c P Q, hBet⟩,
         ⟨hNCol, hNC, P, col_trivial_1_c P Q, hBet⟩⟩

theorem one_side_symmetry_c (P Q A B : Tpoint) (h : OS P Q A B) :
    OS P Q B A := by
  obtain ⟨C, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  exact ⟨C, (⟨H2, H1⟩)⟩

theorem one_side_transitivity_c (P Q A B C : Tpoint)
    (h₁ : OS P Q A B) (h₂ : OS P Q B C) : OS P Q A C := by
  obtain ⟨X, H1⟩ := h₁
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨Y, H4⟩ := h₂
  obtain ⟨H5, H6⟩ := H4
  exact ⟨X, (⟨H2, (l9_2_c P Q X C (l9_8_2_c P Q Y X C (l9_2_c P Q C Y H6) (l9_8_1_c P Q Y X B (l9_2_c P Q B Y H5) (l9_2_c P Q B X H3))))⟩)⟩

theorem l9_17_c (A B C P Q : Tpoint) (h₁ : OS P Q A C) (h₂ : Bet A B C) :
    OS P Q A B := by
  rcases point_equality_decidability A C with hAC | hAC
  · have hAB : A = B := between_identity A B (hAC ▸ h₂)
    have hBC : B = C := hAB.symm.trans hAC
    exact hBC ▸ h₁
  · have h₁copy := h₁
    obtain ⟨D, hTSAD, hTSCD⟩ := h₁copy
    obtain ⟨hNColAPQ, hNColDPQ, X, hColXPQ, hBetAXD⟩ := hTSAD
    obtain ⟨hNColCPQ, hNColDPQ2, Y, hColYPQ, hBetCYD⟩ := hTSCD
    obtain ⟨T, hBetBTD, hBetXTY⟩ := l3_17_c A X D C Y B hBetAXD hBetCYD h₂
    refine ⟨D, ⟨hNColAPQ, hNColDPQ, X, hColXPQ, hBetAXD⟩, ?_⟩
    have hColTPQ : Col T P Q := by
      rcases point_equality_decidability X Y with hXY | hXY
      · have hTX : T = X := (between_identity X T (hXY ▸ hBetXTY)).symm
        exact hTX ▸ hColXPQ
      · have hColPQX : Col P Q X := by show Col P Q X; colr
        have hColPQY : Col P Q Y := by show Col P Q Y; colr
        have hColXYT2 : Col X Y T := by
          have hColXTY : Col X T Y := bet_col_c X T Y hBetXTY
          show Col X Y T
          colr
        have hColPQT : Col P Q T := colx_c X Y T P Q hXY hColPQX hColPQY hColXYT2
        show Col T P Q
        colr
    have hNColBPQ : ¬ Col B P Q := by
      intro hColBPQ
      exact l9_9_bis_c P Q A C h₁ ⟨hNColAPQ, hNColCPQ, B, hColBPQ, h₂⟩
    exact ⟨hNColBPQ, hNColDPQ, T, hColTPQ, hBetBTD⟩

theorem l9_18_c (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    TS X Y A B ↔ (Bet A P B ∧ ¬ Col X Y A ∧ ¬ Col X Y B) := by
  constructor
  · intro hTS
    obtain ⟨hNA, hNB, T, hTCol, hBet⟩ := hTS
    have hXY : X ≠ Y := by
      intro hEq
      subst hEq
      exact hNB (col_trivial_2_c B X)
    have hPT : P = T := by
      apply l6_21_c X Y A B P T
      · exact not_col_permutation_5_c X A Y (not_col_permutation_4_c A X Y hNA)
      · intro hEq
        subst hEq
        have : A = T := between_identity A T hBet
        subst this
        exact hNA hTCol
      · exact h₁
      · exact col_permutation_5_c X T Y (col_permutation_4_c T X Y hTCol)
      · exact h₂
      · exact col_permutation_5_c A T B (bet_col_c A T B hBet)
    subst hPT
    refine ⟨hBet, ?_, ?_⟩
    · exact not_col_permutation_5_c X A Y (not_col_permutation_4_c A X Y hNA)
    · exact not_col_permutation_5_c X B Y (not_col_permutation_4_c B X Y hNB)
  · intro hConj
    obtain ⟨hBet, hNA, hNB⟩ := hConj
    refine ⟨?_, ?_, P, ?_, hBet⟩
    · exact not_col_permutation_5_c A Y X (not_col_permutation_3_c X Y A hNA)
    · exact not_col_permutation_5_c B Y X (not_col_permutation_3_c X Y B hNB)
    · exact col_permutation_2_c X Y P h₁

theorem l9_19_c (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    OS X Y A B ↔ (Out P A B ∧ ¬ Col X Y A) := by
  constructor
  · intro hOS
    have hOScopy := hOS
    obtain ⟨D, hTSAD, hTSBD⟩ := hOScopy
    obtain ⟨hNColAXY, hNColDXY, M, hColMXY, hBetAMD⟩ := hTSAD
    obtain ⟨hNColBXY, hNColDXY2, N, hColNXY, hBetBND⟩ := hTSBD
    have hAP : A ≠ P := by
      intro e
      have hColXYA : Col X Y A := e ▸ h₁
      exact hNColAXY (show Col A X Y by colr)
    have hBP : B ≠ P := by
      intro e
      have hColXYB : Col X Y B := e ▸ h₁
      exact hNColBXY (show Col B X Y by colr)
    have hBetOr : Bet P A B ∨ Bet P B A := by
      rcases h₂ with hCase1 | hCase2 | hCase3
      · exact Or.inr (between_symmetry_c A B P hCase1)
      · exfalso
        have hTSXYAB : TS X Y A B :=
          ⟨hNColAXY, hNColBXY, P, (show Col P X Y by colr), between_symmetry_c B P A hCase2⟩
        exact absurd hTSXYAB (l9_9_bis_c X Y A B hOS)
      · exact Or.inl hCase3
    exact ⟨⟨hAP, hBP, hBetOr⟩, fun hColXYA => hNColAXY (show Col A X Y by colr)⟩
  · intro ⟨hOutPAB, hNColXYA⟩
    obtain ⟨D, hTSXYAD⟩ := l9_10_c X Y A (fun h => hNColXYA (by colr))
    exact ⟨D, hTSXYAD, l9_5_c X Y A D P B hTSXYAD (show Col P X Y by colr) hOutPAB⟩

theorem one_side_not_col123_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B X := by
  obtain ⟨C, H0⟩ := h
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  obtain ⟨H4, H5⟩ := H1
  obtain ⟨_, _⟩ := H5
  intro H6
  exact H4 (col_permutation_2_c A B X H6)

theorem one_side_not_col124_c (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B Y :=
  one_side_not_col123_c A B Y X (one_side_symmetry_c A B X Y h)

theorem col_two_sides_c (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : TS A B P Q) : TS A C P Q := by
  obtain ⟨hPAB, hQAB, T, hTAB, hBet⟩ := h
  refine ⟨?_, ?_, T, ?_, hBet⟩
  · intro hPAC
    apply hPAB
    apply col_permutation_2_c
    exact col_transitivity_1_c A C B P hAC (col_permutation_5_c A B C hCol) (col_permutation_1_c P A C hPAC)
  · intro hQAC
    apply hQAB
    apply col_permutation_2_c
    exact col_transitivity_1_c A C B Q hAC (col_permutation_5_c A B C hCol) (col_permutation_1_c Q A C hQAC)
  · apply col_permutation_2_c
    apply col_transitivity_1_c A B C T
    · intro hAB
      subst hAB
      exact hQAB (col_trivial_2_c Q A)
    · exact hCol
    · exact col_permutation_1_c T A B hTAB

theorem col_one_side_c (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : OS A B P Q) : OS A C P Q := by
  obtain ⟨T, H2⟩ := h
  obtain ⟨H3, H4⟩ := H2
  exact ⟨T, (⟨(col_two_sides_c A B C P T hCol hAC H3), (col_two_sides_c A B C Q T hCol hAC H4)⟩)⟩

theorem os_out_os_c (A B C D C' P : Tpoint)
    (hCol : Col A B P) (h₁ : OS A B C D) (h₂ : Out P C C') :
    OS A B C' D := by
  have h₁copy := h₁
  obtain ⟨T', hTSCT'0, hTSDT'0⟩ := h₁copy
  have hNColCAB : ¬ Col C A B := hTSCT'0.1
  have hAB : A ≠ B := (not_col_distincts_c C A B hNColCAB).2.2.1
  obtain ⟨T, hBetCPT, hCongPTCP⟩ := segment_construction C P C P
  have hPT : P ≠ T := by
    intro e
    have hCongPPCP : Cong P P C P := e ▸ hCongPTCP
    have hCP : C = P := cong_identity C P P (cong_symmetry_c P P C P hCongPPCP)
    have hColABC : Col A B C := hCP ▸ hCol
    exact hNColCAB (show Col C A B by colr)
  have hColCPT : Col C P T := bet_col_c C P T hBetCPT
  have hNColTAB : ¬ Col T A B := by
    intro hColTAB
    exact hNColCAB (show Col C A B by colr)
  have hTSCT : TS A B C T := ⟨hNColCAB, hNColTAB, P, (show Col P A B by colr), hBetCPT⟩
  have hTSTC : TS A B T C := l9_2_c A B C T hTSCT
  have hColPTC : Col P T C := by colr
  have hTSTC' : TS A B T C' :=
    out_out_two_sides_c A B T C T C' P hAB hTSTC (show Col P A B by colr) hColPTC
      (out_trivial_c P T (Ne.symm hPT)) h₂
  have hOSCC' : OS A B C C' := l9_8_1_c A B C C' T hTSCT (l9_2_c A B T C' hTSTC')
  exact one_side_transitivity_c A B C' C D (one_side_symmetry_c A B C C' hOSCC') h₁

theorem out_out_one_side_c (A B X Y Z : Tpoint)
    (h₁ : OS A B X Y) (h₂ : Out A Y Z) : OS A B X Z :=
  one_side_symmetry_c A B Z X
    (os_out_os_c A B Y X Z A (col_trivial_3_c A B) (one_side_symmetry_c A B X Y h₁) h₂)

theorem out_one_side_c (A B X Y : Tpoint)
    (h₁ : ¬ Col A B X ∨ ¬ Col A B Y) (h₂ : Out A X Y) : OS A B X Y := by
  rcases h₁ with hNColABX | hNColABY
  · have hNColXAB : ¬ Col X A B := fun hCol => hNColABX (by colr)
    exact out_out_one_side_c A B X X Y (one_side_reflexivity_c A B X hNColXAB) h₂
  · have hNColYAB : ¬ Col Y A B := fun hCol => hNColABY (by colr)
    exact one_side_symmetry_c A B Y X
      (out_out_one_side_c A B Y Y X (one_side_reflexivity_c A B Y hNColYAB) (l6_6_c A X Y h₂))

theorem bet__ts_c (A B X Y : Tpoint)
    (hAY : A ≠ Y) (hNCol : ¬ Col A B X) (hBet : Bet X A Y) : TS A B X Y :=
  ⟨(not_col_permutation_5_c X B A (not_col_permutation_3_c A B X hNCol)), (⟨((fun H => hNCol (col_transitivity_1_c A Y B X hAY (col_permutation_5_c A B Y (col_permutation_1_c Y A B H)) (col_permutation_1_c X A Y (bet_col_c X A Y hBet))))), (⟨A, (⟨(col_trivial_1_c A B), hBet⟩)⟩)⟩)⟩

theorem bet_ts__ts_c (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    TS A B X Z := by
  obtain ⟨hNX, hNY, T, hT1, hT2⟩ := h₁
  have hXY : X ≠ Y := by
    intro hxy
    rw [hxy] at hT2
    have hYT : Y = T := between_identity Y T hT2
    rw [← hYT] at hT1
    exact hNY hT1
  refine ⟨hNX, ?_, T, hT1, between_exchange4_c X T Y Z hT2 h₂⟩
  intro hZ
  have hZT : Z = T := l6_21_c A B X Y Z T
    (fun hc => hNX (col_permutation_2_c A B X hc)) hXY
    (col_permutation_1_c Z A B hZ) (col_permutation_1_c T A B hT1)
    (bet_col_c X Y Z h₂)
    (col_permutation_5_c X T Y (bet_col_c X T Y hT2))
  rw [hZT] at h₂
  have hYT : Y = T := between_identity Y T (between_exchange3_c X Y T Y h₂ hT2)
  rw [← hYT] at hT1
  exact hNY hT1

theorem bet_ts__os_c (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    OS A B Y Z :=
  ⟨X, (⟨(l9_2_c A B X Y h₁), (l9_2_c A B X Z (bet_ts__ts_c A B X Y Z h₁ h₂))⟩)⟩

theorem l9_31_c (A X Y Z : Tpoint) (h₁ : OS A X Y Z) (h₂ : OS A Z Y X) :
    TS A Y X Z := by
  have h1copy := h₁
  have h2copy := h₂
  obtain ⟨C, hTSAXYC, hTSAXZC⟩ := h1copy
  obtain ⟨D, hTSAZYD, _⟩ := h2copy
  obtain ⟨hNColYAX, _, _, _, _⟩ := hTSAXYC
  obtain ⟨hNColZAX, _, _, _, _⟩ := hTSAXZC
  obtain ⟨hNColYAZ, _, _, _, _⟩ := hTSAZYD
  have hAX : A ≠ X := fun e => hNColYAX (by rw [← e]; exact col_trivial_2_c Y A)
  have hAZ : A ≠ Z := fun e => hNColYAZ (by rw [← e]; exact col_trivial_2_c Y A)
  obtain ⟨Z', hBetZAZ', hCongAZ'ZA⟩ := segment_construction Z A Z A
  have hZ'A : Z' ≠ A := by
    intro e
    have hCongAAZA : Cong A A Z A := e ▸ hCongAZ'ZA
    have hCongZAAA : Cong Z A A A := cong_symmetry_c A A Z A hCongAAZA
    have hZA : Z = A := cong_identity Z A A hCongZAAA
    exact hAZ hZA.symm
  have hTSAXYZ' : TS A X Y Z' := by
    have hTSAXZZ' : TS A X Z Z' := by
      refine ⟨hNColZAX, ?_, A, col_trivial_1_c A X, hBetZAZ'⟩
      intro hColZ'AX
      have hColZAZ' : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
      have hColZ'AZ : Col Z' A Z := by colr
      have hColZ'ZX : Col Z' Z X := col_transitivity_1_c Z' A Z X hZ'A hColZ'AZ hColZ'AX
      exact hNColZAX (show Col Z A X by colr)
    exact l9_8_2_c A X Z Y Z' hTSAXZZ' (one_side_symmetry_c A X Y Z h₁)
  obtain ⟨_, hNColZ'AX, T, hColTAX, hBetYTZ'⟩ := hTSAXYZ'
  have hTA : T ≠ A := by
    intro e
    have hBetYAZ' : Bet Y A Z' := e ▸ hBetYTZ'
    have hColYAZ' : Col Y A Z' := bet_col_c Y A Z' hBetYAZ'
    have hColAZ'Y : Col A Z' Y := by colr
    have hColZAZ'2 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
    have hColAZ'Z : Col A Z' Z := by colr
    have hColAYZ : Col A Y Z := col_transitivity_1_c A Z' Y Z hZ'A.symm hColAZ'Y hColAZ'Z
    exact hNColYAZ (show Col Y A Z by colr)
  have hTY : T ≠ Y := fun e => hNColYAX (e ▸ hColTAX)
  have hOSYAZ'T : OS Y A Z' T := by
    refine out_one_side_c Y A Z' T (Or.inl ?_) (l6_6_c Y T Z' (bet_out_c Y T Z' hTY hBetYTZ'))
    intro hColYAZ'
    have hColAZ'Y : Col A Z' Y := by colr
    have hColZAZ'3 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
    have hColAZ'Z : Col A Z' Z := by colr
    have hColAYZ2 : Col A Y Z := col_transitivity_1_c A Z' Y Z hZ'A.symm hColAZ'Y hColAZ'Z
    exact hNColYAZ (show Col Y A Z by colr)
  rcases hColTAX with hBetTAX | hCaseB
  · -- Bet T A X: leads to a contradiction with h₂
    have hZZ' : Z ≠ Z' := by
      intro e
      have hBetZAZ2 : Bet Z A Z := e ▸ hBetZAZ'
      exact hAZ (between_identity Z A hBetZAZ2).symm
    have hNColZ'ZY : ¬ Col Z' Z Y := by
      intro hColZ'ZY
      have hColZZ'Y : Col Z Z' Y := by colr
      have hColZAZ'5 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
      have hColZZ'A : Col Z Z' A := by colr
      have hColZYA : Col Z Y A := col_transitivity_1_c Z Z' Y A hZZ' hColZZ'Y hColZZ'A
      exact hNColYAZ (show Col Y A Z by colr)
    have hTZ' : T ≠ Z' := by
      intro e
      have hBetZ'AX : Bet Z' A X := e ▸ hBetTAX
      exact hNColZ'AX (bet_col_c Z' A X hBetZ'AX)
    have hOSZ'ZYT : OS Z' Z Y T :=
      out_one_side_c Z' Z Y T (Or.inl hNColZ'ZY)
        (l6_6_c Z' T Y (bet_out_c Z' T Y hTZ' (between_symmetry_c Y T Z' hBetYTZ')))
    have hOSAZYT : OS A Z Y T := by
      have hColZAZ'6 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
      have hColZZ'A2 : Col Z Z' A := by colr
      have hOSZZ'YT : OS Z Z' Y T := invert_one_side_c Z' Z Y T hOSZ'ZYT
      exact invert_one_side_c Z A Y T (col_one_side_c Z Z' A Y T hColZZ'A2 hAZ.symm hOSZZ'YT)
    have hOSAZYTcopy := hOSAZYT
    have hNColXAZ : ¬ Col X A Z := by
      intro hColXAZ
      have hColAZX : Col A Z X := by colr
      have hColZAZ'7 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
      have hColAZZ' : Col A Z Z' := by colr
      have hColAXZ' : Col A X Z' := col_transitivity_1_c A Z X Z' hAZ hColAZX hColAZZ'
      exact hNColZ'AX (show Col Z' A X by colr)
    have hNColTAZ : ¬ Col T A Z := by
      obtain ⟨_, _, hTSAZTC⟩ := hOSAZYT
      exact hTSAZTC.1
    have hTSAZXT : TS A Z X T :=
      ⟨hNColXAZ, hNColTAZ, A, col_trivial_1_c A Z, between_symmetry_c T A X hBetTAX⟩
    have hTSAZYX : TS A Z Y X :=
      l9_8_2_c A Z T Y X (l9_2_c A Z X T hTSAZXT) (one_side_symmetry_c A Z Y T hOSAZYTcopy)
    exact absurd h₂ (l9_9_c A Z Y X hTSAZYX)
  · -- Bet A X T ∨ Bet X T A: the genuine case
    have hBetATXor : Bet A T X ∨ Bet A X T := by
      rcases hCaseB with hBetAXT | hBetXTA
      · exact Or.inr hBetAXT
      · exact Or.inl (between_symmetry_c X T A hBetXTA)
    have hOSAZTX : OS A Z T X := by
      refine out_one_side_c A Z T X (Or.inr ?_) ⟨hTA, hAX.symm, hBetATXor⟩
      intro hColAZX
      exact hNColZAX (show Col Z A X by colr)
    have hNColYAZ' : ¬ Col Y A Z' := by
      intro hColYAZ'
      have hColAZ'Y : Col A Z' Y := by colr
      have hColZAZ'4 : Col Z A Z' := bet_col_c Z A Z' hBetZAZ'
      have hColAZ'Z2 : Col A Z' Z := by colr
      have hColAYZ3 : Col A Y Z := col_transitivity_1_c A Z' Y Z hZ'A.symm hColAZ'Y hColAZ'Z2
      exact hNColYAZ (show Col Y A Z by colr)
    have hNColAYT : ¬ Col A Y T := by
      intro hColAYT
      have hColYTA : Col Y T A := by colr
      have hColYTZ' : Col Y T Z' := bet_col_c Y T Z' hBetYTZ'
      have hColYAZ'2 : Col Y A Z' := col_transitivity_1_c Y T A Z' hTY.symm hColYTA hColYTZ'
      exact hNColYAZ' hColYAZ'2
    have hOSAYTX : OS A Y T X :=
      out_one_side_c A Y T X (Or.inl hNColAYT) ⟨hTA, hAX.symm, hBetATXor⟩
    have hTSAYZ'Z : TS A Y Z' Z :=
      ⟨fun h => hNColYAZ' (by colr), fun h => hNColYAZ (by colr), A, col_trivial_1_c A Y,
        between_symmetry_c Z A Z' hBetZAZ'⟩
    have hOSAYZ'X : OS A Y Z' X :=
      one_side_transitivity_c A Y Z' T X (invert_one_side_c Y A Z' T hOSYAZ'T) hOSAYTX
    exact l9_8_2_c A Y Z' X Z hTSAYZ'Z hOSAYZ'X

theorem col123__nos_c (A B P Q : Tpoint) (h : Col P Q A) : ¬ OS P Q A B :=
  (fun HOne => (let H := one_side_not_col123_c P Q A B HOne; H h))

theorem col124__nos_c (A B P Q : Tpoint) (h : Col P Q B) : ¬ OS P Q A B :=
  (fun HOne => (let HN := col123__nos_c B A P Q h; HN (one_side_symmetry_c P Q A B HOne)))

theorem col2_os__os_c (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h₃ : OS A B X Y) :
    OS C D X Y := by
  obtain ⟨Z, Hts1, Hts2⟩ := h₃
  exact ⟨Z, col_preserves_two_sides_c A B C D X Z hCD h₁ h₂ Hts1, col_preserves_two_sides_c A B C D Y Z hCD h₁ h₂ Hts2⟩

theorem ts_ts_os_c (A B C D : Tpoint) (h₁ : TS A B C D) (h₂ : TS C D A B) :
    OS A C B D := by
  have h1copy := h₁
  have h2copy := h₂
  obtain ⟨hNColCAB, hNColDAB, T, hColTAB, hBetCTD⟩ := h1copy
  obtain ⟨hNColACD, hNColBCD, T1, hColT1CD, hBetAT1B⟩ := h2copy
  have hAB : A ≠ B := fun e => hNColCAB (e ▸ col_trivial_2_c C A)
  have hNColCDA : ¬ Col C D A := fun hc => hNColACD (by colr)
  have hColCDT1 : Col C D T1 := by colr
  have hColCTD : Col C T D := bet_col_c C T D hBetCTD
  have hColCDT : Col C D T := by colr
  have hColAT1B : Col A T1 B := bet_col_c A T1 B hBetAT1B
  have hColABT1 : Col A B T1 := by colr
  have hColABT : Col A B T := by colr
  have hT1eqT : T1 = T := l6_21_c C D A B T1 T hNColCDA hAB hColCDT1 hColCDT hColABT1 hColABT
  have hBetATB : Bet A T B := hT1eqT ▸ hBetAT1B
  have hOSACTB : OS A C T B := by
    refine out_one_side_c A C T B (Or.inr ?_) ?_
    · intro hColACB
      exact hNColCAB (show Col C A B by colr)
    · refine ⟨?_, ?_, Or.inl hBetATB⟩
      · intro e
        have hBetCAD : Bet C A D := e ▸ hBetCTD
        have hColCAD : Col C A D := bet_col_c C A D hBetCAD
        exact hNColACD (show Col A C D by colr)
      · exact fun e => hNColCAB (e ▸ col_trivial_2_c C A)
  have hOSCATD : OS C A T D := by
    refine out_one_side_c C A T D (Or.inr ?_) ?_
    · intro hColCAD
      exact hNColACD (show Col A C D by colr)
    · refine ⟨?_, ?_, Or.inl hBetCTD⟩
      · exact fun e => hNColCAB (e ▸ hColTAB)
      · exact fun e => hNColBCD (e ▸ col_trivial_2_c B C)
  have hOSACTD : OS A C T D := invert_one_side_c C A T D hOSCATD
  exact one_side_transitivity_c A C B T D (one_side_symmetry_c A C T B hOSACTB) hOSACTD

theorem two_sides_not_col_c (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A B X := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  intro H2
  exact H0 (col_permutation_2_c A B X H2)

theorem col_one_side_out_c (A B X Y : Tpoint) (hCol : Col A X Y) (h : OS A B X Y) :
    Out A X Y := by
  have hcopy := h
  obtain ⟨Z, hTSX, hTSY⟩ := hcopy
  obtain ⟨hNColXAB, hNColZAB, T1, hColT1, hBetT1⟩ := hTSX
  obtain ⟨hNColYAB, hNColZAB2, T2, hColT2, hBetT2⟩ := hTSY
  have hXA : X ≠ A := (not_col_distincts_c X A B hNColXAB).2.1
  have hYA : Y ≠ A := (not_col_distincts_c Y A B hNColYAB).2.1
  rcases hCol with hBetAXY | hBetXYA | hBetYAX
  · exact ⟨hXA, hYA, Or.inl hBetAXY⟩
  · exact ⟨hXA, hYA, Or.inr (between_symmetry_c X Y A hBetXYA)⟩
  · exfalso
    have hTS : TS A B X Y :=
      ⟨hNColXAB, hNColYAB, A, col_trivial_1_c A B, between_symmetry_c Y A X hBetYAX⟩
    exact l9_9_c A B X Y hTS h

theorem col_two_sides_bet_c (A B X Y : Tpoint)
    (hCol : Col A X Y) (h : TS A B X Y) : Bet X A Y := by
  obtain ⟨hNColXAB, hNColYAB, T, hColTAB, hBetXTY⟩ := h
  rcases hCol with hCase1 | hCase2 | hCase3
  · exfalso
    have hBetAXT : Bet A X T := between_inner_transitivity_c A X T Y hCase1 hBetXTY
    have hColAXT : Col A X T := bet_col_c A X T hBetAXT
    rcases point_equality_decidability A T with hAT | hAT
    · have hBetAXA : Bet A X A := hAT ▸ hBetAXT
      have hAX : A = X := between_identity A X hBetAXA
      exact hNColXAB (hAX ▸ col_trivial_1_c A B)
    · have hColATX : Col A T X := by show Col A T X; colr
      have hColATB : Col A T B := by show Col A T B; colr
      have hColAXB : Col A X B := col_transitivity_1_c A T X B hAT hColATX hColATB
      exact hNColXAB (show Col X A B by colr)
  · exfalso
    have hBetTYA : Bet T Y A := between_exchange3_c X T Y A hBetXTY hCase2
    have hColTYA : Col T Y A := bet_col_c T Y A hBetTYA
    rcases point_equality_decidability T A with hTA | hTA
    · have hYA : Y = A := by
        have hBetTYT : Bet T Y T := hTA ▸ hBetTYA
        have hTY : T = Y := between_identity T Y hBetTYT
        exact hTY.symm.trans hTA
      exact hNColYAB (hYA ▸ col_trivial_1_c A B)
    · have hColTAY : Col T A Y := by show Col T A Y; colr
      have hColTAB2 : Col T A B := hColTAB
      have hColTYB : Col T Y B := col_transitivity_1_c T A Y B hTA hColTAY hColTAB2
      exact hNColYAB (show Col Y A B by colr)
  · exact between_symmetry_c Y A X hCase3

theorem os_ts1324__os_c (A X Y Z : Tpoint)
    (h₁ : OS A X Y Z) (h₂ : TS A Y X Z) : OS A Z X Y := by
  obtain ⟨HNColXY, HNColYZ, P, HColP, HPBet⟩ := h₂
  have hNotColAXZ : ¬ Col A X Z := one_side_not_col123_c A X Z Y (one_side_symmetry_c A X Y Z h₁)
  have hPZ : P ≠ Z := fun hEq => HNColYZ (hEq ▸ HColP)
  have hPX : P ≠ X := fun hEq => HNColXY (hEq ▸ HColP)
  have hZAPX : OS Z A P X :=
    out_one_side_c Z A P X (Or.inr (fun hc => hNotColAXZ (col_permutation_1_c Z A X hc)))
      (bet_out_c Z P X hPZ (between_symmetry_c X P Z HPBet))
  have hZAXP : OS Z A X P := one_side_symmetry_c Z A P X hZAPX
  have sub1 : OS A Z X P := invert_one_side_c Z A X P hZAXP
  have hXAPZ : OS X A P Z :=
    out_one_side_c X A P Z (Or.inr (fun hc => hNotColAXZ (col_permutation_4_c X A Z hc)))
      (bet_out_c X P Z hPX HPBet)
  have sub2a : OS A X P Z := invert_one_side_c X A P Z hXAPZ
  have sub2b : OS A X Z Y := one_side_symmetry_c A X Y Z h₁
  have hAXPY : OS A X P Y := one_side_transitivity_c A X P Z Y sub2a sub2b
  have hAPY : Out A P Y := col_one_side_out_c A X P Y (col_permutation_4_c P A Y HColP) hAXPY
  have sub2 : OS A Z P Y :=
    out_one_side_c A Z P Y (Or.inr (fun hc => HNColYZ (col_permutation_4_c A Z Y hc))) hAPY
  exact one_side_transitivity_c A Z X P Y sub1 sub2

theorem ts2__ex_bet2_c (A B C D : Tpoint) (h₁ : TS A C B D) (h₂ : TS B D A C) :
    ∃ X, Bet A X C ∧ Bet B X D := by
  obtain ⟨hNColBAC, hNColDAC, X, hCol, hBet⟩ := h₁
  refine ⟨X, ?_, hBet⟩
  have hColBDX : Col B D X := by
    have h := bet_col_c B X D hBet
    show Col B D X; colr
  have hBX : B ≠ X := fun e => hNColBAC (e ▸ hCol)
  have hStep : TS B X A C := col_two_sides_c B D X A C hColBDX hBX h₂
  obtain ⟨hNColABX, hNColCBX, T, hColTBX, hBetATC⟩ := hStep
  have hTSXBAC : TS X B A C :=
    ⟨fun h => hNColABX (by colr), fun h => hNColCBX (by colr), T, (by show Col T X B; colr), hBetATC⟩
  exact col_two_sides_bet_c X B A C hCol hTSXBAC

theorem out_one_side_1_c (A B C D X : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (hOut : Out X C D) :
    OS A B C D := by
  rcases point_equality_decidability C D with hCD | hCD
  · have hNColCAB : ¬ Col C A B := fun h => hNCol (by colr)
    exact hCD ▸ one_side_reflexivity_c A B C hNColCAB
  · obtain ⟨C', hBetCXC', hCongXC'CX⟩ := segment_construction C X C X
    have hCX : C ≠ X := fun e => hNCol (e ▸ hCol)
    have hColXCD : Col X C D := out_col_c X C D hOut
    have hColCXD : Col C X D := by show Col C X D; colr
    have hColCDX : Col C D X := by show Col C D X; colr
    have hColCXC' : Col C X C' := bet_col_c C X C' hBetCXC'
    have hColCDC' : Col C D C' := colx_c C X C' C D hCX (col_trivial_3_c C D) hColCDX hColCXC'
    have hNColC'AB : ¬ Col C' A B := by
      intro hColC'AB
      have hEqC'X : C' = X :=
        l6_21_c A B C D C' X hNCol hCD (show Col A B C' by colr) hCol hColCDC' hColCDX
      have hCongXXCX : Cong X X C X := hEqC'X ▸ hCongXC'CX
      have hEqCX : C = X := cong_identity C X X (cong_symmetry_c X X C X hCongXXCX)
      exact hOut.1 hEqCX
    have hNColCAB2 : ¬ Col C A B := fun h => hNCol (by colr)
    have hTSACC' : TS A B C C' := ⟨hNColCAB2, hNColC'AB, X, (show Col X A B by colr), hBetCXC'⟩
    have hTSADC' : TS A B D C' := l9_5_c A B C C' X D hTSACC' (show Col X A B by colr) hOut
    exact ⟨C', hTSACC', hTSADC'⟩

theorem out_two_sides_two_sides_c (A B X Y P PX : Tpoint)
    (hA_PX : A ≠ PX) (hCol : Col A B PX) (hOut : Out PX X P)
    (h : TS A B P Y) : TS A B X Y := by
  have hcopy := h
  obtain ⟨hNColPAB, hNColYAB, T, hColTAB, hBetPTY⟩ := hcopy
  have hAB : A ≠ B := (not_col_distincts_c P A B hNColPAB).2.2.1
  have hColAPXB : Col A PX B := by show Col A PX B; colr
  have hOSPXAPX : OS PX A P X := by
    refine out_one_side_c PX A P X ?_ (l6_6_c PX X P hOut)
    left
    intro hColPXAP
    have hColAPXP : Col A PX P := by show Col A PX P; colr
    have hColABP : Col A B P := col_transitivity_1_c A PX B P hA_PX hColAPXB hColAPXP
    exact hNColPAB (show Col P A B by colr)
  have hOSAPXPX : OS A PX P X := invert_one_side_c PX A P X hOSPXAPX
  have hOSABPX : OS A B P X := col_one_side_c A PX B P X hColAPXB hAB hOSAPXPX
  exact l9_8_2_c A B P X Y h hOSABPX

theorem l8_21_bis_c (A B C X Y : Tpoint)
    (hXY : X ≠ Y) (hNCol : ¬ Col C A B) :
    ∃ P : Tpoint, Cong A P X Y ∧ Perp A B P A ∧ TS A B C P := by
  have hAB : A ≠ B := by
    intro hEq; subst hEq; exact hNCol (col_trivial_2_c C A)
  obtain ⟨P, T, hPerpABPA, hColABT, hBetCTP⟩ := l8_21_c A B C hAB
  have hTSABCP : TS A B C P :=
    ⟨hNCol, fun hc => perp_not_col_c A B P hPerpABPA (col_permutation_1_c P A B hc),
      T, col_permutation_2_c A B T hColABT, hBetCTP⟩
  have hPA : P ≠ A := (perp_distinct_c A B P A hPerpABPA).2
  obtain ⟨P', hBetOr, hCongAP'XY⟩ := segment_construction_2_c P A X Y hPA
  have hAP' : A ≠ P' := by
    intro hEq
    apply hXY
    have hCongAAXY : Cong A A X Y := hEq ▸ hCongAP'XY
    exact cong_identity X Y A (cong_symmetry_c A A X Y hCongAAXY)
  have hColAPP' : Col A P P' := by
    rcases hBetOr with hBet | hBet
    · exact bet_col_c A P P' hBet
    · exact col_permutation_5_c A P' P (bet_col_c A P' P hBet)
  have step_a : Perp P A A B := perp_sym_c A B P A hPerpABPA
  have step_b : Perp A P A B := perp_left_comm_c P A A B step_a
  have step_c : Perp A P' A B := perp_col_c A P A B P' hAP' step_b hColAPP'
  have step_d : Perp A B A P' := perp_sym_c A P' A B step_c
  have finalPerp : Perp A B P' A := perp_right_comm_c A B A P' step_d
  have hNColP'AB : ¬ Col P' A B :=
    fun hc => perp_not_col_c A B P' finalPerp (col_permutation_1_c P' A B hc)
  have hOutAPP' : Out A P P' := ⟨hPA, hAP'.symm, hBetOr⟩
  have hOSABPP' : OS A B P P' :=
    out_one_side_c A B P P' (Or.inl (perp_not_col_c A B P hPerpABPA)) hOutAPP'
  have hTSABPC : TS A B P C := l9_2_c A B C P hTSABCP
  have hTSABP'C : TS A B P' C := l9_8_2_c A B P P' C hTSABPC hOSABPP'
  have hTSABCP' : TS A B C P' := l9_2_c A B P' C hTSABP'C
  obtain ⟨-, -, T', hColT'AB, hBetCT'P'⟩ := hTSABCP'
  exact ⟨P', hCongAP'XY, finalPerp, hNCol, hNColP'AB, T', hColT'AB, hBetCT'P'⟩

theorem ts__ncol_c (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A X Y ∨ ¬ Col B X Y := by
  obtain ⟨hNX, hNY, T, hTC, hBet⟩ := h
  rcases eq_dec_points_c X T with hXT | hXT
  · rw [← hXT] at hTC
    exact absurd hTC hNX
  · have hXY : X ≠ Y := by
      intro hxy
      rw [← hxy] at hBet
      exact hXT (between_identity X T hBet)
    rcases eq_dec_points_c A T with hAT | hAT
    · refine Or.inr (fun hCol => hNX ?_)
      rw [← hAT] at hBet
      exact col_transitivity_1_c X Y A B hXY
        (col_permutation_5_c X A Y (bet_col_c X A Y hBet))
        (col_permutation_1_c B X Y hCol)
    · refine Or.inl (fun hCol => hNX ?_)
      have c3 : Col X T A := col_transitivity_1_c X Y T A hXY
        (col_permutation_5_c X T Y (bet_col_c X T Y hBet))
        (col_permutation_1_c A X Y hCol)
      have c4 : Col T X B := col_transitivity_1_c T A X B (Ne.symm hAT)
        (col_permutation_1_c X T A c3) hTC
      exact col_transitivity_1_c X T A B hXT c3 (col_permutation_4_c T X B c4)

theorem one_or_two_sides_aux_c (A B C D X : Tpoint)
    (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (h₁ : Col A C X) (h₂ : Col B D X) : TS A B C D ∨ OS A B C D := by
  have hCA : C ≠ A := (not_col_distincts_c C A B hNC1).2.1
  have hDB : D ≠ B := (not_col_distincts_c D A B hNC2).2.2.2
  have hAX : A ≠ X := fun e => hNC2 (by
    have hColBDA : Col B D A := e ▸ h₂
    show Col D A B; colr)
  have hBX : B ≠ X := fun e => hNC1 (by
    have hColACB : Col A C B := e ▸ h₁
    show Col C A B; colr)
  have hNColXAB : ¬ Col X A B := by
    intro hColXAB
    have hColAXC : Col A X C := by colr
    have hColAXB : Col A X B := by colr
    have hColACB : Col A C B := col_transitivity_1_c A X C B hAX hColAXC hColAXB
    exact hNC1 (show Col C A B by colr)
  rcases h₁ with hBetACX | hBetCXA | hBetXAC
  · rcases h₂ with hBetBDX | hBetDXB | hBetXBD
    · exact Or.inr (one_side_transitivity_c A B C X D
        (out_one_side_c A B C X (Or.inr (fun hh => hNColXAB (by colr))) (bet_out_c A C X hCA hBetACX))
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (l6_6_c B D X (bet_out_c B D X hDB hBetBDX)))))
    · exact Or.inr (one_side_transitivity_c A B C X D
        (out_one_side_c A B C X (Or.inr (fun hh => hNColXAB (by colr))) (bet_out_c A C X hCA hBetACX))
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (bet_out_c B X D hBX.symm (between_symmetry_c D X B hBetDXB)))))
    · exact Or.inl (l9_8_2_c A B X C D
        ⟨hNColXAB, hNC2, B, col_trivial_3_c B A, hBetXBD⟩
        (out_one_side_c A B X C (Or.inr (fun hh => hNC1 (by colr)))
          (l6_6_c A C X (bet_out_c A C X hCA hBetACX))))
  · rcases h₂ with hBetBDX | hBetDXB | hBetXBD
    · exact Or.inr (one_side_transitivity_c A B C X D
        (out_one_side_c A B C X (Or.inr (fun hh => hNColXAB (by colr)))
          (l6_6_c A X C (bet_out_c A X C hAX.symm (between_symmetry_c C X A hBetCXA))))
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (l6_6_c B D X (bet_out_c B D X hDB hBetBDX)))))
    · exact Or.inr (one_side_transitivity_c A B C X D
        (out_one_side_c A B C X (Or.inr (fun hh => hNColXAB (by colr)))
          (l6_6_c A X C (bet_out_c A X C hAX.symm (between_symmetry_c C X A hBetCXA))))
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (bet_out_c B X D hBX.symm (between_symmetry_c D X B hBetDXB)))))
    · exact Or.inl (l9_8_2_c A B X C D
        ⟨hNColXAB, hNC2, B, col_trivial_3_c B A, hBetXBD⟩
        (out_one_side_c A B X C (Or.inr (fun hh => hNC1 (by colr)))
          (bet_out_c A X C hAX.symm (between_symmetry_c C X A hBetCXA))))
  · rcases h₂ with hBetBDX | hBetDXB | hBetXBD
    · exact Or.inl (l9_2_c A B D C (l9_8_2_c A B X D C
        ⟨hNColXAB, hNC1, A, col_trivial_1_c A B, hBetXAC⟩
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (l6_6_c B D X (bet_out_c B D X hDB hBetBDX))))))
    · exact Or.inl (l9_2_c A B D C (l9_8_2_c A B X D C
        ⟨hNColXAB, hNC1, A, col_trivial_1_c A B, hBetXAC⟩
        (invert_one_side_c B A X D (out_one_side_c B A X D (Or.inr (fun hh => hNC2 (by colr)))
          (bet_out_c B X D hBX.symm (between_symmetry_c D X B hBetDXB))))))
    · exact Or.inr ⟨X,
        ⟨hNC1, hNColXAB, A, col_trivial_1_c A B, between_symmetry_c X A C hBetXAC⟩,
        ⟨hNC2, hNColXAB, B, col_trivial_3_c B A, between_symmetry_c X B D hBetXBD⟩⟩

theorem cop__one_or_two_sides_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B) :
    TS A B C D ∨ OS A B C D := by
  obtain ⟨X, H2⟩ := hCop
  rcases H2 with H3 | H3
  · obtain ⟨H4, H5⟩ := H3
    have o := or_bet_out_c C X D
    rcases o with x | x
    · exact Or.inl (⟨hNC1, (⟨hNC2, (⟨X, (⟨(col_permutation_5_c X B A (col_permutation_3_c A B X H4)), x⟩)⟩)⟩)⟩)
    · rcases x with x0 | x0
      · exact Or.inr (out_one_side_1_c A B C D X (not_col_permutation_5_c A C B (not_col_permutation_4_c C A B hNC1)) H4 x0)
      · exact ((x0 (col_permutation_5_c C D X H5))).elim
  · rcases H3 with H4 | H4
    · obtain ⟨H5, H6⟩ := H4
      exact one_or_two_sides_aux_c A B C D X hNC1 hNC2 H5 H6
    · obtain ⟨H5, H6⟩ := H4
      have o := one_or_two_sides_aux_c A B D C X hNC2 hNC1 H5 H6
      rcases o with H7 | H7
      · exact Or.inl (l9_2_c A B D C H7)
      · exact Or.inr (one_side_symmetry_c A B D C H7)

theorem os__coplanar_c (A B C D : Tpoint) (h : OS A B C D) :
    Coplanar A B C D := by
  have HOS := h
  have HNCol : ¬ Col A B C := one_side_not_col123_c A B C D HOS
  have hBC : B ≠ C := (not_col_distincts_c A B C HNCol).2.2.1
  obtain ⟨C', hBetCBC', hCongBC'BC⟩ := segment_construction C B B C
  have hBC' : B ≠ C' := cong_diff_3_c B C' B C hBC hCongBC'BC
  have hTSABCC' : TS A B C C' := by
    refine ⟨fun hh => HNCol (by colr), ?_, B, col_trivial_3_c B A, hBetCBC'⟩
    intro hColC'AB
    have hColCBC' : Col C B C' := bet_col_c C B C' hBetCBC'
    have hColBC'C : Col B C' C := by colr
    have hColBC'A : Col B C' A := by colr
    have hColBCA : Col B C A := col_transitivity_1_c B C' C A hBC' hColBC'C hColBC'A
    exact HNCol (show Col A B C by colr)
  have hHT : TS A B D C' := l9_8_2_c A B C D C' hTSABCC' HOS
  obtain ⟨hNCol1, hNCol2, T, hColTAB, hBetDTC'⟩ := hHT
  have hC'T : C' ≠ T := fun e => hNCol2 (e ▸ hColTAB)
  rcases col_dec_c T B C with hColTBC | hNCol3
  · -- Col T B C
    have hNColBAC : ¬ Col B A C := fun hh => HNCol (by colr)
    have hCB : C ≠ B := hBC.symm
    have hTeqB : T = B := l6_21_c B A C B T B hNColBAC hCB
      (by colr : Col B A T) (col_trivial_3_c B A) (by colr : Col C B T) (col_trivial_2_c C B)
    have hBetDBC' : Bet D B C' := hTeqB ▸ hBetDTC'
    have hColBC'D : Col B C' D := by
      have hh := bet_col_c D B C' hBetDBC'
      show Col B C' D; colr
    have hColBC'C2 : Col B C' C := by
      have hh := bet_col_c C B C' hBetCBC'
      show Col B C' C; colr
    have hColBDC : Col B D C := col_transitivity_1_c B C' D C hBC' hColBC'D hColBC'C2
    exact ⟨B, Or.inl ⟨col_trivial_2_c A B, show Col C D B by colr⟩⟩
  · -- ¬ Col T B C
    have hDC' : D ≠ C' := by
      intro e
      have hBetDTD : Bet D T D := e ▸ hBetDTC'
      have hDT : D = T := between_identity D T hBetDTD
      exact hNCol1 (hDT ▸ hColTAB)
    have hColBCC' : Col B C C' := by
      have hh := bet_col_c C B C' hBetCBC'
      show Col B C C'; colr
    rcases bet_dec_c T B A with hBetTBA | hNBetTBA
    · -- Bet T B A
      refine coplanar_perm_18_c B C D A (ts__coplanar_c B C D A ?_)
      have hTSBCTA : TS B C T A :=
        ⟨hNCol3, HNCol, B, col_trivial_1_c B C, hBetTBA⟩
      have hOSBCTD : OS B C T D :=
        out_one_side_1_c B C T D C' (fun hh => hNCol3 (by colr)) hColBCC'
          (bet_out_c C' T D hC'T.symm (between_symmetry_c D T C' hBetDTC'))
      exact l9_8_2_c B C T D A hTSBCTA hOSBCTD
    · -- ¬ Bet T B A
      refine coplanar_perm_19_c B D C A (ts__coplanar_c B D C A ?_)
      have hColDC'T : Col D C' T := by
        have hh := bet_col_c D T C' hBetDTC'
        show Col D C' T; colr
      have hNColBCD : ¬ Col B C D := by
        intro hColBCD
        have hColBCT : Col B C T := colx_c D C' T B C hDC' hColBCD hColBCC' hColDC'T
        exact hNCol3 (show Col T B C by colr)
      have hOSBCDT : OS B C D T :=
        out_one_side_1_c B C D T C' (fun hh => hNColBCD hh) hColBCC'
          (l6_6_c C' T D (bet_out_c C' T D hC'T.symm (between_symmetry_c D T C' hBetDTC')))
      have hColTBA : Col T B A := by colr
      have hOSBCTA : OS B C T A :=
        out_one_side_c B C T A (Or.inr (fun hh => HNCol (by colr)))
          (not_bet_out_c T B A hColTBA hNBetTBA)
      have hOSBCDA : OS B C D A := one_side_transitivity_c B C D T A hOSBCDT hOSBCTA
      exact l9_31_c B C D A hOSBCDA (one_side_symmetry_c B A C D (invert_one_side_c A B C D HOS))

theorem coplanar_trans_1_c (P Q R A B : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B) :
    Coplanar Q R A B := by
  rcases col_dec_c Q R A with hColQRA | hNColQRA
  · exact ⟨A, Or.inl ⟨hColQRA, col_trivial_3_c A B⟩⟩
  · rcases col_dec_c Q R B with hColQRB | hNColQRB
    · exact ⟨B, Or.inl ⟨hColQRB, col_trivial_2_c A B⟩⟩
    · rcases col_dec_c Q A B with hColQAB | hNColQAB
      · exact ⟨Q, Or.inl ⟨col_trivial_3_c Q R, by colr⟩⟩
      · have hA : TS Q R P A ∨ OS Q R P A :=
          cop__one_or_two_sides_c Q R P A (coplanar_perm_8_c P Q R A h₁) hNCol
            (fun hh => hNColQRA (by colr))
        have hB : TS Q R P B ∨ OS Q R P B :=
          cop__one_or_two_sides_c Q R P B (coplanar_perm_8_c P Q R B h₂) hNCol
            (fun hh => hNColQRB (by colr))
        have hDij : TS Q R A B ∨ OS Q R A B := by
          rcases hA with hA_TS | hA_OS
          · rcases hB with hB_TS | hB_OS
            · exact Or.inr (l9_8_1_c Q R A B P (l9_2_c Q R P A hA_TS) (l9_2_c Q R P B hB_TS))
            · exact Or.inl (l9_2_c Q R B A (l9_8_2_c Q R P B A hA_TS hB_OS))
          · rcases hB with hB_TS | hB_OS
            · exact Or.inl (l9_8_2_c Q R P A B hB_TS hA_OS)
            · exact Or.inr (one_side_transitivity_c Q R A P B (one_side_symmetry_c Q R P A hA_OS) hB_OS)
        rcases hDij with hTS | hOS
        · exact ts__coplanar_c Q R A B hTS
        · exact os__coplanar_c Q R A B hOS

theorem col_cop__cop_c (A B C D E : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D) (hCol : Col C D E) :
    Coplanar A B C E := by
  rcases col_dec_c D A C with hColDAC | hNColDAC
  · have hColECD : Col E C D := by colr
    have hColACD : Col A C D := by colr
    have hColACE : Col A C E := l6_16_1_c C D E A hCD hColECD hColACD
    exact coplanar_perm_4_c A C E B (col__coplanar_c A C E B hColACE)
  · have hColDCE : Col D C E := by colr
    have hCop1 : Coplanar D A C B := coplanar_perm_19_c A B C D hCop
    have hCop2 : Coplanar D A C E := coplanar_perm_4_c D C E A (col__coplanar_c D C E A hColDCE)
    exact coplanar_perm_2_c A C B E (coplanar_trans_1_c D A C B E hNColDAC hCop1 hCop2)

theorem bet_cop__cop_c (A B C D E : Tpoint)
    (hCop : Coplanar A B C E) (hBet : Bet C D E) : Coplanar A B C D := by
  have o := point_equality_decidability C E
  rcases o with x | x
  · subst x
    have HBet1 := between_identity C D hBet
    subst HBet1
    exact hCop
  · exact col_cop__cop_c A B C E D hCop x (col_permutation_5_c C D E (bet_col_c C D E hBet))

theorem col2_cop__cop_c (A B C D E F : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D)
    (h₁ : Col C D E) (h₂ : Col C D F) : Coplanar A B E F := by
  rcases point_equality_decidability E C with hEC | hEC
  · exact hEC ▸ col_cop__cop_c A B C D F hCop hCD h₂
  · have hColFCD : Col F C D := by colr
    have hColECD : Col E C D := by colr
    have hColECF : Col E C F := l6_16_1_c C D F E hCD hColFCD hColECD
    exact col_cop__cop_c A B E C F
      (coplanar_perm_1_c A B C E (col_cop__cop_c A B C D E hCop hCD h₁)) hEC hColECF

theorem col_cop2__cop_c (A B C U V P : Tpoint)
    (hUV : U ≠ V) (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C V)
    (hCol : Col U V P) : Coplanar A B C P := by
  rcases col_dec_c A B C with hColABC | hNColABC
  · exact col__coplanar_c A B C P hColABC
  · have Haux : ∀ A B C : Tpoint, ¬ Col A B C → ¬ Col U A B →
        Coplanar A B C U → Coplanar A B C V → Coplanar A B C P := by
      intro A B C HNCol HNCol' HU HV
      have hCUAB : Coplanar U A B C := coplanar_perm_18_c A B C U HU
      have hInner2 : Coplanar A B U V :=
        coplanar_trans_1_c C A B U V (fun hh => HNCol (by colr))
          (coplanar_perm_12_c A B C U HU) (coplanar_perm_12_c A B C V HV)
      have hABUP : Coplanar A B U P := col_cop__cop_c A B U V P hInner2 hUV hCol
      exact coplanar_trans_1_c U A B C P HNCol' hCUAB (coplanar_perm_12_c A B U P hABUP)
    rcases col_dec_c U A B with hColUAB | hNColUAB
    · rcases col_dec_c U A C with hColUAC | hNColUAC
      · have hNColUBC : ¬ Col U B C := by
          intro hColUBC
          rcases point_equality_decidability U A with hUA | hUA
          · exact hNColABC (hUA ▸ hColUBC)
          · have hColAUB : Col A U B := by colr
            have hColAUC : Col A U C := by colr
            exact hNColABC (col_transitivity_1_c A U B C hUA.symm hColAUB hColAUC)
        exact coplanar_perm_12_c B C A P (Haux B C A
          (fun hh => hNColABC (by colr)) hNColUBC
          (coplanar_perm_8_c A B C U h₁) (coplanar_perm_8_c A B C V h₂))
      · exact coplanar_perm_2_c A C B P (Haux A C B
          (fun hh => hNColABC (by colr)) hNColUAC
          (coplanar_perm_2_c A B C U h₁) (coplanar_perm_2_c A B C V h₂))
    · exact Haux A B C hNColABC hNColUAB h₁ h₂

theorem bet_cop2__cop_c (A B C U V W : Tpoint)
    (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C W) (hBet : Bet U V W) :
    Coplanar A B C V := by
  have o := point_equality_decidability U W
  rcases o with x | x
  · subst x
    have HBet1 := between_identity U V hBet
    subst HBet1
    exact h₁
  · exact col_cop2__cop_c A B C U W V x h₁ h₂ (col_permutation_5_c U V W (bet_col_c U V W hBet))

theorem coplanar_pseudo_trans_c (A B C D P Q R : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B)
    (h₃ : Coplanar P Q R C) (h₄ : Coplanar P Q R D) :
    Coplanar A B C D := by
  have Haux : ∀ P Q R A B C : Tpoint, ¬ Col P Q R →
      Coplanar P Q R A → Coplanar P Q R B → Coplanar P Q R C → Coplanar A B C R := by
    intro P Q R A B C HNC HCop1 HCop2 HCop3
    rcases col_dec_c R Q A with hColRQA | hNColRQA
    · have hRQ : R ≠ Q := (not_col_distincts_c P Q R HNC).2.2.1.symm
      have hInner : Coplanar Q R B C := coplanar_trans_1_c P Q R B C HNC HCop2 HCop3
      have hBCRQ : Coplanar B C R Q := coplanar_perm_17_c Q R B C hInner
      exact coplanar_perm_18_c B C R A (col_cop__cop_c B C R Q A hBCRQ hRQ hColRQA)
    · have hNColQRA : ¬ Col Q R A := fun hh => hNColRQA (by colr)
      have hCopQRAB : Coplanar Q R A B := coplanar_trans_1_c P Q R A B HNC HCop1 HCop2
      have hCopQRAC : Coplanar Q R A C := coplanar_trans_1_c P Q R A C HNC HCop1 HCop3
      have hRABC : Coplanar R A B C := coplanar_trans_1_c Q R A B C hNColQRA hCopQRAB hCopQRAC
      exact coplanar_perm_9_c R A B C hRABC
  rcases col_dec_c P Q D with hColPQD | hNColPQD
  · have hPQ : P ≠ Q := (not_col_distincts_c P Q R hNCol).2.1
    have hNColQRP : ¬ Col Q R P := fun hh => hNCol (by colr)
    have hCopAP : Coplanar A B C P :=
      Haux Q R P A B C hNColQRP
        (coplanar_perm_8_c P Q R A h₁) (coplanar_perm_8_c P Q R B h₂) (coplanar_perm_8_c P Q R C h₃)
    have hNColPRQ : ¬ Col P R Q := fun hh => hNCol (by colr)
    have hCopAQ : Coplanar A B C Q :=
      Haux P R Q A B C hNColPRQ
        (coplanar_perm_2_c P Q R A h₁) (coplanar_perm_2_c P Q R B h₂) (coplanar_perm_2_c P Q R C h₃)
    exact col_cop2__cop_c A B C P Q D hPQ hCopAP hCopAQ hColPQD
  · have hNColRPQ : ¬ Col R P Q := fun hh => hNCol (by colr)
    have hCopPQDA : Coplanar P Q D A :=
      coplanar_trans_1_c R P Q D A hNColRPQ (coplanar_perm_12_c P Q R D h₄) (coplanar_perm_12_c P Q R A h₁)
    have hCopPQDB : Coplanar P Q D B :=
      coplanar_trans_1_c R P Q D B hNColRPQ (coplanar_perm_12_c P Q R D h₄) (coplanar_perm_12_c P Q R B h₂)
    have hCopPQDC : Coplanar P Q D C :=
      coplanar_trans_1_c R P Q D C hNColRPQ (coplanar_perm_12_c P Q R D h₄) (coplanar_perm_12_c P Q R C h₃)
    exact Haux P Q D A B C hNColPQD hCopPQDA hCopPQDB hCopPQDC

theorem l9_30_c (A B C D E F P X Y Z : Tpoint)
    (hNCopP : ¬ Coplanar A B C P) (hNColDEF : ¬ Col D E F)
    (hCopDEF_P : Coplanar D E F P)
    (h₁ : Coplanar A B C X) (h₂ : Coplanar A B C Y) (h₃ : Coplanar A B C Z)
    (h₄ : Coplanar D E F X) (h₅ : Coplanar D E F Y) (h₆ : Coplanar D E F Z) :
    Col X Y Z := by
  rcases col_dec_c X Y Z with hCol | hNCol
  · exact hCol
  · exfalso
    have hNColABC : ¬ Col A B C := ncop__ncol_c A B C P hNCopP
    have hCopXYZA : Coplanar X Y Z A :=
      coplanar_pseudo_trans_c X Y Z A A B C hNColABC h₁ h₂ h₃
        ⟨A, Or.inl ⟨col_trivial_3_c A B, col_trivial_2_c C A⟩⟩
    have hCopXYZB : Coplanar X Y Z B :=
      coplanar_pseudo_trans_c X Y Z B A B C hNColABC h₁ h₂ h₃
        ⟨B, Or.inl ⟨col_trivial_2_c A B, col_trivial_2_c C B⟩⟩
    have hCopXYZC : Coplanar X Y Z C :=
      coplanar_pseudo_trans_c X Y Z C A B C hNColABC h₁ h₂ h₃
        ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c A C, col_trivial_2_c B C⟩)⟩
    have hCopXYZP : Coplanar X Y Z P :=
      coplanar_pseudo_trans_c X Y Z P D E F hNColDEF h₄ h₅ h₆ hCopDEF_P
    exact hNCopP (coplanar_pseudo_trans_c A B C P X Y Z hNCol hCopXYZA hCopXYZB hCopXYZC hCopXYZP)

theorem cop_per2__col_c (A X Y Z : Tpoint)
    (hCop : Coplanar A X Y Z) (hAZ : A ≠ Z)
    (h₁ : Per X Z A) (h₂ : Per Y Z A) : Col X Y Z := by
  obtain ⟨B', hMid1, hCong1⟩ := h₁
  obtain ⟨B, hMid2, hCong2⟩ := h₂
  have hBB' : B = B' := symmetric_point_uniqueness_c A Z B B' hMid2 hMid1
  subst hBB'
  have hABFalse : A = B → False := fun hAB => hAZ (l7_3_c Z A (hAB ▸ hMid1)).symm
  rcases point_equality_decidability X Y with hXY | hXY
  · subst hXY
    exact col_trivial_1_c X Z
  · rcases point_equality_decidability X Z with hXZ | hXZ
    · subst hXZ
      exact col_trivial_3_c X Y
    · rcases point_equality_decidability Y Z with hYZ | hYZ
      · subst hYZ
        exact col_trivial_2_c X Y
      · obtain ⟨I, hDisj⟩ := hCop
        have Haux : ∀ W : Tpoint, Cong W A W B → Col A W I → W ≠ I →
            Cong I A I B → False := by
          intro W hCongW hColAWI hWI hCong3
          have hAI : A ≠ I := by
            intro hEq
            subst hEq
            exact hABFalse (cong_identity A B A (cong_symmetry_c A A A B hCong3))
          have hWA : W ≠ A := by
            intro hEq
            exact hABFalse (cong_identity A B A (cong_symmetry_c A A A B (hEq ▸ hCongW)))
          have hCongAWBW : Cong A W B W := cong_commutativity_c W A W B hCongW
          rcases hColAWI with hBet1 | hBet1 | hBet1
          · -- Bet A W I
            have hOutAWI : Out A W I := ⟨hWA, hAI.symm, Or.inl hBet1⟩
            have hLe1 : Le A W A I := l6_13_2_c A W I hOutAWI hBet1
            have hCongAIBI : Cong A I B I :=
              cong_right_commutativity_c A I I B (cong_left_commutativity_c I A I B hCong3)
            have hLe2 : Le A W B I :=
              l5_6_c A W A I A W B I hLe1 (cong_reflexivity_c A W) hCongAIBI
            obtain ⟨W', hBetBWI, hCongBWAW⟩ := le_bet_c B I A W hLe2
            have h5 : Bet I W A := between_symmetry_c A W I hBet1
            have h6 : Bet I W' B := between_symmetry_c B W' I hBetBWI
            have hCongWAW'B : Cong W A W' B := cong_4321_c B W' A W hCongBWAW
            have h1result : Cong I W I W' := l4_3_c I W A I W' B h5 h6 hCong3 hCongWAW'B
            have hCong5 : Cong A W' B W :=
              five_segment I I W W' A B W' W h1result hCongWAW'B
                (cong_symmetry_c I W I W' h1result)
                (cong_right_commutativity_c W W' W W' (cong_reflexivity_c W W'))
                h5 h6 hWI.symm
            have hCongAWAW' : Cong A W A W' :=
              cong_transitivity_c A W B W A W' hCongAWBW (cong_symmetry_c A W' B W hCong5)
            have hColAIW : Col A I W := col_permutation_5_c A W I (Or.inl hBet1)
            have hWeqW' : W = W' :=
              l4_18_c A I W W' hAI hColAIW hCongAWAW' h1result
            subst hWeqW'
            have hAeqB : A = B :=
              construction_uniqueness_c I W W A A B hWI.symm h5 (cong_reflexivity_c W A) h6
                (cong_4321_c A W B W hCongAWBW)
            exact hABFalse hAeqB
          · -- Bet W I A
            obtain ⟨W', hBetBIW', hCong4⟩ := segment_construction B I I W
            have h1 : Cong W I W' I :=
              cong_commutativity_c I W I W' (cong_symmetry_c I W' I W hCong4)
            have h6 : Bet W' I B := between_symmetry_c B I W' hBetBIW'
            have hCong5 : Cong A W' B W :=
              five_segment W W' I I A B W' W h1 hCong3
                (cong_right_commutativity_c W W' W W' (cong_reflexivity_c W W'))
                hCong4 hBet1 h6 hWI
            have hCongAWAW' : Cong A W A W' :=
              cong_transitivity_c A W B W A W' hCongAWBW (cong_symmetry_c A W' B W hCong5)
            have hColAIW : Col A I W := col_permutation_5_c A W I (Or.inr (Or.inl hBet1))
            have hWeqW' : W = W' :=
              l4_18_c A I W W' hAI hColAIW hCongAWAW' (cong_commutativity_c W I W' I h1)
            subst hWeqW'
            have hAeqB : A = B :=
              construction_uniqueness_c W I I A A B hWI hBet1 (cong_reflexivity_c I A) h6
                (cong_symmetry_c I A I B hCong3)
            exact hABFalse hAeqB
          · -- Bet I A W
            obtain ⟨W', hBetIBW', hCong4⟩ := segment_construction I B A W
            have hCongAWBW' : Cong A W B W' := cong_symmetry_c B W' A W hCong4
            have hCongIBIA : Cong I B I A := cong_symmetry_c I A I B hCong3
            have hCongABBA : Cong A B B A :=
              cong_right_commutativity_c A B A B (cong_reflexivity_c A B)
            have hCong5 : Cong W B W' A :=
              five_segment I I A B W W' B A hCong3 hCongAWBW' hCongIBIA hCongABBA
                hBet1 hBetIBW' hAI.symm
            have hCongAW'BW : Cong A W' B W := cong_4321_c W B W' A hCong5
            have hCongAWAW' : Cong A W A W' :=
              cong_transitivity_c A W B W A W' hCongAWBW (cong_symmetry_c A W' B W hCongAW'BW)
            have hCongIWIW' : Cong I W I W' :=
              l2_11_c I A W I B W' hBet1 hBetIBW' hCong3 hCongAWBW'
            have hColAIW : Col A I W := col_permutation_5_c A W I (Or.inr (Or.inr hBet1))
            have hWeqW' : W = W' :=
              l4_18_c A I W W' hAI hColAIW hCongAWAW' hCongIWIW'
            subst hWeqW'
            have hAeqB : A = B := between_cong_2_c I W A B hBet1 hBetIBW' hCong3
            exact hABFalse hAeqB
        rcases hDisj with ⟨hCol1, hCol2⟩ | ⟨hCol1, hCol2⟩ | ⟨hCol1, hCol2⟩
        · -- I on line A,X ; Col Y Z I
          rcases point_equality_decidability X I with hXI | hXI
          · subst hXI
            exact col_permutation_2_c Y Z X hCol2
          · exfalso
            have hCong3 : Cong I A I B :=
              l4_17_c Y Z I A B hYZ hCol2 hCong2 (cong_left_commutativity_c A Z Z B hMid1.2)
            exact Haux X hCong1 hCol1 hXI hCong3
        · -- I on line A,Y ; Col X Z I
          rcases point_equality_decidability Y I with hYI | hYI
          · subst hYI
            exact col_permutation_5_c X Z Y hCol2
          · exfalso
            have hCong3 : Cong I A I B :=
              l4_17_c X Z I A B hXZ hCol2 hCong1 (cong_left_commutativity_c A Z Z B hMid1.2)
            exact Haux Y hCong2 hCol1 hYI hCong3
        · -- I on line A,Z ; Col X Y I
          rcases point_equality_decidability Z I with hZI | hZI
          · subst hZI
            exact hCol2
          · have hColZAB : Col Z A B := midpoint_col_c A Z B hMid1
            have hColAZB : Col A Z B := col_permutation_4_c Z A B hColZAB
            have hColAIB : Col A I B := col_transitivity_1_c A Z I B hAZ hCol1 hColAZB
            have hCong3 : Cong I A I B :=
              l4_17_c X Y I A B hXY hCol2 hCong1 hCong2
            rcases l7_20_c I A B hColAIB hCong3 with hABeq | hMidIAB
            · exact absurd (l7_3_c Z A (hABeq ▸ hMid1)).symm hAZ
            · have hIZ : I = Z := l7_17_c A B I Z hMidIAB hMid1
              subst hIZ
              exact hCol2

theorem cop_perp2__col_c (X Y Z A B : Tpoint)
    (hCop : Coplanar A B Y Z) (h₁ : Perp X Y A B) (h₂ : Perp X Z A B) :
    Col X Y Z := by
  rcases col_dec_c A B X with hColABX | hNColABX
  · rcases point_equality_decidability X A with hXA | hXA
    · subst hXA
      have hPerXYB : Per Y X B := perp_per_2_c X Y B h₁
      have hPerZXB : Per Z X B := perp_per_2_c X Z B h₂
      have hXB : X ≠ B := (perp_distinct_c X Y X B h₁).2
      have hCopBYZX : Coplanar B Y Z X := coplanar_perm_9_c X B Y Z hCop
      exact col_permutation_2_c Y Z X
        (cop_per2__col_c B Y Z X hCopBYZX hXB.symm hPerXYB hPerZXB)
    · have hAX : A ≠ X := hXA.symm
      have hAB : A ≠ B := (perp_distinct_c X Y A B h₁).2
      have hPerpAXXY : Perp A X X Y :=
        perp_col_c A B X Y X hAX (perp_sym_c X Y A B h₁) hColABX
      have hPerpAXXZ : Perp A X X Z :=
        perp_col_c A B X Z X hAX (perp_sym_c X Z A B h₂) hColABX
      have hPerYXA : Per Y X A := perp_per_1_c X Y A (perp_sym_c A X X Y hPerpAXXY)
      have hPerZXA : Per Z X A := perp_per_1_c X Z A (perp_sym_c A X X Z hPerpAXXZ)
      have hCopYZAB : Coplanar Y Z A B := coplanar_perm_16_c A B Y Z hCop
      have hCopYZAX : Coplanar Y Z A X :=
        col_cop__cop_c Y Z A B X hCopYZAB hAB hColABX
      have hCopAYZX : Coplanar A Y Z X := coplanar_perm_12_c Y Z A X hCopYZAX
      exact col_permutation_2_c Y Z X
        (cop_per2__col_c A Y Z X hCopAYZX hAX hPerYXA hPerZXA)
  · have h₁' := h₁
    have h₂' := h₂
    obtain ⟨Y0, hPerpAtY0⟩ := h₁'
    obtain ⟨Z0, hPerpAtZ0⟩ := h₂'
    have hColXYY0 : Col X Y Y0 := (perp_in_col_c X Y A B Y0 hPerpAtY0).1
    have hColABY0 : Col A B Y0 := (perp_in_col_c X Y A B Y0 hPerpAtY0).2
    have hColXZZ0 : Col X Z Z0 := (perp_in_col_c X Z A B Z0 hPerpAtZ0).1
    have hColABZ0 : Col A B Z0 := (perp_in_col_c X Z A B Z0 hPerpAtZ0).2
    have hXY0 : X ≠ Y0 := fun hEq => hNColABX (hEq ▸ hColABY0)
    have hXZ0 : X ≠ Z0 := fun hEq => hNColABX (hEq ▸ hColABZ0)
    have hPerpXY0AB : Perp X Y0 A B := perp_col_c X Y A B Y0 hXY0 h₁ hColXYY0
    have hPerpXZ0AB : Perp X Z0 A B := perp_col_c X Z A B Z0 hXZ0 h₂ hColXZZ0
    have hY0Z0 : Y0 = Z0 :=
      l8_18_uniqueness_c A B X Y0 Z0 hNColABX hColABY0 (perp_sym_c X Y0 A B hPerpXY0AB)
        hColABZ0 (perp_sym_c X Z0 A B hPerpXZ0AB)
    subst hY0Z0
    exact col_transitivity_1_c X Y0 Y Z hXY0
      (col_permutation_5_c X Y Y0 hColXYY0) (col_permutation_5_c X Z Y0 hColXZZ0)

theorem two_sides_dec_c (A B C D : Tpoint) : TS A B C D ∨ ¬ TS A B C D := by
  rcases col_dec_c C A B with hCol1 | hNCol1
  · exact Or.inr (fun h => h.1 hCol1)
  rcases col_dec_c D A B with hCol2 | hNCol2
  · exact Or.inr (fun h => h.2.1 hCol2)
  have hNColABC : ¬ Col A B C := fun h => hNCol1 (by colr)
  have hNColABD : ¬ Col A B D := fun h => hNCol2 (by colr)
  obtain ⟨C0, hColABC0, hPerpABCC0⟩ := l8_18_existence_c A B C hNColABC
  obtain ⟨D0, hColABD0, hPerpABDD0⟩ := l8_18_existence_c A B D hNColABD
  have hAB : A ≠ B := (perp_distinct_c A B C C0 hPerpABCC0).1
  obtain ⟨M, hMidM⟩ := midpoint_existence_c C0 D0
  have hColABM : Col A B M := by
    rcases eq_dec_points_c C0 D0 with hEq | hC0D0
    · have hMidMC0C0 : Midpoint M C0 C0 := hEq ▸ hMidM
      have hMC0 : M = C0 := l7_3_c M C0 hMidMC0C0
      rw [hMC0]; exact hColABC0
    · have hColMC0D0 : Col M C0 D0 := midpoint_col_c C0 M D0 hMidM
      colr
  have hDD0 : D ≠ D0 := (perp_distinct_c A B D D0 hPerpABDD0).2
  have hC0C : C0 ≠ C := (perp_distinct_c A B C C0 hPerpABCC0).2.symm
  obtain ⟨D', hOutD0D'D, hCongD0D'C0C⟩ := l6_11_existence_c D0 C0 C D hDD0 hC0C
  rcases bet_dec_c C M D' with hBetCMD' | hNBetCMD'
  · -- LEFT: Bet C M D' holds ⟹ TS A B C D
    left
    have hD0D' : D0 ≠ D' := hOutD0D'D.1.symm
    have hNColD'AB : ¬ Col D' A B := by
      intro hColD'AB
      have hColD0D'D : Col D0 D' D := out_col_c D0 D' D hOutD0D'D
      exact hNColABD (by colr)
    have hColMAB : Col M A B := by colr
    have hTSD'C : TS A B D' C :=
      ⟨hNColD'AB, hNCol1, M, hColMAB, between_symmetry_c C M D' hBetCMD'⟩
    have hColD0AB : Col D0 A B := by colr
    have hTSDC : TS A B D C := l9_5_c A B D' C D0 D hTSD'C hColD0AB hOutD0D'D
    exact l9_2_c A B D C hTSDC
  · -- RIGHT: ¬ Bet C M D' ⟹ ¬ TS A B C D
    right
    intro hTS
    apply hNBetCMD'
    have invert_two_sides_loc : ∀ P Q R S : Tpoint, TS P Q R S → TS Q P R S := by
      intro P Q R S h
      obtain ⟨h1, h2, T, hT, hBet⟩ := h
      exact ⟨fun hc => h1 (col_permutation_5_c R Q P hc),
             fun hc => h2 (col_permutation_5_c S Q P hc),
             T, col_permutation_5_c T P Q hT, hBet⟩
    have hTS_ADC : TS A B D C := l9_2_c A B C D hTS
    have hColD0AB : Col D0 A B := by colr
    have hOutD0DD' : Out D0 D D' := l6_6_c D0 D' D hOutD0D'D
    have hHTS1 : TS A B D' C := l9_5_c A B D C D0 D' hTS_ADC hColD0AB hOutD0DD'
    rcases eq_dec_points_c C0 D0 with hEq | hNeq
    · -- degenerate: C0 = D0
      have hMidMC0C0 : Midpoint M C0 C0 := hEq ▸ hMidM
      have hMC0 : M = C0 := l7_3_c M C0 hMidMC0C0
      have hPerpABDC0 : Perp A B D C0 := hEq ▸ hPerpABDD0
      have hOutC0D'D : Out C0 D' D := hEq ▸ hOutD0D'D
      have hPerpABCM : Perp A B C M := hMC0 ▸ hPerpABCC0
      have hPerpABDM : Perp A B D M := hMC0 ▸ hPerpABDC0
      have hPerpMCAB : Perp M C A B :=
        perp_left_comm_c C M A B (perp_sym_c A B C M hPerpABCM)
      have hPerpMDAB : Perp M D A B :=
        perp_left_comm_c D M A B (perp_sym_c A B D M hPerpABDM)
      have hCopABCD : Coplanar A B C D := ts__coplanar_c A B C D hTS
      have hColMCD : Col M C D := cop_perp2__col_c M C D A B hCopABCD hPerpMCAB hPerpMDAB
      have hOutMD'D : Out M D' D := hMC0 ▸ hOutC0D'D
      have hDM : D ≠ M := fun hh => hNColABD (hh ▸ hColABM)
      have hColMD'D : Col M D' D := out_col_c M D' D hOutMD'D
      have hColMCD' : Col M C D' := by colr
      rcases distinct_c A B M hAB with hMA | hMB
      · have hAM : A ≠ M := hMA.symm
        have hTSABCD' : TS A B C D' := l9_2_c A B D' C hHTS1
        have hTSAMCD' : TS A M C D' := col_two_sides_c A B M C D' hColABM hAM hTSABCD'
        have hTSMACD' : TS M A C D' := invert_two_sides_loc A M C D' hTSAMCD'
        exact col_two_sides_bet_c M A C D' hColMCD' hTSMACD'
      · have hBM : B ≠ M := hMB.symm
        have hColBAM : Col B A M := by colr
        have hTSBACD' : TS B A C D' := l9_2_c B A D' C (invert_two_sides_loc A B D' C hHTS1)
        have hTSBMCD' : TS B M C D' := col_two_sides_c B A M C D' hColBAM hBM hTSBACD'
        have hTSMBCD' : TS M B C D' := invert_two_sides_loc B M C D' hTSBMCD'
        exact col_two_sides_bet_c M B C D' hColMCD' hTSMBCD'
    · -- general: C0 ≠ D0
      obtain ⟨_, _, M', hColM'AB, hBetD'M'C⟩ := hHTS1
      have hPerpC0D0CC0 : Perp C0 D0 C C0 :=
        perp_col2_c A B C0 D0 C C0 hPerpABCC0 hNeq hColABC0 hColABD0
      have hPerD0C0C : Per D0 C0 C := perp_per_1_c C0 D0 C hPerpC0D0CC0
      have hPerpD0C0DD0 : Perp D0 C0 D D0 :=
        perp_col2_c A B D0 C0 D D0 hPerpABDD0 hNeq.symm hColABD0 hColABC0
      have hPerC0D0D : Per C0 D0 D := perp_per_1_c D0 C0 D hPerpD0C0DD0
      have hD0D : D0 ≠ D := hDD0.symm
      have hColD0D'D : Col D0 D' D := out_col_c D0 D' D hOutD0D'D
      have hColD0DD' : Col D0 D D' := by colr
      have hPerC0D0D' : Per C0 D0 D' := per_col_c C0 D0 D D' hD0D hPerC0D0D hColD0DD'
      have hCongC0CD0D' : Cong C0 C D0 D' := cong_symmetry_c D0 D' C0 C hCongD0D'C0C
      have hBetCM'D' : Bet C M' D' := between_symmetry_c D' M' C hBetD'M'C
      have hColC0D0M' : Col C0 D0 M' := by colr
      obtain ⟨_, hMidM'C0D0, _⟩ :=
        l8_22_c C0 D0 C D' M' hNeq hC0C hPerD0C0C hPerC0D0D' hCongC0CD0D' hColC0D0M' hBetCM'D'
      have hMM' : M = M' := l7_17_c C0 D0 M M' hMidM hMidM'C0D0
      rw [hMM']
      exact between_symmetry_c D' M' C hBetD'M'C

theorem cop_nts__os_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNTS : ¬ TS A B C D) : OS A B C D := by
  have o := cop__one_or_two_sides_c A B C D hCop hNC1 hNC2
  rcases o with H3 | H3
  · exact ((hNTS H3)).elim
  · exact H3

theorem cop_nos__ts_c (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNOS : ¬ OS A B C D) : TS A B C D := by
  have o := cop__one_or_two_sides_c A B C D hCop hNC1 hNC2
  rcases o with H3 | H3
  · exact H3
  · exact ((hNOS H3)).elim

theorem one_side_dec_c (A B C D : Tpoint) : OS A B C D ∨ ¬ OS A B C D := by
  rcases col_dec_c A B D with hColABD | hNColABD
  · exact Or.inr (fun hOS => one_side_not_col124_c A B C D hOS hColABD)
  · have hNColDAB : ¬ Col D A B := fun h => hNColABD (col_permutation_1_c D A B h)
    obtain ⟨D', hTSABDD'⟩ := l9_10_c A B D hNColDAB
    rcases two_sides_dec_c A B C D' with hTS | hNTS
    · exact Or.inl (l9_8_1_c A B C D D' hTS hTSABDD')
    · exact Or.inr (fun hOS => hNTS (l9_8_2_c A B D C D' hTSABDD' (one_side_symmetry_c A B C D hOS)))

theorem cop_dec_c (A B C D : Tpoint) : Coplanar A B C D ∨ ¬ Coplanar A B C D := by
  rcases col_dec_c C A B with hColCAB | hNColCAB
  · exact Or.inl ⟨C, Or.inl ⟨col_permutation_1_c C A B hColCAB, col_trivial_3_c C D⟩⟩
  rcases col_dec_c D A B with hColDAB | hNColDAB
  · exact Or.inl ⟨D, Or.inl ⟨col_permutation_1_c D A B hColDAB, col_trivial_2_c C D⟩⟩
  rcases two_sides_dec_c A B C D with hTS | hNTS
  · exact Or.inl (ts__coplanar_c A B C D hTS)
  rcases one_side_dec_c A B C D with hOS | hNOS
  · exact Or.inl (os__coplanar_c A B C D hOS)
  · exact Or.inr (fun hCop =>
      (cop__one_or_two_sides_c A B C D hCop hNColCAB hNColDAB).elim hNTS hNOS)

theorem ex_diff_cop_c (A B C D : Tpoint) :
    ∃ E, Coplanar A B C E ∧ D ≠ E := by
  rcases point_equality_decidability A D with hAD | hAD
  · rcases point_equality_decidability B D with hBD | hBD
    · obtain ⟨E, hDE⟩ := another_point_c D
      refine ⟨E, ?_, hDE⟩
      rw [hAD, hBD]
      exact ⟨E, Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩⟩
    · exact ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_2_c _ _⟩⟩, Ne.symm hBD⟩
  · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c _ _, col_trivial_2_c _ _⟩⟩, Ne.symm hAD⟩

theorem ex_ncol_cop_c (A B C D E : Tpoint) (hDE : D ≠ E) :
    ∃ F, Coplanar A B C F ∧ ¬ Col D E F := by
  rcases col_dec_c A B C with hABC | hABC
  · obtain ⟨F, hF⟩ := not_col_exists_c D E hDE
    exact ⟨F, ⟨C, Or.inl ⟨hABC, col_trivial_3_c C F⟩⟩, hF⟩
  · rcases col_dec_c D E A with hDEA | hDEA
    · rcases col_dec_c D E B with hDEB | hDEB
      · refine ⟨C, ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c A C, col_trivial_2_c B C⟩)⟩,
          fun hDEC => hABC (col3_c D E A B C hDE hDEA hDEB hDEC)⟩
      · exact ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c A B, col_trivial_2_c C B⟩⟩, hDEB⟩
    · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c A B, col_trivial_2_c C A⟩⟩, hDEA⟩

theorem ex_ncol_cop2_c (A B C D : Tpoint) :
    ∃ E F, Coplanar A B C E ∧ Coplanar A B C F ∧ ¬ Col D E F := by
  obtain ⟨E, HE, HDE⟩ := ex_diff_cop_c A B C D
  obtain ⟨F, HF, HCol⟩ := ex_ncol_cop_c A B C D E HDE
  exact ⟨E, F, HE, HF, HCol⟩

theorem col2_cop2__eq_c (A B C U V P Q : Tpoint)
    (hNCop : ¬ Coplanar A B C U) (hUV : U ≠ V)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q)
    (h₃ : Col U V P) (h₄ : Col U V Q) : P = Q := by
  rcases point_equality_decidability P Q with hPQ | hPQ
  · exact hPQ
  · exfalso
    have hColUPQ : Col U P Q := col_transitivity_1_c U V P Q hUV h₃ h₄
    have hColPQU : Col P Q U := by colr
    exact hNCop (col_cop2__cop_c A B C P Q U hPQ h₁ h₂ hColPQU)

theorem cong3_cop2__col_c (A B C P Q : Tpoint)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q) (hPQ : P ≠ Q)
    (h₃ : Cong A P A Q) (h₄ : Cong B P B Q) (h₅ : Cong C P C Q) :
    Col A B C := by
  rcases col_dec_c A B C with hCol | hNCol
  · exact hCol
  · obtain ⟨M, hMid⟩ := midpoint_existence_c P Q
    have hPerAMP : Per A M P := ⟨Q, hMid, h₃⟩
    have hPerBMP : Per B M P := ⟨Q, hMid, h₄⟩
    have hPerCMP : Per C M P := ⟨Q, hMid, h₅⟩
    have hMPQ : M ≠ P ∧ M ≠ Q := midpoint_distinct_1_c M P Q hPQ hMid
    rcases point_equality_decidability A M with hAM | hAM
    · subst hAM
      have hPA : P ≠ A := hMPQ.1.symm
      have hCopPBCA : Coplanar P B C A := coplanar_perm_21_c A B C P h₁
      exact col_permutation_2_c B C A (cop_per2__col_c P B C A hCopPBCA hPA hPerBMP hPerCMP)
    · have hColPQM : Col P Q M := col_permutation_1_c M P Q (midpoint_col_c P M Q hMid)
      have hNColCAB : ¬ Col C A B := fun hh => hNCol (col_permutation_1_c C A B hh)
      have hCopCABP : Coplanar C A B P := coplanar_perm_12_c A B C P h₁
      have hCopCABQ : Coplanar C A B Q := coplanar_perm_12_c A B C Q h₂
      have hCopABPQ : Coplanar A B P Q :=
        coplanar_trans_1_c C A B P Q hNColCAB hCopCABP hCopCABQ
      have hCopABPM : Coplanar A B P M := col_cop__cop_c A B P Q M hCopABPQ hPQ hColPQM
      have hCopPABM : Coplanar P A B M := coplanar_perm_12_c A B P M hCopABPM
      have hColABM : Col A B M :=
        cop_per2__col_c P A B M hCopPABM hMPQ.1.symm hPerAMP hPerBMP
      have hNColBAC : ¬ Col B A C := fun hh => hNCol (col_permutation_4_c B A C hh)
      have hCopBACP : Coplanar B A C P := coplanar_perm_6_c A B C P h₁
      have hCopBACQ : Coplanar B A C Q := coplanar_perm_6_c A B C Q h₂
      have hCopACPQ : Coplanar A C P Q :=
        coplanar_trans_1_c B A C P Q hNColBAC hCopBACP hCopBACQ
      have hCopACPM : Coplanar A C P M := col_cop__cop_c A C P Q M hCopACPQ hPQ hColPQM
      have hCopPACM : Coplanar P A C M := coplanar_perm_12_c A C P M hCopACPM
      have hColACM : Col A C M :=
        cop_per2__col_c P A C M hCopPACM hMPQ.1.symm hPerAMP hPerCMP
      exact col_transitivity_1_c A M B C hAM
        (col_permutation_5_c A B M hColABM) (col_permutation_5_c A C M hColACM)

theorem l9_38_c (A B C P Q : Tpoint) (h : TSP A B C P Q) : TSP A B C Q P := by
  obtain ⟨HP, HQ, T, HT, HBet⟩ := h
  exact ⟨HQ, HP, T, HT, between_symmetry HBet⟩

theorem l9_39_c (A B C D P Q R : Tpoint)
    (h₁ : TSP A B C P R) (hCop : Coplanar A B C D) (hOut : Out D P Q) :
    TSP A B C Q R := by
  obtain ⟨HP, HR, T, HT, HBet⟩ := h₁
  have hDQ : D ≠ Q := hOut.2.1.symm
  have hColDPQ : Col D P Q := out_col_c D P Q hOut
  have hNCopQ : ¬ Coplanar A B C Q := by
    intro hCopQ
    have hColDQP : Col D Q P := by colr
    exact HP (col_cop2__cop_c A B C D Q P hDQ hCop hCopQ hColDQP)
  refine ⟨hNCopQ, HR, ?_⟩
  rcases point_equality_decidability D T with hDT | hDT
  · refine ⟨D, hDT ▸ HT, bet_out__bet_c P Q R D (hDT ▸ HBet) hOut⟩
  · have hNColPDT : ¬ Col P D T := by
      intro hColPDT
      have hColDTP : Col D T P := by colr
      exact HP (col_cop2__cop_c A B C D T P hDT hCop HT hColDTP)
    have hNColRDT : ¬ Col R D T := by
      intro hColRDT
      have hColDTR : Col D T R := by colr
      exact HR (col_cop2__cop_c A B C D T R hDT hCop HT hColDTR)
    have hTSDTQR : TS D T Q R :=
      l9_8_2_c D T P Q R
        ⟨hNColPDT, hNColRDT, T, col_trivial_3_c T D, HBet⟩
        (out_one_side_c D T P Q (Or.inl (fun hh => hNColPDT (by colr))) hOut)
    obtain ⟨hNColQDT, hNColRDT2, T', hColT'DT, hBetQT'R⟩ := hTSDTQR
    have hColDTT' : Col D T T' := by colr
    exact ⟨T', col_cop2__cop_c A B C D T T' hDT hCop HT hColDTT', hBetQT'R⟩

theorem l9_41_1_c (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : TSP A B C Q R) : OSP A B C P Q :=
  ⟨R, (⟨h₁, h₂⟩)⟩

theorem l9_41_2_c (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : OSP A B C P Q) : TSP A B C Q R := by
  obtain ⟨S, hTSP_PS, hTSP_QS⟩ := h₂
  obtain ⟨HP, HS1, X, HX, HBetPXS⟩ := hTSP_PS
  obtain ⟨HQ, HS, Y, HY, HBetQYS⟩ := hTSP_QS
  have hPX : P ≠ X := fun e => HP (e ▸ HX)
  have hSX : S ≠ X := fun e => HS1 (e ▸ HX)
  have hQY : Q ≠ Y := fun e => HQ (e ▸ HY)
  have hSY : S ≠ Y := fun e => HS (e ▸ HY)
  have hColPXS : Col P X S := bet_col_c P X S HBetPXS
  have hColQYS : Col Q Y S := bet_col_c Q Y S HBetQYS
  have hPS : P ≠ S := by
    intro hEq
    subst hEq
    exact hPX (between_identity _ _ HBetPXS)
  have hQS : Q ≠ S := by
    intro hEq
    subst hEq
    exact hQY (between_identity _ _ HBetQYS)
  rcases col_dec_c P Q S with hColPQS | hNCol
  · -- Case: Col P Q S
    have hColQSX : Col Q S X := by colr
    have hColQSY : Col Q S Y := by colr
    have hXY : X = Y := col2_cop2__eq_c A B C Q S X Y HQ hQS HX HY hColQSX hColQSY
    subst hXY
    have hOutXPQ : Out X P Q := (l6_2_c P Q S X hPX hQY hSX HBetPXS).mp HBetQYS
    exact l9_39_c A B C X P Q R h₁ HX hOutXPQ
  · -- Case: ¬ Col P Q S
    obtain ⟨Z, hBetXZQ, hBetYZP⟩ := inner_pasch P Q S X Y HBetPXS HBetQYS
    have hXZ : X ≠ Z := by
      intro e
      subst e
      have hColYXP : Col Y X P := bet_col_c Y X P hBetYZP
      exact hNCol (by colr)
    have hYZ : Y ≠ Z := by
      intro e
      subst e
      have hColXYQ : Col X Y Q := bet_col_c X Y Q hBetXZQ
      exact hNCol (by colr)
    have hOutXZQ : Out X Z Q := bet_out_c X Z Q hXZ.symm hBetXZQ
    have hOutYZP : Out Y Z P := bet_out_c Y Z P hYZ.symm hBetYZP
    have hOutYPZ : Out Y P Z := l6_6_c Y Z P hOutYZP
    have hTSPZR : TSP A B C Z R := l9_39_c A B C Y P Z R h₁ HY hOutYPZ
    exact l9_39_c A B C X Z Q R hTSPZR HX hOutXZQ

theorem tsp_exists_c (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    ∃ Q, TSP A B C P Q := by
  obtain ⟨Q, hBetPAQ, hCongAQAP⟩ := segment_construction P A A P
  have hHA : Coplanar A B C A := coplanar_perm_1_c A B A C (col__coplanar_c A B A C (col_trivial_3_c A B))
  refine ⟨Q, hNCop, ?_, A, hHA, hBetPAQ⟩
  have hAP : A ≠ P := fun e => hNCop (e ▸ hHA)
  have hAQ : A ≠ Q := cong_diff_3_c A Q A P hAP hCongAQAP
  intro hCopQ
  have hColPAQ : Col P A Q := bet_col_c P A Q hBetPAQ
  have hColAQP : Col A Q P := by colr
  exact hNCop (col_cop2__cop_c A B C A Q P hAQ hHA hCopQ hColAQP)

theorem osp_reflexivity_c (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    OSP A B C P P := by
  obtain ⟨Q, hTSP⟩ := tsp_exists_c A B C P hNCop
  exact ⟨Q, hTSP, hTSP⟩

theorem osp_symmetry_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    OSP A B C Q P := by
  rcases h with ⟨R, hR1, hR2⟩
  exact ⟨R, hR2, hR1⟩

theorem osp_transitivity_c (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P Q) (h₂ : OSP A B C Q R) : OSP A B C P R := by
  obtain ⟨S, HPS, HQS⟩ := h₁
  exact ⟨S, HPS, l9_41_2_c A B C Q R S HQS h₂⟩

theorem cop3_tsp__tsp_c (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : TSP A B C P Q) : TSP D E F P Q := by
  obtain ⟨HP, HQ, T, HT, HBet⟩ := h₄
  have hNColABC : ¬ Col A B C := ncop__ncol_c A B C P HP
  have hCopDEFA : Coplanar D E F A :=
    coplanar_pseudo_trans_c D E F A A B C hNColABC h₁ h₂ h₃
      ⟨A, Or.inl ⟨col_trivial_3_c A B, col_trivial_2_c C A⟩⟩
  have hCopDEFB : Coplanar D E F B :=
    coplanar_pseudo_trans_c D E F B A B C hNColABC h₁ h₂ h₃
      ⟨B, Or.inl ⟨col_trivial_2_c A B, col_trivial_2_c C B⟩⟩
  have hCopDEFC : Coplanar D E F C :=
    coplanar_pseudo_trans_c D E F C A B C hNColABC h₁ h₂ h₃
      ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c A C, col_trivial_2_c B C⟩)⟩
  have hCopDEFT : Coplanar D E F T :=
    coplanar_pseudo_trans_c D E F T A B C hNColABC h₁ h₂ h₃ HT
  refine ⟨?_, ?_, T, hCopDEFT, HBet⟩
  · exact fun hCopDEFP =>
      HP (coplanar_pseudo_trans_c A B C P D E F hNCol hCopDEFA hCopDEFB hCopDEFC hCopDEFP)
  · exact fun hCopDEFQ =>
      HQ (coplanar_pseudo_trans_c A B C Q D E F hNCol hCopDEFA hCopDEFB hCopDEFC hCopDEFQ)

theorem cop3_osp__osp_c (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : OSP A B C P Q) : OSP D E F P Q := by
  obtain ⟨R, hPR, hQR⟩ := h₄
  exact ⟨R, cop3_tsp__tsp_c A B C D E F P R hNCol h₁ h₂ h₃ hPR,
         cop3_tsp__tsp_c A B C D E F Q R hNCol h₁ h₂ h₃ hQR⟩

theorem ncop_distincts_c (A B C D : Tpoint) (h : ¬ Coplanar A B C D) :
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inr (Or.inl ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨C, Or.inr (Or.inr ⟨col_trivial_1_c _ _, col_trivial_2_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨D, Or.inr (Or.inr ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨C, Or.inr (Or.inl ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩)⟩
  · intro e; apply h; rw [e]
    exact ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_1_c _ _⟩⟩

theorem tsp_distincts_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q ∧ P ≠ Q := by
  obtain ⟨HP, HQ, T, hT, hBet⟩ := h
  obtain ⟨hab, hac, hap, hbc, hbp, hcp⟩ := ncop_distincts_c A B C P HP
  obtain ⟨_, _, haq, _, hbq, hcq⟩ := ncop_distincts_c A B C Q HQ
  refine ⟨hab, hac, hbc, hap, hbp, hcp, haq, hbq, hcq, ?_⟩
  intro hpq
  rw [hpq] at hBet
  have hTQ := between_identity Q T hBet
  rw [← hTQ] at hT
  exact HQ hT

theorem osp_distincts_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q := by
  obtain ⟨R, HPR, HQR⟩ := h
  have hPR := tsp_distincts_c A B C P R HPR
  have hQR := tsp_distincts_c A B C Q R HQR
  obtain ⟨hAB, hAC, hBC, hAP, hBP, hCP, -, -, -, -⟩ := hPR
  obtain ⟨-, -, -, hAQ, hBQ, hCQ, -, -, -, -⟩ := hQR
  exact ⟨hAB, hAC, hBC, hAP, hBP, hCP, hAQ, hBQ, hCQ⟩

theorem tsp__ncop1_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C P := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨_, _⟩ := H1
  exact H0

theorem tsp__ncop2_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C Q := by
  obtain ⟨_, H0⟩ := h
  obtain ⟨H1, _⟩ := H0
  exact H1

theorem osp__ncop1_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C P := by
  rcases h with ⟨R, hTSP, _⟩
  exact tsp__ncop1_c A B C P R hTSP

theorem osp__ncop2_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C Q := by
  obtain ⟨R, H1, H2⟩ := h
  exact tsp__ncop1_c A B C Q R H2

theorem tsp__nosp_c (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ OSP A B C P Q := by
  intro hOS
  have hAbs : TSP A B C P P :=
    l9_41_2_c A B C Q P P (l9_38_c A B C P Q h) (osp_symmetry_c A B C P Q hOS)
  obtain ⟨-, -, -, -, -, -, -, -, -, hPP⟩ := tsp_distincts_c A B C P P hAbs
  exact hPP rfl

theorem osp__ntsp_c (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ TSP A B C P Q := fun hTSP => tsp__nosp_c A B C P Q hTSP h

theorem osp_bet__osp_c (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P R) (h₂ : Bet P Q R) : OSP A B C P Q := by
  obtain ⟨S, hTSP_PS, HR, HS, Y, HY, hBetRYS⟩ := h₁
  have hTSP_PS' := hTSP_PS
  obtain ⟨HP, HS2, X, HX, hBetPXS⟩ := hTSP_PS'
  have hPX : P ≠ X := fun e => HP (e ▸ HX)
  have hRY : R ≠ Y := fun e => HR (e ▸ HY)
  have hSY : S ≠ Y := fun e => HS (e ▸ HY)
  have hSX : S ≠ X := fun e => HS2 (e ▸ HX)
  obtain ⟨-, -, -, -, -, -, -, -, -, hPS⟩ :=
    tsp_distincts_c A B C P S ⟨HP, HS2, X, HX, hBetPXS⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hRS⟩ :=
    tsp_distincts_c A B C R S ⟨HR, HS, Y, HY, hBetRYS⟩
  rcases col_dec_c P R S with hColPRS | hNCol
  · -- Case: Col P R S
    have hColPXS : Col P X S := bet_col_c P X S hBetPXS
    have hColRYS : Col R Y S := bet_col_c R Y S hBetRYS
    have hColRSX : Col R S X := by colr
    have hColRSY : Col R S Y := by colr
    have hXY : X = Y := col2_cop2__eq_c A B C R S X Y HR hRS HX HY hColRSX hColRSY
    subst hXY
    have hOutXPR : Out X P R := (l6_2_c P R S X hPX hRY hSY hBetPXS).mp hBetRYS
    have hOutXPQ : Out X P Q := out_bet_out_1_c P Q R X hOutXPR h₂
    exact ⟨S, hTSP_PS, l9_39_c A B C X P Q S hTSP_PS HX hOutXPQ⟩
  · -- Case: ¬ Col P R S
    have hColPXS : Col P X S := bet_col_c P X S hBetPXS
    have hColRYS : Col R Y S := bet_col_c R Y S hBetRYS
    have hNColPXY : ¬ Col P X Y := by
      intro hCol
      exact hNCol (by colr)
    have hNColSXY : ¬ Col S X Y := by
      intro hCol
      exact hNCol (by colr)
    have hNColRXY : ¬ Col R X Y := by
      intro hCol
      exact hNCol (by colr)
    have hOSXYPR : OS X Y P R :=
      ⟨S, ⟨hNColPXY, hNColSXY, X, col_trivial_1_c X Y, hBetPXS⟩,
          ⟨hNColRXY, hNColSXY, Y, col_trivial_3_c Y X, hBetRYS⟩⟩
    have hOSXYPQ : OS X Y P Q := l9_17_c P Q R X Y hOSXYPR h₂
    obtain ⟨S', ⟨-, hNColS'XY, X', hColX'XY, hBetPX'S'⟩,
                ⟨hNColQXY, -, Y', hColY'XY, hBetQY'S'⟩⟩ := hOSXYPQ
    have hXY : X ≠ Y := fun e => hNColPXY (e ▸ (col_trivial_2_c P X))
    have hCopX' : Coplanar A B C X' :=
      col_cop2__cop_c A B C X Y X' hXY HX HY (col_permutation_1_c X' X Y hColX'XY)
    have hCopY' : Coplanar A B C Y' :=
      col_cop2__cop_c A B C X Y Y' hXY HX HY (col_permutation_1_c Y' X Y hColY'XY)
    have hX'S' : X' ≠ S' := fun e => hNColS'XY (e ▸ hColX'XY)
    have hHS' : ¬ Coplanar A B C S' := by
      intro hCopS'
      apply HP
      have hColPX'S' : Col P X' S' := bet_col_c P X' S' hBetPX'S'
      have hColX'S'P : Col X' S' P := col_permutation_1_c P X' S' hColPX'S'
      exact col_cop2__cop_c A B C X' S' P hX'S' hCopX' hCopS' hColX'S'P
    have hQY' : Q ≠ Y' := fun e => hNColQXY (e ▸ hColY'XY)
    have hNCopQ : ¬ Coplanar A B C Q := by
      intro hCopQ
      apply hHS'
      have hColQY'S' : Col Q Y' S' := bet_col_c Q Y' S' hBetQY'S'
      exact col_cop2__cop_c A B C Q Y' S' hQY' hCopQ hCopY' hColQY'S'
    exact ⟨S', ⟨HP, hHS', X', hCopX', hBetPX'S'⟩, ⟨hNCopQ, hHS', Y', hCopY', hBetQY'S'⟩⟩

theorem l9_18_3_c (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    TSP A B C X Y ↔ Bet X P Y ∧ ¬ Coplanar A B C X ∧ ¬ Coplanar A B C Y := by
  constructor
  · intro h
    obtain ⟨HX, HY, T, HT, HBet⟩ := h
    have hXY : X ≠ Y := by
      intro hEq
      subst hEq
      apply HX
      rw [between_identity X T HBet]
      exact HT
    have hColXTY : Col X T Y := bet_col_c X T Y HBet
    have hColXYT : Col X Y T := col_permutation_5_c X T Y hColXTY
    have hTP : T = P := col2_cop2__eq_c A B C X Y T P HX hXY HT hCop hColXYT hCol
    exact ⟨hTP ▸ HBet, HX, HY⟩
  · intro h
    obtain ⟨hBet, HX, HY⟩ := h
    exact ⟨HX, HY, P, hCop, hBet⟩

theorem bet_cop__tsp_c (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hPY : P ≠ Y)
    (hCop : Coplanar A B C P) (hBet : Bet X P Y) : TSP A B C X Y := by
  have hColXPY : Col X P Y := bet_col_c X P Y hBet
  have hColXYP : Col X Y P := col_permutation_5_c X P Y hColXPY
  have hNCopY : ¬ Coplanar A B C Y := by
    intro hCopY
    apply hNCop
    have hColPYX : Col P Y X := col_permutation_1_c X P Y hColXPY
    exact col_cop2__cop_c A B C P Y X hPY hCop hCopY hColPYX
  exact (l9_18_3_c A B C X Y P hCop hColXYP).mpr ⟨hBet, hNCop, hNCopY⟩

theorem cop_out__osp_c (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hCop : Coplanar A B C P)
    (hOut : Out P X Y) : OSP A B C X Y := by
  have hOut' := hOut
  obtain ⟨hXP, hYP, -⟩ := hOut'
  have hPY : P ≠ Y := hYP.symm
  have hColPXY : Col P X Y := out_col_c P X Y hOut
  have hColPYX : Col P Y X := col_permutation_5_c P X Y hColPXY
  have hNCopY : ¬ Coplanar A B C Y := by
    intro hCopY
    apply hNCop
    exact col_cop2__cop_c A B C P Y X hPY hCop hCopY hColPYX
  obtain ⟨X', hBetXPX', hCongPX'PX⟩ := segment_construction X P P X
  have hPX' : P ≠ X' := cong_diff_3_c P X' P X hXP.symm hCongPX'PX
  have hColXPX' : Col X P X' := bet_col_c X P X' hBetXPX'
  have hColPX'X : Col P X' X := col_permutation_1_c X P X' hColXPX'
  have hNCopX' : ¬ Coplanar A B C X' := by
    intro hCopX'
    apply hNCop
    exact col_cop2__cop_c A B C P X' X hPX' hCop hCopX' hColPX'X
  have hBetYPX' : Bet Y P X' := bet_out__bet_c X Y X' P hBetXPX' hOut
  exact ⟨X', ⟨hNCop, hNCopX', P, hCop, hBetXPX'⟩, ⟨hNCopY, hNCopX', P, hCop, hBetYPX'⟩⟩

theorem l9_19_3_c (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    OSP A B C X Y ↔ Out P X Y ∧ ¬ Coplanar A B C X := by
  constructor
  · intro hOS
    have hNCopX : ¬ Coplanar A B C X := osp__ncop1_c A B C X Y hOS
    have hNCopY : ¬ Coplanar A B C Y := osp__ncop2_c A B C X Y hOS
    have hColXPY : Col X P Y := col_permutation_5_c X Y P hCol
    have hNBet : ¬ Bet X P Y := by
      intro hBet
      exact osp__ntsp_c A B C X Y hOS ⟨hNCopX, hNCopY, P, hCop, hBet⟩
    exact ⟨not_bet_out_c X P Y hColXPY hNBet, hNCopX⟩
  · intro h
    obtain ⟨hOut, hNCop⟩ := h
    exact cop_out__osp_c A B C X Y P hNCop hCop hOut

theorem cop2_ts__tsp_c (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : TS D E X Y) : TSP A B C X Y := by
  obtain ⟨HNCol, HNCol', T, hColTDE, hBetXTY⟩ := h₃
  have hDE : D ≠ E := fun e => HNCol (e ▸ col_trivial_2_c X D)
  have hColDET : Col D E T := col_permutation_1_c T D E hColTDE
  have hCopT : Coplanar A B C T := col_cop2__cop_c A B C D E T hDE h₁ h₂ hColDET
  have hTY : T ≠ Y := fun e => HNCol' (e ▸ hColTDE)
  have hColXTY : Col X T Y := bet_col_c X T Y hBetXTY
  have hColTYX : Col T Y X := col_permutation_1_c X T Y hColXTY
  have hNCopY : ¬ Coplanar A B C Y := by
    intro hCopY
    apply hNCop
    exact col_cop2__cop_c A B C T Y X hTY hCopT hCopY hColTYX
  exact ⟨hNCop, hNCopY, T, hCopT, hBetXTY⟩

theorem cop2_os__osp_c (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : OS D E X Y) : OSP A B C X Y := by
  obtain ⟨Z, hXZ, hYZ⟩ := h₃
  have hTSP_XZ : TSP A B C X Z := cop2_ts__tsp_c A B C D E X Z hNCop h₁ h₂ hXZ
  have hNCopZ : ¬ Coplanar A B C Z := tsp__ncop2_c A B C X Z hTSP_XZ
  have hTS_ZY : TS D E Z Y := l9_2_c D E Y Z hYZ
  have hTSP_ZY : TSP A B C Z Y := cop2_ts__tsp_c A B C D E Z Y hNCopZ h₁ h₂ hTS_ZY
  have hTSP_YZ : TSP A B C Y Z := l9_38_c A B C Z Y hTSP_ZY
  exact ⟨Z, hTSP_XZ, hTSP_YZ⟩

theorem cop3_tsp__ts_c (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : TSP A B C X Y) : TS D E X Y :=
  (let HX := tsp__ncop1_c A B C X Y h₄; (let HY := tsp__ncop2_c A B C X Y h₄; cop_nos__ts_c D E X Y h₃ ((fun H => HX (col_cop2__cop_c A B C D E X hDE h₁ h₂ (col_permutation_5_c D X E (col_permutation_4_c X D E H))))) ((fun H => HY (col_cop2__cop_c A B C D E Y hDE h₁ h₂ (col_permutation_5_c D Y E (col_permutation_4_c Y D E H))))) ((fun H => (let HTSP0 := tsp__nosp_c A B C X Y h₄; HTSP0 (cop2_os__osp_c A B C D E X Y HX h₁ h₂ H))))))

theorem cop3_osp__os_c (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : OSP A B C X Y) : OS D E X Y :=
  (let HX := osp__ncop1_c A B C X Y h₄; (let HY := osp__ncop2_c A B C X Y h₄; cop_nts__os_c D E X Y h₃ ((fun H => HX (col_cop2__cop_c A B C D E X hDE h₁ h₂ (col_permutation_5_c D X E (col_permutation_4_c X D E H))))) ((fun H => HY (col_cop2__cop_c A B C D E Y hDE h₁ h₂ (col_permutation_5_c D Y E (col_permutation_4_c Y D E H))))) ((fun H => (let HOSP0 := osp__ntsp_c A B C X Y h₄; HOSP0 (cop2_ts__tsp_c A B C D E X Y HX h₁ h₂ H))))))

theorem cop_tsp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : TSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := by
  rcases col_dec_c D E P with hcol | hncol
  · have hd := tsp_distincts_c A B C D E h
    rcases point_equality_decidability P A with hPA | hPA
    · refine ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c _ _, col_trivial_2_c _ _⟩⟩,
        ⟨P, Or.inl ⟨hcol, col_trivial_3_c _ _⟩⟩, ?_⟩
      rw [hPA]
      exact hd.1
    · exact ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c _ _, col_trivial_2_c _ _⟩⟩,
        ⟨P, Or.inl ⟨hcol, col_trivial_3_c _ _⟩⟩, hPA⟩
  · obtain ⟨_, _, T, hTcop, hbet⟩ := h
    have hColDET : Col D E T := col_permutation_5_c D T E (Or.inl hbet)
    refine ⟨T, hTcop, ⟨T, Or.inl ⟨hColDET, col_trivial_2_c _ _⟩⟩, ?_⟩
    intro e
    apply hncol
    rw [e]
    exact hColDET

theorem cop_osp__ex_cop2_c (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : OSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := by
  rcases col_dec_c D E P with hCol | hNCol
  · obtain ⟨hAB, -, -, -, -, -, -, -, -⟩ := osp_distincts_c A B C D E h
    rcases point_equality_decidability P A with hPA | hPA
    · subst hPA
      refine ⟨B, ⟨B, Or.inl ⟨col_trivial_2_c P B, col_trivial_2_c C B⟩⟩, ?_, hAB⟩
      exact ⟨P, Or.inl ⟨hCol, col_trivial_3_c P B⟩⟩
    · refine ⟨A, ⟨A, Or.inl ⟨col_trivial_3_c A B, col_trivial_2_c C A⟩⟩, ?_, hPA⟩
      exact ⟨P, Or.inl ⟨hCol, col_trivial_3_c P A⟩⟩
  · obtain ⟨E', hBetEPE', hCongPE'PE⟩ := segment_construction E P P E
    have hEP : E ≠ P := fun e => hNCol (e ▸ col_trivial_2_c D E)
    have hPE' : P ≠ E' := cong_diff_4_c P E' P E hEP hCongPE'PE
    have hColEPE' : Col E P E' := bet_col_c E P E' hBetEPE'
    have hColPE'E : Col P E' E := col_permutation_1_c E P E' hColEPE'
    have hNColDE'P : ¬ Col D E' P := by
      intro hColAssume
      have hColPE'D : Col P E' D := col_permutation_3_c D E' P hColAssume
      have hColPDE : Col P D E := col_transitivity_1_c P E' D E hPE' hColPE'D hColPE'E
      exact hNCol (col_permutation_1_c P D E hColPDE)
    have hNCopE : ¬ Coplanar A B C E := osp__ncop2_c A B C D E h
    have hTSP_EE' : TSP A B C E E' :=
      bet_cop__tsp_c A B C E E' P hNCopE hPE' hCop hBetEPE'
    have hOSPED : OSP A B C E D := osp_symmetry_c A B C D E h
    have hTSP_DE' : TSP A B C D E' := l9_41_2_c A B C E D E' hTSP_EE' hOSPED
    obtain ⟨Q, hCopQ, hCopDE'PQ, hPQ⟩ := cop_tsp__ex_cop2_c A B C D E' P hCop hTSP_DE'
    have hCopDE'PE : Coplanar D E' P E :=
      ⟨E, Or.inr (Or.inr ⟨col_trivial_2_c D E, col_permutation_4_c P E' E hColPE'E⟩)⟩
    have hNColE'DP : ¬ Col E' D P :=
      fun hh => hNColDE'P (col_permutation_4_c E' D P hh)
    have hCopDPQE : Coplanar D P Q E :=
      coplanar_trans_1_c E' D P Q E hNColE'DP
        (coplanar_perm_6_c D E' P Q hCopDE'PQ) (coplanar_perm_6_c D E' P E hCopDE'PE)
    have hCopDEPQ : Coplanar D E P Q := coplanar_perm_4_c D P Q E hCopDPQE
    exact ⟨Q, hCopQ, hCopDEPQ, hPQ⟩

theorem sac__coplanar_c (A B C D : Tpoint) (h : Saccheri A B C D) :
    Coplanar A B C D := by
  obtain ⟨_, _, _, hOS⟩ := h
  exact coplanar_perm_4_c A C D B (coplanar_perm_4_c A D B C (os__coplanar_c A D B C hOS))

#print axioms GeocoqTranslate.Tarski.Base.ts_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.l9_2_c
#print axioms GeocoqTranslate.Tarski.Base.mid_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.per_mid_per_c
#print axioms GeocoqTranslate.Tarski.Base.sym_preserve_diff_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_1_aux_c
#print axioms GeocoqTranslate.Tarski.Base.per_col_eq_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_1_c
#print axioms GeocoqTranslate.Tarski.Base.mid_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.col_preserves_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.out_out_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_2_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l9_4_2_c
#print axioms GeocoqTranslate.Tarski.Base.l9_5_c
#print axioms GeocoqTranslate.Tarski.Base.outer_pasch_c
#print axioms GeocoqTranslate.Tarski.Base.os_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.invert_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.l9_8_1_c
#print axioms GeocoqTranslate.Tarski.Base.not_two_sides_id_c
#print axioms GeocoqTranslate.Tarski.Base.l9_8_2_c
#print axioms GeocoqTranslate.Tarski.Base.l9_9_c
#print axioms GeocoqTranslate.Tarski.Base.l9_9_bis_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_chara_c
#print axioms GeocoqTranslate.Tarski.Base.l9_10_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.l9_17_c
#print axioms GeocoqTranslate.Tarski.Base.l9_18_c
#print axioms GeocoqTranslate.Tarski.Base.l9_19_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_not_col123_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_not_col124_c
#print axioms GeocoqTranslate.Tarski.Base.col_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.col_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.out_out_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.out_one_side_c
#print axioms GeocoqTranslate.Tarski.Base.bet__ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet_ts__ts_c
#print axioms GeocoqTranslate.Tarski.Base.bet_ts__os_c
#print axioms GeocoqTranslate.Tarski.Base.l9_31_c
#print axioms GeocoqTranslate.Tarski.Base.col123__nos_c
#print axioms GeocoqTranslate.Tarski.Base.col124__nos_c
#print axioms GeocoqTranslate.Tarski.Base.col2_os__os_c
#print axioms GeocoqTranslate.Tarski.Base.os_out_os_c
#print axioms GeocoqTranslate.Tarski.Base.ts_ts_os_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_not_col_c
#print axioms GeocoqTranslate.Tarski.Base.col_one_side_out_c
#print axioms GeocoqTranslate.Tarski.Base.col_two_sides_bet_c
#print axioms GeocoqTranslate.Tarski.Base.os_ts1324__os_c
#print axioms GeocoqTranslate.Tarski.Base.ts2__ex_bet2_c
#print axioms GeocoqTranslate.Tarski.Base.out_one_side_1_c
#print axioms GeocoqTranslate.Tarski.Base.out_two_sides_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.l8_21_bis_c
#print axioms GeocoqTranslate.Tarski.Base.ts__ncol_c
#print axioms GeocoqTranslate.Tarski.Base.one_or_two_sides_aux_c
#print axioms GeocoqTranslate.Tarski.Base.cop__one_or_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.os__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_trans_1_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.col2_cop__cop_c
#print axioms GeocoqTranslate.Tarski.Base.col_cop2__cop_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop2__cop_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_pseudo_trans_c
#print axioms GeocoqTranslate.Tarski.Base.l9_30_c
#print axioms GeocoqTranslate.Tarski.Base.cop_per2__col_c
#print axioms GeocoqTranslate.Tarski.Base.cop_perp2__col_c
#print axioms GeocoqTranslate.Tarski.Base.two_sides_dec_c
#print axioms GeocoqTranslate.Tarski.Base.cop_nts__os_c
#print axioms GeocoqTranslate.Tarski.Base.cop_nos__ts_c
#print axioms GeocoqTranslate.Tarski.Base.one_side_dec_c
#print axioms GeocoqTranslate.Tarski.Base.cop_dec_c
#print axioms GeocoqTranslate.Tarski.Base.ex_diff_cop_c
#print axioms GeocoqTranslate.Tarski.Base.ex_ncol_cop_c
#print axioms GeocoqTranslate.Tarski.Base.ex_ncol_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.col2_cop2__eq_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_cop2__col_c
#print axioms GeocoqTranslate.Tarski.Base.l9_38_c
#print axioms GeocoqTranslate.Tarski.Base.l9_39_c
#print axioms GeocoqTranslate.Tarski.Base.l9_41_1_c
#print axioms GeocoqTranslate.Tarski.Base.l9_41_2_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_exists_c
#print axioms GeocoqTranslate.Tarski.Base.osp_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.osp_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.osp_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_tsp__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_osp__osp_c
#print axioms GeocoqTranslate.Tarski.Base.ncop_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.tsp_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.osp_distincts_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ncop1_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ncop2_c
#print axioms GeocoqTranslate.Tarski.Base.tsp__nosp_c
#print axioms GeocoqTranslate.Tarski.Base.osp__ntsp_c
#print axioms GeocoqTranslate.Tarski.Base.osp_bet__osp_c
#print axioms GeocoqTranslate.Tarski.Base.l9_18_3_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cop__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop_out__osp_c
#print axioms GeocoqTranslate.Tarski.Base.l9_19_3_c
#print axioms GeocoqTranslate.Tarski.Base.cop2_ts__tsp_c
#print axioms GeocoqTranslate.Tarski.Base.cop2_os__osp_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_tsp__ts_c
#print axioms GeocoqTranslate.Tarski.Base.cop3_osp__os_c
#print axioms GeocoqTranslate.Tarski.Base.cop_tsp__ex_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.cop_osp__ex_cop2_c
#print axioms GeocoqTranslate.Tarski.Base.sac__coplanar_c

#print axioms GeocoqTranslate.Tarski.Base.col__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.ncop__ncol_c
#print axioms GeocoqTranslate.Tarski.Base.ts__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.perp__coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_1_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_2_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_4_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_6_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_8_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_9_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_12_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_16_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_17_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_18_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_19_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_21_c
end GeocoqTranslate.Tarski.Base
