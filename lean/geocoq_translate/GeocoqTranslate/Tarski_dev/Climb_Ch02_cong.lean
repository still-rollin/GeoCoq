import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem cong_reflexivity_c (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B (cong_pseudo_reflexivity B A) (cong_pseudo_reflexivity B A)

theorem cong_symmetry_c (A B C D : Tpoint) (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_reflexivity A B)

theorem cong_transitivity_c (A B C D E F : Tpoint)
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symmetry h1) h2

theorem cong_left_commutativity_c (A B C D : Tpoint)
    (h : Cong A B C D) : Cong B A C D :=
  cong_inner_transitivity A B B A C D (cong_symmetry (cong_pseudo_reflexivity B A)) h

theorem cong_right_commutativity_c (A B C D : Tpoint)
    (h : Cong A B C D) : Cong A B D C :=
  cong_symmetry ((let H0 := cong_symmetry h; cong_left_commutativity H0))

theorem cong_3421_c (A B C D : Tpoint) (h : Cong A B C D) : Cong C D B A :=
  cong_right_commutativity (cong_right_commutativity (cong_right_commutativity (cong_symmetry h)))

theorem cong_4312_c (A B C D : Tpoint) (h : Cong A B C D) : Cong D C A B :=
  cong_right_commutativity (cong_right_commutativity (cong_symmetry (cong_right_commutativity h)))

theorem cong_4321_c (A B C D : Tpoint) (h : Cong A B C D) : Cong D C B A :=
  cong_right_commutativity (cong_symmetry (cong_right_commutativity h))

theorem cong_trivial_identity_c (A B : Tpoint) : Cong A A B B := sorry

theorem cong_reverse_identity_c (A C D : Tpoint) (h : Cong A A C D) : C = D :=
  (let H0 := cong_symmetry h; cong_identity C D A H0)

theorem cong_commutativity_c (A B C D : Tpoint) (h : Cong A B C D) : Cong B A D C :=
  cong_left_commutativity (cong_right_commutativity h)

theorem not_cong_2134_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A C D :=
  (fun H0 => h (cong_symmetry (cong_3421_c B A C D H0)))

theorem not_cong_1243_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong A B D C :=
  (fun H0 => h (cong_symmetry (cong_4312_c A B D C H0)))

theorem not_cong_2143_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A D C :=
  (fun H0 => h (cong_symmetry (cong_4321_c B A D C H0)))

theorem not_cong_3412_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D A B :=
  (fun H0 => h (cong_symmetry H0))

theorem not_cong_4312_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C A B :=
  (fun H0 => h (cong_symmetry (cong_left_commutativity H0)))

theorem not_cong_3421_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D B A :=
  (fun H0 => h (cong_symmetry (cong_right_commutativity H0)))

theorem not_cong_4321_c (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C B A :=
  (fun H0 => h (cong_symmetry (cong_commutativity H0)))

theorem five_segment_with_def_c (A B C D A' B' C' D' : Tpoint)
    (h : OFSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨H1, H2⟩ := h
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  exact five_segment A A' B B' C C' D D' H5 H7 H9 H10 H1 H3 hAB

theorem cong_diff_c (A B C D : Tpoint) (hAB : A ≠ B) (h : Cong A B C D) : C ≠ D := by
  exact fun H1 => eq_ind_r (fun C0 => Cong A B C0 D - > False) (fun H2 => hAB (cong_identity A B D H2)) H1 h

theorem cong_diff_2_c (A B C D : Tpoint) (hBA : B ≠ A) (h : Cong A B C D) : C ≠ D := by
  exact fun H1 => eq_ind_r (fun C0 => Cong A B C0 D - > False) (fun H2 => hBA (Eq.symm (cong_identity A B D H2))) H1 h

theorem cong_diff_3_c (A B C D : Tpoint) (hCD : C ≠ D) (h : Cong A B C D) : A ≠ B := by
  exact fun H1 => eq_ind_r (fun A0 => Cong A0 B C D - > False) (fun H2 => hCD (cong_identity C D B (cong_symmetry H2))) H1 h

theorem cong_diff_4_c (A B C D : Tpoint) (hDC : D ≠ C) (h : Cong A B C D) : A ≠ B := by
  exact fun H1 => eq_ind_r (fun A0 => Cong A0 B C D - > False) (fun H2 => hDC (Eq.symm (cong_identity C D B (cong_symmetry H2)))) H1 h

theorem cong_3_sym_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem cong_3_swap_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 B A C B' A' C' := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry (cong_symmetry (cong_symmetry (cong_4321_c A B A' B' H0)))), (⟨H3, H2⟩)⟩

theorem cong_3_swap_2_c (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A C B A' C' B' := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨H2, (⟨H0, (cong_symmetry (cong_symmetry (cong_symmetry (cong_4321_c B C B' C' H3))))⟩)⟩

theorem cong3_transitivity_c (A0 B0 C0 A1 B1 C1 A2 B2 C2 : Tpoint)
    (h1 : Cong_3 A0 B0 C0 A1 B1 C1) (h2 : Cong_3 A1 B1 C1 A2 B2 C2) :
    Cong_3 A0 B0 C0 A2 B2 C2 := by
  obtain ⟨H1, H2⟩ := h2
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := h1
  obtain ⟨H7, H8⟩ := H6
  exact ⟨(cong_transitivity H5 H1), (⟨(cong_transitivity H7 H3), (cong_transitivity H8 H4)⟩)⟩

theorem eq_dec_points_c (A B : Tpoint) : A = B ∨ A ≠ B := sorry

theorem distinct_c (P Q R : Tpoint) (hPQ : P ≠ Q) : R ≠ P ∨ R ≠ Q := by
  have o := point_equality_decidability R P
  rcases o with H0 | H0
  · subst H0
    exact Or.inr hPQ
  · exact Or.inl H0

theorem l2_11_c (A B C A' B' C' : Tpoint)
    (h1 : Bet A B C) (h2 : Bet A' B' C')
    (h3 : Cong A B A' B') (h4 : Cong B C B' C') : Cong A C A' C' := by
  have o := point_equality_decidability A B
  rcases o with H3 | H3
  · exact eq_ind A (fun B0 => Bet A B0 C - > Cong A B0 A' B' - > Cong B0 C B' C' - > Cong A C A' C') (fun _ H4 H5 => (let H6 := cong_identity A' B' A (cong_symmetry H4); eq_ind_r (fun A'0 => Bet A'0 B' C' - > Cong A A A'0 B' - > Cong A C A'0 C') (fun _ _ => H5) H6 h2 H4)) B H3 h1 h3 h4
  · exact cong_commutativity (five_segment A A' B B' C C' A A' h3 h4 (cong_trivial_identity A A') (cong_symmetry (cong_symmetry (cong_commutativity h3))) h1 h2 H3)

theorem bet_cong3_c (A B C A' B' : Tpoint)
    (h1 : Bet A B C) (h2 : Cong A B A' B') : ∃ C', Cong_3 A B C A' B' C' := by
  have H1 := segment_construction A' B' B C
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := l2_11 h1 H3 h2 (cong_symmetry H4)
  exact ⟨x, (⟨h2, (⟨H5, (cong_symmetry H4)⟩)⟩)⟩

theorem construction_uniqueness_c (Q A B C X Y : Tpoint)
    (hQA : Q ≠ A) (hBet1 : Bet Q A X) (hCong1 : Cong A X B C)
    (hBet2 : Bet Q A Y) (hCong2 : Cong A Y B C) : X = Y := sorry

theorem Cong_cases_c (A B C D : Tpoint)
    (h : Cong A B C D ∨ Cong A B D C ∨ Cong B A C D ∨ Cong B A D C ∨
         Cong C D A B ∨ Cong C D B A ∨ Cong D C A B ∨ Cong D C B A) :
    Cong A B C D := by
  have H0 := h
  rcases H0 with H1 | H1
  · exact H1
  · rcases H1 with H2 | H2
    · exact cong_symmetry (cong_symmetry (cong_right_commutativity H2))
    · rcases H2 with H3 | H3
      · exact cong_symmetry (cong_symmetry (cong_left_commutativity H3))
      · rcases H3 with H4 | H4
        · exact cong_symmetry (cong_symmetry (cong_commutativity H4))
        · rcases H4 with H5 | H5
          · exact cong_symmetry H5
          · rcases H5 with H6 | H6
            · exact cong_symmetry (cong_symmetry (cong_4312_c C D B A H6))
            · rcases H6 with H7 | H7
              · exact cong_symmetry (cong_symmetry (cong_3421_c D C A B H7))
              · exact cong_symmetry (cong_symmetry (cong_4321_c D C B A H7))

theorem Cong_perm_c (A B C D : Tpoint) (h : Cong A B C D) :
    Cong A B C D ∧ Cong A B D C ∧ Cong B A C D ∧ Cong B A D C ∧
    Cong C D A B ∧ Cong C D B A ∧ Cong D C A B ∧ Cong D C B A :=
  ⟨h, (⟨(cong_symmetry (cong_symmetry (cong_right_commutativity h))), (⟨(cong_symmetry (cong_symmetry (cong_left_commutativity h))), (⟨(cong_symmetry (cong_symmetry (cong_commutativity h))), (⟨(cong_symmetry h), (⟨(cong_symmetry (cong_symmetry (cong_3421_c A B C D h))), (⟨(cong_symmetry (cong_symmetry (cong_4312_c A B C D h))), (cong_symmetry (cong_symmetry (cong_4321_c A B C D h)))⟩)⟩)⟩)⟩)⟩)⟩)⟩

#print axioms GeocoqTranslate.Tarski.Base.cong_reflexivity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_symmetry_c
#print axioms GeocoqTranslate.Tarski.Base.cong_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_left_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_right_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3421_c
#print axioms GeocoqTranslate.Tarski.Base.cong_4312_c
#print axioms GeocoqTranslate.Tarski.Base.cong_4321_c
#print axioms GeocoqTranslate.Tarski.Base.cong_trivial_identity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_reverse_identity_c
#print axioms GeocoqTranslate.Tarski.Base.cong_commutativity_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_2134_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_1243_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_2143_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_3412_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_4312_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_3421_c
#print axioms GeocoqTranslate.Tarski.Base.not_cong_4321_c
#print axioms GeocoqTranslate.Tarski.Base.five_segment_with_def_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_3_c
#print axioms GeocoqTranslate.Tarski.Base.cong_diff_4_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_sym_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_swap_c
#print axioms GeocoqTranslate.Tarski.Base.cong_3_swap_2_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_transitivity_c
#print axioms GeocoqTranslate.Tarski.Base.eq_dec_points_c
#print axioms GeocoqTranslate.Tarski.Base.distinct_c
#print axioms GeocoqTranslate.Tarski.Base.l2_11_c
#print axioms GeocoqTranslate.Tarski.Base.bet_cong3_c
#print axioms GeocoqTranslate.Tarski.Base.construction_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.Cong_cases_c
#print axioms GeocoqTranslate.Tarski.Base.Cong_perm_c
end GeocoqTranslate.Tarski.Base