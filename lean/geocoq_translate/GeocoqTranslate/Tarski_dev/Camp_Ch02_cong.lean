import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem cong_reflexivity_ax (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B (cong_pseudo_reflexivity B A) (cong_pseudo_reflexivity B A)

theorem cong_symmetry_ax (A B C D : Tpoint) (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_reflexivity A B)

theorem cong_transitivity_ax (A B C D E F : Tpoint)
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symmetry h1) h2

theorem cong_left_commutativity_ax (A B C D : Tpoint)
    (h : Cong A B C D) : Cong B A C D :=
  cong_inner_transitivity A B B A C D (cong_symmetry (cong_pseudo_reflexivity B A)) h

theorem cong_right_commutativity_ax (A B C D : Tpoint)
    (h : Cong A B C D) : Cong A B D C :=
  cong_symmetry ((let H0 := cong_symmetry h; cong_left_commutativity H0))

theorem cong_3421_ax (A B C D : Tpoint) (h : Cong A B C D) : Cong C D B A :=
  cong_right_commutativity (cong_right_commutativity (cong_right_commutativity (cong_symmetry h)))

theorem cong_4312_ax (A B C D : Tpoint) (h : Cong A B C D) : Cong D C A B :=
  cong_right_commutativity (cong_right_commutativity (cong_symmetry (cong_right_commutativity h)))

theorem cong_4321_ax (A B C D : Tpoint) (h : Cong A B C D) : Cong D C B A :=
  cong_right_commutativity (cong_symmetry (cong_right_commutativity h))

theorem cong_reverse_identity_ax (A C D : Tpoint) (h : Cong A A C D) : C = D :=
  (let H0 := cong_symmetry h; cong_identity C D A H0)

theorem cong_commutativity_ax (A B C D : Tpoint) (h : Cong A B C D) : Cong B A D C :=
  cong_left_commutativity (cong_right_commutativity h)

theorem five_segment_with_def_ax (A B C D A' B' C' D' : Tpoint)
    (h : OFSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨H1, H2⟩ := h
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨H9, H10⟩ := H8
  exact five_segment A A' B B' C C' D D' H5 H7 H9 H10 H1 H3 hAB

theorem cong_3_sym_ax (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨H0, H1⟩ := h
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(cong_symmetry H0), (⟨(cong_symmetry H2), (cong_symmetry H3)⟩)⟩

theorem cong3_transitivity_ax (A0 B0 C0 A1 B1 C1 A2 B2 C2 : Tpoint)
    (h1 : Cong_3 A0 B0 C0 A1 B1 C1) (h2 : Cong_3 A1 B1 C1 A2 B2 C2) :
    Cong_3 A0 B0 C0 A2 B2 C2 := by
  obtain ⟨H1, H2⟩ := h2
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := h1
  obtain ⟨H7, H8⟩ := H6
  exact ⟨(cong_transitivity H5 H1), (⟨(cong_transitivity H7 H3), (cong_transitivity H8 H4)⟩)⟩

theorem distinct_ax (P Q R : Tpoint) (hPQ : P ≠ Q) : R ≠ P ∨ R ≠ Q := by
  have o := point_equality_decidability R P
  rcases o with H0 | H0
  · subst H0
    exact Or.inr hPQ
  · exact Or.inl H0

theorem bet_cong3_ax (A B C A' B' : Tpoint)
    (h1 : Bet A B C) (h2 : Cong A B A' B') : ∃ C', Cong_3 A B C A' B' C' := by
  have H1 := segment_construction A' B' B C
  obtain ⟨x, H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have H5 := l2_11 h1 H3 h2 (cong_symmetry H4)
  exact ⟨x, (⟨h2, (⟨H5, (cong_symmetry H4)⟩)⟩)⟩

#print axioms GeocoqTranslate.Tarski.Base.cong_reflexivity_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_symmetry_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_transitivity_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_left_commutativity_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_right_commutativity_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_3421_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_4312_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_4321_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_reverse_identity_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_commutativity_ax
#print axioms GeocoqTranslate.Tarski.Base.five_segment_with_def_ax
#print axioms GeocoqTranslate.Tarski.Base.cong_3_sym_ax
#print axioms GeocoqTranslate.Tarski.Base.cong3_transitivity_ax
#print axioms GeocoqTranslate.Tarski.Base.distinct_ax
#print axioms GeocoqTranslate.Tarski.Base.bet_cong3_ax

end GeocoqTranslate.Tarski.Base