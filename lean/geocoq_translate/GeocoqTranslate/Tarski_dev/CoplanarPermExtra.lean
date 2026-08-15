import GeocoqTranslate.Tarski_dev.Ch10

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem coplanar_perm_3_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar A C D B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨H1, H2⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H2, (col_permutation_5_c D x B (col_permutation_1_c B D x H3))⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H2, (col_permutation_4_c B C x H3)⟩))))⟩

theorem coplanar_perm_5_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar A D C B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨H1, (col_permutation_4_c C D x H2)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H2, (col_permutation_4_c B D x H3)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H2, (col_permutation_5_c C x B (col_permutation_1_c B C x H3))⟩)))⟩

theorem coplanar_perm_7_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B A D C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨(col_permutation_5_c B x A (col_permutation_1_c A B x H1)), (col_permutation_5_c D x C (col_permutation_1_c C D x H2))⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H3, H2⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H3, H2⟩))))⟩

theorem coplanar_perm_10_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B D A C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨(col_permutation_4_c A B x H1), (col_permutation_4_c C D x H2)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H3, H2⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨H3, (col_permutation_4_c A D x H2)⟩))))⟩

theorem coplanar_perm_11_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar B D C A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨(col_permutation_4_c A B x H1), (col_permutation_4_c C D x H2)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨H3, (col_permutation_5_c C x A (col_permutation_1_c A C x H2))⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨H3, (col_permutation_4_c A D x H2)⟩))))⟩

theorem coplanar_perm_13_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C A D B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨H2, H1⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c C x A (col_permutation_1_c A C x H2)), (col_permutation_5_c D x B (col_permutation_1_c B D x H3))⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c B C x H3), H2⟩))))⟩

theorem coplanar_perm_14_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C B A D := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨H2, (col_permutation_4_c A B x H1)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c A C x H2), H3⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c C x B (col_permutation_1_c B C x H3)), H2⟩)))⟩

theorem coplanar_perm_15_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar C B D A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inl (⟨H2, (col_permutation_4_c A B x H1)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c A C x H2), H3⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c C x B (col_permutation_1_c B C x H3)), (col_permutation_5_c D x A (col_permutation_1_c A D x H2))⟩)))⟩

theorem coplanar_perm_20_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D B A C := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inr (Or.inr (⟨(col_permutation_4_c C D x H2), (col_permutation_4_c A B x H1)⟩))
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inl (⟨(col_permutation_5_c D x B (col_permutation_1_c B D x H3)), H2⟩)
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c A D x H2), H3⟩))))⟩

theorem coplanar_perm_22_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D C A B := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨(col_permutation_5_c D x C (col_permutation_1_c C D x H2)), H1⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c B D x H3), (col_permutation_4_c A C x H2)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c A D x H2), (col_permutation_4_c B C x H3)⟩))))⟩

theorem coplanar_perm_23_c (A B C D : Tpoint) (H : Coplanar A B C D) : Coplanar D C B A := by
  obtain ⟨x, x0⟩ := H
  exact ⟨x, ((by
  rcases x0 with H0 | H0
  · obtain ⟨H1, H2⟩ := H0
    exact Or.inl (⟨(col_permutation_5_c D x C (col_permutation_1_c C D x H2)), (col_permutation_5_c B x A (col_permutation_1_c A B x H1))⟩)
  · rcases H0 with H1 | H1
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inl (⟨(col_permutation_4_c B D x H3), (col_permutation_4_c A C x H2)⟩))
    · obtain ⟨H2, H3⟩ := H1
      exact Or.inr (Or.inr (⟨(col_permutation_4_c A D x H2), (col_permutation_4_c B C x H3)⟩))))⟩

theorem invert_two_sides_c (A B P Q : Tpoint) (H : TS A B P Q) : TS B A P Q := by
  obtain ⟨H0, H1⟩ := H
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(not_col_permutation_5_c P A B H0), (⟨(not_col_permutation_5_c Q A B H2), ((by
  obtain ⟨T, H4⟩ := H3
  obtain ⟨H5, H6⟩ := H4
  exact ⟨T, (⟨(col_permutation_5_c T A B H5), H6⟩)⟩))⟩)⟩

theorem coplanar_trivial_c (A B C : Tpoint) : Coplanar A A B C :=
  ⟨B, (Or.inl (⟨(col_trivial_1_c A B), (col_trivial_3_c B C)⟩))⟩


theorem reflectl_coplanar_c (A B C D : Tpoint) (H : ReflectL A B C D) : Coplanar A B C D := by
  obtain ⟨⟨X, hMid, hColCD⟩, _⟩ := H
  obtain ⟨hBet, _⟩ := hMid
  exact ⟨X, Or.inl ⟨col_permutation_2_c B X A (bet_col_c B X A hBet), hColCD⟩⟩

theorem reflect_coplanar_c (A B C D : Tpoint) (H : Reflect A B C D) : Coplanar A B C D := by
  rcases H with ⟨_, hR⟩ | ⟨heq, hMid⟩
  · exact reflectl_coplanar_c A B C D hR
  · subst heq
    exact coplanar_perm_16_c C C A B (coplanar_trivial_c C A B)

theorem inangle_coplanar_c (A B C D : Tpoint) (H : InAngle A B C D) : Coplanar A B C D := by
  obtain ⟨_, _, _, X, hBet, hDij⟩ := H
  refine ⟨X, Or.inr (Or.inl ⟨?_, col_permutation_5_c B X D (bet_col_c B X D hBet)⟩)⟩
  rcases hDij with h4 | h4
  · subst h4
    exact col_trivial_2_c A X
  · exact col_permutation_2_c C X A (out_col_c C X A h4)

#print axioms GeocoqTranslate.Tarski.Base.reflectl_coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.reflect_coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.inangle_coplanar_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_3_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_5_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_7_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_10_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_11_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_13_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_14_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_15_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_20_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_22_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_perm_23_c
#print axioms GeocoqTranslate.Tarski.Base.invert_two_sides_c
#print axioms GeocoqTranslate.Tarski.Base.coplanar_trivial_c
end GeocoqTranslate.Tarski.Base
