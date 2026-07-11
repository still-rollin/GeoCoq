import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem col_permutation_1_ax (A B C : Tpoint) (h : Col A B C) : Col B C A := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr H0)
  · rcases H0 with H1 | H1
    · exact Or.inl H1
    · exact Or.inr (Or.inl H1)

theorem col_permutation_2_ax (A B C : Tpoint) (h : Col A B C) : Col C A B := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inl H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inr H1)
    · exact Or.inl H1

theorem col_permutation_3_ax (A B C : Tpoint) (h : Col A B C) : Col C B A := by
  rcases h with H0 | H0
  · exact Or.inl (between_symmetry H0)
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inr (between_symmetry H1))
    · exact Or.inr (Or.inl (between_symmetry H1))

theorem col_permutation_4_ax (A B C : Tpoint) (h : Col A B C) : Col B A C := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inr (between_symmetry H0))
  · rcases H0 with H1 | H1
    · exact Or.inr (Or.inl (between_symmetry H1))
    · exact Or.inl (between_symmetry H1)

theorem col_permutation_5_ax (A B C : Tpoint) (h : Col A B C) : Col A C B := by
  rcases h with H0 | H0
  · exact Or.inr (Or.inl (between_symmetry H0))
  · rcases H0 with H1 | H1
    · exact Or.inl (between_symmetry H1)
    · exact Or.inr (Or.inr (between_symmetry H1))

theorem col_trivial_1_ax (A B : Tpoint) : Col A A B :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_trivial B A))))

theorem col_trivial_2_ax (A B : Tpoint) : Col A B B :=
  Or.inr (Or.inl (between_symmetry (between_symmetry (between_trivial2 B A))))

theorem col_trivial_3_ax (A B : Tpoint) : Col A B A :=
  Or.inr (Or.inr (between_symmetry (between_symmetry (between_symmetry (between_trivial B A)))))

theorem l4_18_ax (A B C C' : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' :=
  cong_identity C C' C (l4_17 hAB hCol (cong_symmetry h₁) (cong_symmetry h₂))

#print axioms GeocoqTranslate.Tarski.Base.col_permutation_1_ax
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_2_ax
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_3_ax
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_4_ax
#print axioms GeocoqTranslate.Tarski.Base.col_permutation_5_ax
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_1_ax
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_2_ax
#print axioms GeocoqTranslate.Tarski.Base.col_trivial_3_ax
#print axioms GeocoqTranslate.Tarski.Base.l4_18_ax

end GeocoqTranslate.Tarski.Base