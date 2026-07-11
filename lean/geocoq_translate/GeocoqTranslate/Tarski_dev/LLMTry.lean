import GeocoqTranslate.Tarski_dev.Climb_All
namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality
variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem le_transitivity_llm (A B C D E F : Tpoint) (h₁ : Le A B C D) (h₂ : Le C D E F) : Le A B E F := by

  obtain ⟨y, H2, H3⟩ := h₁
  obtain ⟨z, H5, H6⟩ := h₂
  obtain ⟨P, H9, H10⟩ := l4_5_c C y D E z H2 H6
  obtain ⟨H11, H12, H13⟩ := H10
  exact ⟨P, between_symmetry_c F P E (between_symmetry_c E P F (between_exchange4_c E P z F H9 H5)), cong_transitivity_c A B C y E P H3 H11⟩

#print axioms GeocoqTranslate.Tarski.Base.le_transitivity_llm
end GeocoqTranslate.Tarski.Base