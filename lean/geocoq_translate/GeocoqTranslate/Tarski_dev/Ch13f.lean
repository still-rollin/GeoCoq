import GeocoqTranslate.Tarski_dev.Ch13e

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_euclidean Tpoint]

theorem l13_15_1_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C → ¬ Par O B A C → Coplanar O B A C → Par_strict A B A' B' → Par_strict A C A' C' → Col O A A' → Col O B B' → Col O C C' → Par B C B' C' := sorry

theorem l13_15_2_aux_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C → ¬ Par O A B C → Par O B A C → Par_strict A B A' B' → Par_strict A C A' C' → Col O A A' → Col O B B' → Col O C C' → Par B C B' C' := sorry

theorem l13_15_2_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C → Par O B A C → Par_strict A B A' B' → Par_strict A C A' C' → Col O A A' → Col O B B' → Col O C C' → Par B C B' C' := sorry

theorem l13_15_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C → Coplanar O B A C → Par_strict A B A' B' → Par_strict A C A' C' → Col O A A' → Col O B B' → Col O C C' → Par B C B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  have o := par_dec_c b6 b1 b0 b2
  rcases o with H6 | H6
  · exact l13_15_2_c b0 b1 b2 b3 b4 b5 b6 b7 H6 b9 b10 b11 b12 b13
  · exact l13_15_1_c b0 b1 b2 b3 b4 b5 b6 b7 H6 b8 b9 b10 b11 b12 b13
theorem l13_15_par_c :
    ∀ (A B C A' B' C' : Tpoint), ¬ Col A B C → Par_strict A B A' B' → Par_strict A C A' C' → Par A A' B B' → Par A A' C C' → Par B C B' C' := sorry

theorem l13_18_2_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C → Par_strict A B A' B' → Par_strict A C A' C' → (Par_strict B C B' C' ∧ Col O A A' ∧ Col O B B' → Col O C C') := sorry

theorem l13_18_3_c :
    ∀ (A B C A' B' C' : Tpoint), ¬ Col A B C → Par_strict A B A' B' → Par_strict A C A' C' → (Par_strict B C B' C' ∧ Par A A' B B') → (Par C C' A A' ∧ Par C C' B B') := sorry

theorem l13_18_c :
    ∀ (A B C A' B' C' O : Tpoint), ¬ Col A B C ∧ Par_strict A B A' B' ∧ Par_strict A C A' C' → (Par_strict B C B' C' ∧ Col O A A' ∧ Col O B B' → Col O C C') ∧ ((Par_strict B C B' C' ∧ Par A A' B B') → (Par C C' A A' ∧ Par C C' B B')) ∧ (Par A A' B B' ∧ Par A A' C C' → Par B C B' C') := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H0, H1⟩ := b7
  obtain ⟨H2, H3⟩ := H1
  exact ⟨(fun H4 => l13_18_2_c b1 b2 b3 b4 b5 b6 H0 H2 H3 H4), (⟨(fun H4 => (by
  obtain ⟨H5, H6⟩ := H4
  exact l13_18_3_c b0 b1 b2 b3 b4 b5 H0 H2 H3 (⟨H5, H6⟩))), (fun H4 => (by
  obtain ⟨H5, H6⟩ := H4
  exact l13_15_par_c b0 b1 b2 b3 b4 b5 H0 H2 H3 H5 H6))⟩)⟩
theorem l13_19_aux_c :
    ∀ (A B C D A' B' C' D' O : Tpoint), ¬ Col O A B → A ≠ A' → A ≠ C → O ≠ A → O ≠ A' → O ≠ C → O ≠ C' → O ≠ B → O ≠ B' → O ≠ D → O ≠ D' → Col O A C → Col O A A' → Col O A C' → Col O B D → Col O B B' → Col O B D' → ¬ Par A B C D → Par A B A' B' → Par A D A' D' → Par B C B' C' → Par C D C' D' := sorry

theorem l13_19_c :
    ∀ (A B C D A' B' C' D' O : Tpoint), ¬ Col O A B → O ≠ A → O ≠ A' → O ≠ C → O ≠ C' → O ≠ B → O ≠ B' → O ≠ D → O ≠ D' → Col O A C → Col O A A' → Col O A C' → Col O B D → Col O B B' → Col O B D' → Par A B A' B' → Par A D A' D' → Par B C B' C' → Par C D C' D' := sorry

theorem l13_19_par_aux_c :
    ∀ (A B C D A' B' C' D' X Y : Tpoint), X ≠ A → X ≠ A' → X ≠ C → X ≠ C' → Y ≠ B → Y ≠ B' → Y ≠ D → Y ≠ D' → Col X A C → Col X A A' → Col X A C' → Col Y B D → Col Y B B' → Col Y B D' → A ≠ C → B ≠ D → A ≠ A' → Par_strict X A Y B → ¬ Par A B C D → Par A B A' B' → Par A D A' D' → Par B C B' C' → Par C D C' D' := sorry

theorem l13_19_par_c :
    ∀ (A B C D A' B' C' D' X Y : Tpoint), X ≠ A → X ≠ A' → X ≠ C → X ≠ C' → Y ≠ B → Y ≠ B' → Y ≠ D → Y ≠ D' → Col X A C → Col X A A' → Col X A C' → Col Y B D → Col Y B B' → Col Y B D' → Par_strict X A Y B → Par A B A' B' → Par A D A' D' → Par B C B' C' → Par C D C' D' := sorry

#print axioms GeocoqTranslate.Tarski.Base.l13_15_1_c
#print axioms GeocoqTranslate.Tarski.Base.l13_15_2_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l13_15_2_c
#print axioms GeocoqTranslate.Tarski.Base.l13_15_c
#print axioms GeocoqTranslate.Tarski.Base.l13_15_par_c
#print axioms GeocoqTranslate.Tarski.Base.l13_18_2_c
#print axioms GeocoqTranslate.Tarski.Base.l13_18_3_c
#print axioms GeocoqTranslate.Tarski.Base.l13_18_c
#print axioms GeocoqTranslate.Tarski.Base.l13_19_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l13_19_c
#print axioms GeocoqTranslate.Tarski.Base.l13_19_par_aux_c
#print axioms GeocoqTranslate.Tarski.Base.l13_19_par_c
end GeocoqTranslate.Tarski.Base