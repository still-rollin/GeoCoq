import GeocoqTranslate.Tarski_dev.CoplanarPermExtra

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem cop__cong_on_bissect_c :
    ∀ (A B M P X : Tpoint), Coplanar A B X P → Midpoint M A B → Perp_at M A B P M → Cong X A X B → Col M P X := sorry

theorem cong_cop_mid_perp__col_c :
    ∀ (A B M P X : Tpoint), Coplanar A B X P → Cong A X B X → Midpoint M A B → Perp A B P M → Col M P X := sorry

theorem cop_image_in2__col_c :
    ∀ (A B P P' Q Q' M : Tpoint), Coplanar A B P Q → ReflectL_at M P P' A B → ReflectL_at M Q Q' A B → Col M P Q := sorry

theorem l10_10_spec_c :
    ∀ (A B P Q P' Q' : Tpoint), ReflectL P' P A B → ReflectL Q' Q A B → Cong P Q P' Q' := sorry

theorem l10_10_c :
    ∀ (A B P Q P' Q' : Tpoint), Reflect P' P A B → Reflect Q' Q A B → Cong P Q P' Q' := sorry

theorem image_preserves_bet_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Bet A B C → Bet A' B' C' := sorry

theorem image_gen_preserves_bet_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Bet A B C → Bet A' B' C' := sorry

theorem image_preserves_col_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Col A B C → Col A' B' C' := sorry

theorem image_gen_preserves_col_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Col A B C → Col A' B' C' := sorry

theorem image_gen_preserves_ncol_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → ¬ Col A B C → ¬ Col A' B' C' := sorry

theorem image_gen_preserves_inter_c :
    ∀ (A B C D I A' B' C' D' I' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Reflect D D' X Y → ¬ Col A B C → C ≠ D → Col A B I → Col C D I → Col A' B' I' → Col C' D' I' → Reflect I I' X Y := sorry

theorem intersection_with_image_gen_c :
    ∀ (A B C A' B' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → ¬ Col A B A' → Col A B C → Col A' B' C → Col C X Y := sorry

theorem image_preserves_midpoint_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Midpoint A B C → Midpoint A' B' C' := sorry

theorem image_spec_preserves_per_c :
    ∀ (A B C A' B' C' X Y : Tpoint), ReflectL A A' X Y → ReflectL B B' X Y → ReflectL C C' X Y → Per A B C → Per A' B' C' := sorry

theorem image_preserves_per_c :
    ∀ (A B C A' B' C' X Y : Tpoint), Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Per A B C → Per A' B' C' := sorry

theorem l10_12_c :
    ∀ (A B C A' B' C' : Tpoint), Per A B C → Per A' B' C' → Cong A B A' B' → Cong B C B' C' → Cong A C A' C' := sorry
theorem l10_16_c :
    ∀ (A B C A' B' P : Tpoint), ¬ Col A B C → ¬ Col A' B' P → Cong A B A' B' → ∃ (C' : Tpoint), Cong_3 A B C A' B' C' ∧ OS A' B' P C' := sorry

theorem cong_cop_image__col_c :
    ∀ (A B P P' X : Tpoint), P ≠ P' → Reflect P P' A B → Cong P X P' X → Coplanar A B P X → Col A B X := sorry

theorem cong_cop_per2_1_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ Midpoint B X Y := sorry

theorem cong_cop_per2_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ ReflectL X Y A B := sorry

theorem cong_cop_per2_gen_c :
    ∀ (A B X Y : Tpoint), A ≠ B → Per A B X → Per A B Y → Cong B X B Y → Coplanar A B X Y → X = Y ∨ Reflect X Y A B := sorry

theorem ex_perp_cop_c :
    ∀ (A B C P : Tpoint), A ≠ B → ∃ (Q : Tpoint), Perp A B Q C ∧ Coplanar A B P Q := sorry
theorem hilbert_s_version_of_pasch_aux_c :
    ∀ (A B C I P : Tpoint), Coplanar A B C P → ¬ Col A I P → ¬ Col B C P → Bet B I C → B ≠ I → I ≠ C → B ≠ C → ∃ (X : Tpoint), Col I P X ∧ ((Bet A X B ∧ A ≠ X ∧ X ≠ B ∧ A ≠ B) ∨ (Bet A X C ∧ A ≠ X ∧ X ≠ C ∧ A ≠ C)) := sorry

theorem hilbert_s_version_of_pasch_c :
    ∀ (A B C P Q : Tpoint), Coplanar A B C P → ¬ Col C Q P → ¬ Col A B P → BetS A Q B → ∃ (X : Tpoint), Col P Q X ∧ (BetS A X C ∨ BetS B X C) := sorry

theorem two_sides_cases_c :
    ∀ (O P A B : Tpoint), ¬ Col O A B → OS O P A B → TS O A P B ∨ TS O B P A := sorry

theorem not_par_two_sides_c :
    ∀ (A B C D I : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ∃ (X : Tpoint), ∃ (Y : Tpoint), Col C D X ∧ Col C D Y ∧ TS A B X Y := sorry

theorem cop_not_par_other_side_c :
    ∀ (A B C D I P : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ¬ Col A B P → Coplanar A B C P → ∃ (Q : Tpoint), Col C D Q ∧ TS A B P Q := sorry

theorem cop_not_par_same_side_c :
    ∀ (A B C D I P : Tpoint), C ≠ D → Col A B I → Col C D I → ¬ Col A B C → ¬ Col A B P → Coplanar A B C P → ∃ (Q : Tpoint), Col C D Q ∧ OS A B P Q := sorry
theorem all_coplanar_c :
    ∀ (A B C D : Tpoint), Coplanar A B C D := sorry

theorem per2__col_c :
    ∀ (A B C X : Tpoint), Per A X C → X ≠ C → Per B X C → Col A B X := sorry

theorem perp2__col_c :
    ∀ (X Y Z A B : Tpoint), Perp X Y A B → Perp X Z A B → Col X Y Z := sorry

#print axioms GeocoqTranslate.Tarski.Base.cop__cong_on_bissect_c
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_mid_perp__col_c
#print axioms GeocoqTranslate.Tarski.Base.cop_image_in2__col_c
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
#print axioms GeocoqTranslate.Tarski.Base.cong_cop_image__col_c
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
#print axioms GeocoqTranslate.Tarski.Base.per2__col_c
#print axioms GeocoqTranslate.Tarski.Base.perp2__col_c
end GeocoqTranslate.Tarski.Base