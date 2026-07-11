-- Regression evidence for the `colr`/`cong_r` wiring finding — see
-- docs/session_progress.md Item 11 addendum and
-- docs/ch09_ch10_closure_architecture.md §1/Stage 0.
-- The real instance now lives in ColCongInstances.lean (imported transitively
-- via Ch10 -> ... -> Ch07 -> ColCongInstances); this file just exercises it.
import GeocoqTranslate.Tarski_dev.Ch10

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

-- pure-permutation goals, no col3 needed at all
theorem scratch_test1 (C D X : Tpoint) (H2 : Col C D X) : Col D C X := by colr
theorem scratch_test2 (A C X : Tpoint) (H2 : Col A C X) : Col A X C := by colr

-- a transitivity-shaped goal (needs col3)
theorem scratch_test3 (P Q A B : Tpoint) (hPQ : P ≠ Q) (h1 : Col P Q A) (h2 : Col P Q B) :
    Col P A B := by colr

#print axioms GeocoqTranslate.Tarski.Base.scratch_test1
#print axioms GeocoqTranslate.Tarski.Base.scratch_test2
#print axioms GeocoqTranslate.Tarski.Base.scratch_test3

-- negative result, documented: colr does NOT handle negated goals (¬ Col _ _ _),
-- so the `not_col_permutation_*` family is OUT OF SCOPE for the translit.py
-- COL_FAMILY substitution below.
-- theorem scratch_test4 (A B C : Tpoint) (H : ¬ Col A B C) : ¬ Col B C A := by colr
--   -- error: colr: goal is not of the form `Col _ _ _`

end GeocoqTranslate.Tarski.Base
