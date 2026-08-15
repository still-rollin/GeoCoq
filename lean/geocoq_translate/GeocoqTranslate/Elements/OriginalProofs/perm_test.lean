/- Unit tests for the permutation-aware tactics (perm_close / perm_apply).
   This is the unit-test deliverable Julien asked for. -/
import GeocoqTranslate.Elements.OriginalProofs.perm_tactics

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

set_option maxHeartbeats 800000

/-! ### perm_close — EXHAUSTIVE: every valid permutation of every predicate.
    These hit every branch of every `*_cases` lemma (completeness guard). -/

-- Col: all 6 (S₃) — every branch of Col_cases
example (A B C : Point) (h : Col A B C) : Col A B C := by perm_close
example (A B C : Point) (h : Col A B C) : Col A C B := by perm_close
example (A B C : Point) (h : Col A B C) : Col B A C := by perm_close
example (A B C : Point) (h : Col A B C) : Col B C A := by perm_close
example (A B C : Point) (h : Col A B C) : Col C A B := by perm_close
example (A B C : Point) (h : Col A B C) : Col C B A := by perm_close

-- nCol: all 6 — every branch of nCol_cases
example (A B C : Point) (h : nCol A B C) : nCol A B C := by perm_close
example (A B C : Point) (h : nCol A B C) : nCol A C B := by perm_close
example (A B C : Point) (h : nCol A B C) : nCol B A C := by perm_close
example (A B C : Point) (h : nCol A B C) : nCol B C A := by perm_close
example (A B C : Point) (h : nCol A B C) : nCol C A B := by perm_close
example (A B C : Point) (h : nCol A B C) : nCol C B A := by perm_close

-- BetS: both 2 — every branch of BetS_cases
example (A B C : Point) (h : BetS A B C) : BetS A B C := by perm_close
example (A B C : Point) (h : BetS A B C) : BetS C B A := by perm_close

-- Cong: all 8 — every branch of Cong_cases
example (A B C D : Point) (h : Cong A B C D) : Cong A B C D := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong A B D C := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong B A C D := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong B A D C := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong C D A B := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong C D B A := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong D C A B := by perm_close
example (A B C D : Point) (h : Cong A B C D) : Cong D C B A := by perm_close

-- Par: all 8 — every branch of Par_cases (Par symmetry is a derived lemma,
-- so the Par-aware `perm_close_par` from perm_tactics is used)
example (A B C D : Point) (h : Par A B C D) : Par A B C D := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par B A C D := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par A B D C := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par B A D C := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par C D A B := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par C D B A := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par D C A B := by perm_close_par
example (A B C D : Point) (h : Par A B C D) : Par D C B A := by perm_close_par

-- neq: both orientations
example (A B : Point) (h : A ≠ B) : A ≠ B := by perm_close
example (A B : Point) (h : A ≠ B) : B ≠ A := by perm_close

/-! ### perm_apply — apply a lemma modulo permutation of the goal -/
-- bare fact in the non-canonical orientation
example (A B C : Point) (h : Col A B C) : Col B A C := by perm_apply h
example (A B C : Point) (h : Col A B C) : Col C B A := by perm_apply h
example (A B C : Point) (h : nCol A B C) : nCol B C A := by perm_apply h
example (A B C : Point) (h : BetS A B C) : BetS C B A := by perm_apply h
example (A B C D : Point) (h : Cong A B C D) : Cong D C B A := by perm_apply h
example (A B C D : Point) (h : Par A B C D) : Par C D A B := by perm_apply h

-- lemma WITH a premise, discharged from context (the real perm_apply idiom)
example (A B C : Point) (key : ∀ X Y Z : Point, Col X Y Z → Col X Y Z)
    (h : Col A B C) : Col B A C := by perm_apply (key A B C)

/- We deliberately do NOT keep `fail_if_success`-style negative tests here
   (checking e.g. that `perm_close` fails to prove `BetS B A C` from
   `BetS A B C`). That pattern is borrowed from ordinary software testing,
   where a black-box check on behavior is often the only guard against a
   silent bug. It doesn't add the same protection here: if `perm_close` or
   `perm_apply` were ever unsound and used at a real proof site, the
   resulting proof simply would not kernel-check — `lake build` plus
   `#print axioms` (no `sorryAx`) is the actual soundness guarantee, not a
   test file. -/

end GeocoqTranslate.Elements
