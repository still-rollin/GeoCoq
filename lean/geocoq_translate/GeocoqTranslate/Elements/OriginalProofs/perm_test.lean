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

/-! ### NEGATIVE tests — the tactics must NOT prove a non-permutation
    (soundness / over-proving guard). Each `fail_if_success` succeeds ONLY if
    the inner `perm_close`/`perm_apply` correctly FAILS. -/

-- BetS: ONLY the reverse (A B C ↔ C B A) is a valid symmetry.
-- None of the other 4 orderings are derivable from BetS A B C.
example (A B C : Point) (h : BetS A B C) : True := by
  fail_if_success (have : BetS B A C := by perm_close)
  fail_if_success (have : BetS A C B := by perm_close)
  fail_if_success (have : BetS B C A := by perm_close)
  fail_if_success (have : BetS C A B := by perm_close)
  trivial

example (A B C : Point) (h : BetS A B C) : True := by
  fail_if_success (have : BetS B A C := by perm_apply h)
  fail_if_success (have : BetS A C B := by perm_apply h)
  trivial

-- BetS on unrelated points must not close.
example (A B C D : Point) (h : BetS A B C) : True := by
  fail_if_success (have : BetS A B D := by perm_close)
  trivial

-- Col: a fresh point is not collinear just because A B C are.
example (A B C D : Point) (h : Col A B C) : True := by
  fail_if_success (have : Col A B D := by perm_close)
  trivial

-- neq: A ≠ B does not give A ≠ C.
example (A B C : Point) (h : A ≠ B) : True := by
  fail_if_success (have : A ≠ C := by perm_close)
  trivial

-- Cong: swapping only one endpoint across the pair is NOT a Cong symmetry.
example (A B C D : Point) (h : Cong A B C D) : True := by
  fail_if_success (have : Cong A C B D := by perm_close)
  trivial

end GeocoqTranslate.Elements
