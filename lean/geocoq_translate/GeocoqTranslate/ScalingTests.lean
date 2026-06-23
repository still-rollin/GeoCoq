/-
PHASE-2 SCALING TESTS (Julien's explicit ask): does the *deployed* bounded
`conclude` / `forward_using` (euclidean_tactics.lean) scale as the number of
facts/assumptions grows?  These call the REAL tactics, not raw solve_by_elim.

The hard case Julien named ("not always the first assumption which matches"):
each `pivotN` is seeded with N DECOY facts `Col Gᵢ B C` — every decoy matches
collinear4's FIRST premise `Col ?A B C` but FAILS the second `Col ?A B D`, so
the tactic must backtrack past all N decoys to the one correct pivot A.

`#count_heartbeats in` prints the cost; read the growth rate across N.
-/
import Mathlib.Tactic
import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinear4
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_collinearorder

namespace GeocoqTranslate.Elements
open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass
variable {Point : Type} [euclidean_neutral_ruler_compass Point]

-- ============================================================================
-- TEST A: backward pivot (`conclude lemma_collinear4`) with N deep-trap decoys
-- ============================================================================

#count_heartbeats in
theorem pivot4 (A B C D : Point)
    (G1 G2 G3 G4 : Point)
    (d1 : Col G1 B C)  (d2 : Col G2 B C)  (d3 : Col G3 B C)  (d4 : Col G4 B C)
    (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D := by
  conclude lemma_collinear4

#count_heartbeats in
theorem pivot12 (A B C D : Point)
    (G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 : Point)
    (d1 : Col G1 B C)  (d2 : Col G2 B C)  (d3 : Col G3 B C)  (d4 : Col G4 B C)  (d5 : Col G5 B C)  (d6 : Col G6 B C)  (d7 : Col G7 B C)  (d8 : Col G8 B C)  (d9 : Col G9 B C)  (d10 : Col G10 B C)  (d11 : Col G11 B C)  (d12 : Col G12 B C)
    (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D := by
  conclude lemma_collinear4

#count_heartbeats in
theorem pivot24 (A B C D : Point)
    (G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 : Point)
    (d1 : Col G1 B C)  (d2 : Col G2 B C)  (d3 : Col G3 B C)  (d4 : Col G4 B C)  (d5 : Col G5 B C)  (d6 : Col G6 B C)  (d7 : Col G7 B C)  (d8 : Col G8 B C)  (d9 : Col G9 B C)  (d10 : Col G10 B C)  (d11 : Col G11 B C)  (d12 : Col G12 B C)  (d13 : Col G13 B C)  (d14 : Col G14 B C)  (d15 : Col G15 B C)  (d16 : Col G16 B C)  (d17 : Col G17 B C)  (d18 : Col G18 B C)  (d19 : Col G19 B C)  (d20 : Col G20 B C)  (d21 : Col G21 B C)  (d22 : Col G22 B C)  (d23 : Col G23 B C)  (d24 : Col G24 B C)
    (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D := by
  conclude lemma_collinear4

#count_heartbeats in
theorem pivot48 (A B C D : Point)
    (G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G28 G29 G30 G31 G32 G33 G34 G35 G36 G37 G38 G39 G40 G41 G42 G43 G44 G45 G46 G47 G48 : Point)
    (d1 : Col G1 B C)  (d2 : Col G2 B C)  (d3 : Col G3 B C)  (d4 : Col G4 B C)  (d5 : Col G5 B C)  (d6 : Col G6 B C)  (d7 : Col G7 B C)  (d8 : Col G8 B C)  (d9 : Col G9 B C)  (d10 : Col G10 B C)  (d11 : Col G11 B C)  (d12 : Col G12 B C)  (d13 : Col G13 B C)  (d14 : Col G14 B C)  (d15 : Col G15 B C)  (d16 : Col G16 B C)  (d17 : Col G17 B C)  (d18 : Col G18 B C)  (d19 : Col G19 B C)  (d20 : Col G20 B C)  (d21 : Col G21 B C)  (d22 : Col G22 B C)  (d23 : Col G23 B C)  (d24 : Col G24 B C)  (d25 : Col G25 B C)  (d26 : Col G26 B C)  (d27 : Col G27 B C)  (d28 : Col G28 B C)  (d29 : Col G29 B C)  (d30 : Col G30 B C)  (d31 : Col G31 B C)  (d32 : Col G32 B C)  (d33 : Col G33 B C)  (d34 : Col G34 B C)  (d35 : Col G35 B C)  (d36 : Col G36 B C)  (d37 : Col G37 B C)  (d38 : Col G38 B C)  (d39 : Col G39 B C)  (d40 : Col G40 B C)  (d41 : Col G41 B C)  (d42 : Col G42 B C)  (d43 : Col G43 B C)  (d44 : Col G44 B C)  (d45 : Col G45 B C)  (d46 : Col G46 B C)  (d47 : Col G47 B C)  (d48 : Col G48 B C)
    (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D := by
  conclude lemma_collinear4

-- ============================================================================
-- TEST B: forward reorder (`forward_using lemma_collinearorder`) with N noise
-- facts.  Goal `Col C B A` must be PROJECTED out of collinearorder's conjunction
-- applied to `hABC`, while N unrelated `Col Gᵢ Hᵢ Kᵢ` facts clutter the context.
-- ============================================================================

#count_heartbeats in
theorem reorder4 (A B C : Point)
    (G1 H1 K1 G2 H2 K2 G3 H3 K3 G4 H4 K4 : Point)
    (d1 : Col G1 H1 K1)  (d2 : Col G2 H2 K2)  (d3 : Col G3 H3 K3)  (d4 : Col G4 H4 K4)
    (hABC : Col A B C) : Col C B A := by
  forward_using lemma_collinearorder

#count_heartbeats in
theorem reorder12 (A B C : Point)
    (G1 H1 K1 G2 H2 K2 G3 H3 K3 G4 H4 K4 G5 H5 K5 G6 H6 K6 G7 H7 K7 G8 H8 K8 G9 H9 K9 G10 H10 K10 G11 H11 K11 G12 H12 K12 : Point)
    (d1 : Col G1 H1 K1)  (d2 : Col G2 H2 K2)  (d3 : Col G3 H3 K3)  (d4 : Col G4 H4 K4)  (d5 : Col G5 H5 K5)  (d6 : Col G6 H6 K6)  (d7 : Col G7 H7 K7)  (d8 : Col G8 H8 K8)  (d9 : Col G9 H9 K9)  (d10 : Col G10 H10 K10)  (d11 : Col G11 H11 K11)  (d12 : Col G12 H12 K12)
    (hABC : Col A B C) : Col C B A := by
  forward_using lemma_collinearorder

#count_heartbeats in
theorem reorder24 (A B C : Point)
    (G1 H1 K1 G2 H2 K2 G3 H3 K3 G4 H4 K4 G5 H5 K5 G6 H6 K6 G7 H7 K7 G8 H8 K8 G9 H9 K9 G10 H10 K10 G11 H11 K11 G12 H12 K12 G13 H13 K13 G14 H14 K14 G15 H15 K15 G16 H16 K16 G17 H17 K17 G18 H18 K18 G19 H19 K19 G20 H20 K20 G21 H21 K21 G22 H22 K22 G23 H23 K23 G24 H24 K24 : Point)
    (d1 : Col G1 H1 K1)  (d2 : Col G2 H2 K2)  (d3 : Col G3 H3 K3)  (d4 : Col G4 H4 K4)  (d5 : Col G5 H5 K5)  (d6 : Col G6 H6 K6)  (d7 : Col G7 H7 K7)  (d8 : Col G8 H8 K8)  (d9 : Col G9 H9 K9)  (d10 : Col G10 H10 K10)  (d11 : Col G11 H11 K11)  (d12 : Col G12 H12 K12)  (d13 : Col G13 H13 K13)  (d14 : Col G14 H14 K14)  (d15 : Col G15 H15 K15)  (d16 : Col G16 H16 K16)  (d17 : Col G17 H17 K17)  (d18 : Col G18 H18 K18)  (d19 : Col G19 H19 K19)  (d20 : Col G20 H20 K20)  (d21 : Col G21 H21 K21)  (d22 : Col G22 H22 K22)  (d23 : Col G23 H23 K23)  (d24 : Col G24 H24 K24)
    (hABC : Col A B C) : Col C B A := by
  forward_using lemma_collinearorder

#count_heartbeats in
theorem reorder48 (A B C : Point)
    (G1 H1 K1 G2 H2 K2 G3 H3 K3 G4 H4 K4 G5 H5 K5 G6 H6 K6 G7 H7 K7 G8 H8 K8 G9 H9 K9 G10 H10 K10 G11 H11 K11 G12 H12 K12 G13 H13 K13 G14 H14 K14 G15 H15 K15 G16 H16 K16 G17 H17 K17 G18 H18 K18 G19 H19 K19 G20 H20 K20 G21 H21 K21 G22 H22 K22 G23 H23 K23 G24 H24 K24 G25 H25 K25 G26 H26 K26 G27 H27 K27 G28 H28 K28 G29 H29 K29 G30 H30 K30 G31 H31 K31 G32 H32 K32 G33 H33 K33 G34 H34 K34 G35 H35 K35 G36 H36 K36 G37 H37 K37 G38 H38 K38 G39 H39 K39 G40 H40 K40 G41 H41 K41 G42 H42 K42 G43 H43 K43 G44 H44 K44 G45 H45 K45 G46 H46 K46 G47 H47 K47 G48 H48 K48 : Point)
    (d1 : Col G1 H1 K1)  (d2 : Col G2 H2 K2)  (d3 : Col G3 H3 K3)  (d4 : Col G4 H4 K4)  (d5 : Col G5 H5 K5)  (d6 : Col G6 H6 K6)  (d7 : Col G7 H7 K7)  (d8 : Col G8 H8 K8)  (d9 : Col G9 H9 K9)  (d10 : Col G10 H10 K10)  (d11 : Col G11 H11 K11)  (d12 : Col G12 H12 K12)  (d13 : Col G13 H13 K13)  (d14 : Col G14 H14 K14)  (d15 : Col G15 H15 K15)  (d16 : Col G16 H16 K16)  (d17 : Col G17 H17 K17)  (d18 : Col G18 H18 K18)  (d19 : Col G19 H19 K19)  (d20 : Col G20 H20 K20)  (d21 : Col G21 H21 K21)  (d22 : Col G22 H22 K22)  (d23 : Col G23 H23 K23)  (d24 : Col G24 H24 K24)  (d25 : Col G25 H25 K25)  (d26 : Col G26 H26 K26)  (d27 : Col G27 H27 K27)  (d28 : Col G28 H28 K28)  (d29 : Col G29 H29 K29)  (d30 : Col G30 H30 K30)  (d31 : Col G31 H31 K31)  (d32 : Col G32 H32 K32)  (d33 : Col G33 H33 K33)  (d34 : Col G34 H34 K34)  (d35 : Col G35 H35 K35)  (d36 : Col G36 H36 K36)  (d37 : Col G37 H37 K37)  (d38 : Col G38 H38 K38)  (d39 : Col G39 H39 K39)  (d40 : Col G40 H40 K40)  (d41 : Col G41 H41 K41)  (d42 : Col G42 H42 K42)  (d43 : Col G43 H43 K43)  (d44 : Col G44 H44 K44)  (d45 : Col G45 H45 K45)  (d46 : Col G46 H46 K46)  (d47 : Col G47 H47 K47)  (d48 : Col G48 H48 K48)
    (hABC : Col A B C) : Col C B A := by
  forward_using lemma_collinearorder

end GeocoqTranslate.Elements
