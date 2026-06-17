/-
Translated from theories/Elements/OriginalProofs/euclidean_defs.v (subset
needed by Proposition 1). Additional defs added as later propositions
reach them.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis

variable {Point : Type} [euclidean_neutral_basis Point]

/-- Three points form an equilateral triangle: all three sides equal. -/
def equilateral (A B C : Point) : Prop :=
  Cong A B B C ∧ Cong B C C A

/-- `Lt A B C D` — segment AB is strictly shorter than CD. In the
    GeoCoq Elements style: there is an interior point X on CD with
    `Cong C X A B`. -/
def Lt (A B C D : Point) : Prop :=
  ∃ X, BetS C X D ∧ Cong C X A B

/-- `Out A B C` — ray from A through B contains C (in the Elements
    style: there is some point X such that B and C are on the same
    side of A on a common line through A). -/
def Out (A B C : Point) : Prop :=
  ∃ X, BetS X A C ∧ BetS X A B

/-- `TG A B C D E F` — triangle inequality witness: `EF` is strictly
    shorter than the concatenation of `AB` and `CD`. Witnessed by a
    point `X` with `BetS A B X`, `Cong B X C D`, and `Lt E F A X`. -/
def TG (A B C D E F : Point) : Prop :=
  ∃ X, BetS A B X ∧ Cong B X C D ∧ Lt E F A X

/-! ## Derived predicates needed across the Elements (dependency order). -/

/-- `Midpoint A B C` — B is the midpoint of segment AC. -/
def Midpoint (A B C : Point) : Prop := BetS A B C ∧ Cong A B B C

/-- `Per A B C` — the angle at B (in A B C) is a right angle. -/
def Per (A B C : Point) : Prop :=
  ∃ X, BetS A B X ∧ Cong A B X B ∧ Cong A C X C ∧ B ≠ C

/-- `Supp A B C D F` — angle DBF is the supplement of angle ABC. -/
def Supp (A B C D F : Point) : Prop := Out B C D ∧ BetS A B F

/-- `CongA A B C a b c` — angle ABC is congruent to angle abc. -/
def CongA (A B C a b c : Point) : Prop :=
  ∃ U V u v, Out B A U ∧ Out B C V ∧ Out b a u ∧ Out b c v ∧
    Cong B U b u ∧ Cong B V b v ∧ Cong U V u v ∧ nCol A B C

/-- `Perp_at P Q A B C` — lines PQ and AB are perpendicular at point C. -/
def Perp_at (P Q A B C : Point) : Prop :=
  ∃ X, Col P Q C ∧ Col A B C ∧ Col A B X ∧ Per X C P

/-- `Perp P Q A B` — lines PQ and AB are perpendicular. -/
def Perp (P Q A B : Point) : Prop := ∃ X, Perp_at P Q A B X

/-- `InAngle A B C P` — P lies in the interior of angle ABC. -/
def InAngle (A B C P : Point) : Prop :=
  ∃ X Y, Out B A X ∧ Out B C Y ∧ BetS X P Y

/-- `OS P Q A B` — P and Q lie on the same side of line AB. -/
def OS (P Q A B : Point) : Prop :=
  ∃ X U V, Col A B U ∧ Col A B V ∧ BetS P U X ∧ BetS Q V X ∧
    nCol A B P ∧ nCol A B Q

/-- `isosceles A B C` — triangle ABC has `Cong A B A C`. -/
def isosceles (A B C : Point) : Prop := Triangle A B C ∧ Cong A B A C

/-- `Cut A B C D E` — segments AB and CD cross at E. -/
def Cut (A B C D E : Point) : Prop :=
  BetS A E B ∧ BetS C E D ∧ nCol A B C ∧ nCol A B D

/-- `Meet A B C D` — lines AB and CD meet at some point. -/
def Meet (A B C D : Point) : Prop :=
  ∃ X, A ≠ B ∧ C ≠ D ∧ Col A B X ∧ Col C D X

/-- `CR A B C D` — segments AB and CD cross (diagonals meet). -/
def CR (A B C D : Point) : Prop := ∃ X, BetS A X B ∧ BetS C X D

/-- `LtA A B C D E F` — angle ABC is less than angle DEF. -/
def LtA (A B C D E F : Point) : Prop :=
  ∃ U X V, BetS U X V ∧ Out E D U ∧ Out E F V ∧ CongA A B C D E X

/-- `TT A B C D E F G H` — segment-sum triangle inequality witness. -/
def TT (A B C D E F G H : Point) : Prop :=
  ∃ X, BetS E F X ∧ Cong F X G H ∧ TG A B C D E X

/-- `RT A B C D E F` — angles ABC and DEF sum to two right angles. -/
def RT (A B C D E F : Point) : Prop :=
  ∃ X Y Z U V, Supp X Y U V Z ∧ CongA A B C X Y U ∧ CongA D E F V Y Z

/-- `TP A B C D` — AB and CD are "thin parallel" (same side, no meet). -/
def TP (A B C D : Point) : Prop :=
  A ≠ B ∧ C ≠ D ∧ ¬ Meet A B C D ∧ OS C D A B

/-- `Par A B C D` — lines AB and CD are parallel. -/
def Par (A B C D : Point) : Prop :=
  ∃ U V u v X, A ≠ B ∧ C ≠ D ∧ Col A B U ∧ Col A B V ∧ U ≠ V ∧
    Col C D u ∧ Col C D v ∧ u ≠ v ∧ ¬ Meet A B C D ∧ BetS U X v ∧ BetS u X V

/-- `SumA A B C D E F P Q R` — angle PQR is the sum of ABC and DEF. -/
def SumA (A B C D E F P Q R : Point) : Prop :=
  ∃ X, CongA A B C P Q X ∧ CongA D E F X Q R ∧ BetS P X R

/-- `PG A B C D` — ABCD is a parallelogram. -/
def PG (A B C D : Point) : Prop := Par A B C D ∧ Par A D B C

/-- `SQ A B C D` — ABCD is a square. -/
def SQ (A B C D : Point) : Prop :=
  Cong A B C D ∧ Cong A B B C ∧ Cong A B D A ∧
    Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A

/-- `RE A B C D` — ABCD is a rectangle. -/
def RE (A B C D : Point) : Prop :=
  Per D A B ∧ Per A B C ∧ Per B C D ∧ Per C D A ∧ CR A C B D

end GeocoqTranslate.Elements
