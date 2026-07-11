/-
Translated from theories/Axioms/Definitions.v (subset used by Ch02_cong).

Definitions building on `Tarski_neutral_dimensionless`. More definitions
from the same Rocq file will be added here as later chapters need them.
-/

import GeocoqTranslate.Tarski.Axioms

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

/-- Definition 2.10: Outer Five Segment Configuration. -/
def OFSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Bet A B C ∧ Bet A' B' C' ∧
  Cong A B A' B' ∧ Cong B C B' C' ∧
  Cong A D A' D' ∧ Cong B D B' D'

/-- Inner Five Segment Configuration (Definitions.v line 21). -/
def IFSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Bet A B C ∧ Bet A' B' C' ∧
  Cong A C A' C' ∧ Cong B C B' C' ∧
  Cong A D A' D' ∧ Cong C D C' D'

/-- Definition 4.4: triangle congruence. -/
@[simp]
def Cong_3 (A B C A' B' C' : Tpoint) : Prop :=
  Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'

def Cong_4 (P1 P2 P3 P4 Q1 Q2 Q3 Q4 : Tpoint) : Prop :=
  Cong P1 P2 Q1 Q2 ∧ Cong P1 P3 Q1 Q3 ∧ Cong P1 P4 Q1 Q4 ∧
  Cong P2 P3 Q2 Q3 ∧ Cong P2 P4 Q2 Q4 ∧ Cong P3 P4 Q3 Q4

def Cong_5 (P1 P2 P3 P4 P5 Q1 Q2 Q3 Q4 Q5 : Tpoint) : Prop :=
  Cong P1 P2 Q1 Q2 ∧ Cong P1 P3 Q1 Q3 ∧
  Cong P1 P4 Q1 Q4 ∧ Cong P1 P5 Q1 Q5 ∧
  Cong P2 P3 Q2 Q3 ∧ Cong P2 P4 Q2 Q4 ∧ Cong P2 P5 Q2 Q5 ∧
  Cong P3 P4 Q3 Q4 ∧ Cong P3 P5 Q3 Q5 ∧ Cong P4 P5 Q4 Q5

/-- Definition 4.10: collinearity. -/
@[simp]
def Col (A B C : Tpoint) : Prop :=
  Bet A B C ∨ Bet B C A ∨ Bet C A B

/-- Five-Segment Configuration with collinearity (Definitions.v line 47). -/
def FSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Col A B C ∧ Cong_3 A B C A' B' C' ∧ Cong A D A' D' ∧ Cong B D B' D'

/-- Four-point betweenness (used in Ch03 lemma `l3_9_4`). -/
def Bet_4 (A₁ A₂ A₃ A₄ : Tpoint) : Prop :=
  Bet A₁ A₂ A₃ ∧ Bet A₂ A₃ A₄ ∧ Bet A₁ A₂ A₄ ∧ Bet A₁ A₃ A₄

/-- Strict betweenness: `Bet` plus three distinctness conditions. -/
def BetS (A B C : Tpoint) : Prop :=
  Bet A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C

/-- Definition 5.4: segment `AB ≤ CD` iff `AB` is congruent to a subsegment of `CD`. -/
def Le (A B C D : Tpoint) : Prop :=
  ∃ E, Bet C E D ∧ Cong A B C E

/-- `AB ≥ CD` iff `CD ≤ AB`. -/
def Ge (A B C D : Tpoint) : Prop := Le C D A B

/-- Strict comparison: `AB < CD` iff `AB ≤ CD` and `AB` not congruent to `CD`. -/
def Lt (A B C D : Tpoint) : Prop := Le A B C D ∧ ¬ Cong A B C D

/-- `AB > CD` iff `CD < AB`. -/
def Gt (A B C D : Tpoint) : Prop := Lt C D A B

/-- Definition 6.1: `Out P A B` — `A` and `B` lie on the same ray from `P`. -/
def Out (P A B : Tpoint) : Prop :=
  A ≠ P ∧ B ≠ P ∧ (Bet P A B ∨ Bet P B A)

/-- Definition 7.1: `Midpoint M A B` — `M` is between `A`, `B` with equal distances. -/
def Midpoint (M A B : Tpoint) : Prop := Bet A M B ∧ Cong A M M B

/-- Definition 8.1: `Per A B C` — angle at `B` is right (reflection of `C` over `B`
    is congruent to `A`). -/
def Per (A B C : Tpoint) : Prop := ∃ C', Midpoint B C C' ∧ Cong A C A C'

/-- Definition 8.11 (`X`-anchored form): line `AB` is perpendicular to line `CD` at `X`. -/
def Perp_at (X A B C D : Tpoint) : Prop :=
  A ≠ B ∧ C ≠ D ∧ Col X A B ∧ Col X C D ∧
  ∀ U V, Col U A B → Col V C D → Per U X V

/-- Definition 8.11: line `AB` is perpendicular to line `CD` (at some point). -/
def Perp (A B C D : Tpoint) : Prop := ∃ X, Perp_at X A B C D

/-- Definition 9.1: `TS A B P Q` — `P` and `Q` are on opposite sides of line `AB`. -/
def TS (A B P Q : Tpoint) : Prop :=
  ¬ Col P A B ∧ ¬ Col Q A B ∧ ∃ T, Col T A B ∧ Bet P T Q

/-- `OS A B P Q` — `P` and `Q` are on the same side of line `AB`. -/
def OS (A B P Q : Tpoint) : Prop := ∃ R, TS A B P R ∧ TS A B Q R

/-- Coplanarity of four points. -/
def Coplanar (A B C D : Tpoint) : Prop :=
  ∃ X, (Col A B X ∧ Col C D X) ∨
       (Col A C X ∧ Col B D X) ∨
       (Col A D X ∧ Col B C X)

/-- Definition 9.37: `P` and `Q` on opposite sides of plane `ABC`. -/
def TSP (A B C P Q : Tpoint) : Prop :=
  ¬ Coplanar A B C P ∧ ¬ Coplanar A B C Q ∧
  ∃ T, Coplanar A B C T ∧ Bet P T Q

/-- Definition 9.40: `P` and `Q` on the same side of plane `ABC`. -/
def OSP (A B C P Q : Tpoint) : Prop :=
  ∃ R, TSP A B C P R ∧ TSP A B C Q R

/-- Definition 10.3: `ReflectL P' P A B` — `P'` is the image of `P` under the
    reflection across line `AB`, in the form used for `A ≠ B`. -/
def ReflectL (P' P A B : Tpoint) : Prop :=
  (∃ X, Midpoint X P P' ∧ Col A B X) ∧ (Perp A B P P' ∨ P = P')

/-- Definition 10.3: `Reflect P' P A B` — `P'` is the reflection of `P` across
    line `AB` (handles the degenerate `A = B` case as a point reflection). -/
def Reflect (P' P A B : Tpoint) : Prop :=
  (A ≠ B ∧ ReflectL P' P A B) ∨ (A = B ∧ Midpoint A P P')

/-- Definition 10.3: `ReflectL_at M P' P A B` — anchored variant of `ReflectL`. -/
def ReflectL_at (M P' P A B : Tpoint) : Prop :=
  (Midpoint M P P' ∧ Col A B M) ∧ (Perp A B P P' ∨ P = P')

/-- Definition 10.3: `Reflect_at M P' P A B` — anchored variant of `Reflect`. -/
def Reflect_at (M P' P A B : Tpoint) : Prop :=
  (A ≠ B ∧ ReflectL_at M P' P A B) ∨ (A = B ∧ A = M ∧ Midpoint M P P')

/-- Saccheri quadrilateral `ABCD`: right angles at `A` and `D`, equal legs `AB = CD`,
    and `B`, `C` on the same side of `AD`. -/
def Saccheri (A B C D : Tpoint) : Prop :=
  Per B A D ∧ Per A D C ∧ Cong A B C D ∧ OS A D B C

/-! ## Ch11-Ch16 definitions (Definitions.v lines 68-601)

Ported in one pass so Ch11-Ch16 lemma *statements* can be stated (proofs still
pending). Kept in the same dependency order as the Rocq source. -/

/-- Definition 6.22: `X` is the intersection of lines `A1A2` and `B1B2`. -/
def Inter (A1 A2 B1 B2 X : Tpoint) : Prop :=
  B1 ≠ B2 ∧ (∃ P, Col P B1 B2 ∧ ¬ Col P A1 A2) ∧
  Col A1 A2 X ∧ Col B1 B2 X

/-- Definition 11.2: angle congruence. -/
def CongA (A B C D E F : Tpoint) : Prop :=
  A ≠ B ∧ C ≠ B ∧ D ≠ E ∧ F ≠ E ∧
  ∃ A' C' D' F',
  Bet B A A' ∧ Cong A A' E D ∧
  Bet B C C' ∧ Cong C C' E F ∧
  Bet E D D' ∧ Cong D D' B A ∧
  Bet E F F' ∧ Cong F F' B C ∧
  Cong A' C' D' F'

/-- Definition 11.23: `P` is inside angle `ABC`. -/
def InAngle (P A B C : Tpoint) : Prop :=
  A ≠ B ∧ C ≠ B ∧ P ≠ B ∧ ∃ X, Bet A X C ∧ (X = B ∨ Out B X P)

/-- Definition 11.27: angle `ABC ≤` angle `DEF`. -/
def LeA (A B C D E F : Tpoint) : Prop := ∃ P, InAngle P D E F ∧ CongA A B C D E P

def GeA (A B C D E F : Tpoint) : Prop := LeA D E F A B C

/-- Definition 11.38: strict angle comparison. -/
def LtA (A B C D E F : Tpoint) : Prop := LeA A B C D E F ∧ ¬ CongA A B C D E F

def GtA (A B C D E F : Tpoint) : Prop := LtA D E F A B C

/-- Definition 11.39: angle `ABC` is acute. -/
def Acute (A B C : Tpoint) : Prop :=
  ∃ A' B' C', Per A' B' C' ∧ LtA A B C A' B' C'

/-- Definition 11.39: angle `ABC` is obtuse. -/
def Obtuse (A B C : Tpoint) : Prop :=
  ∃ A' B' C', Per A' B' C' ∧ LtA A' B' C' A B C

/-- Definition 11.59: `X` is the foot of plane `ABC`'s orthogonal to line `UV`. -/
def Orth_at (X A B C U V : Tpoint) : Prop :=
  ¬ Col A B C ∧ U ≠ V ∧ Coplanar A B C X ∧ Col U V X ∧
  ∀ P Q, Coplanar A B C P → Col U V Q → Per P X Q

def Orth (A B C U V : Tpoint) : Prop := ∃ X, Orth_at X A B C U V

/-- Definition 12.2: lines `AB` and `CD` are strictly parallel. -/
def Par_strict (A B C D : Tpoint) : Prop :=
  Coplanar A B C D ∧ ¬ ∃ X, Col X A B ∧ Col X C D

/-- Definition 12.3: lines `AB` and `CD` are parallel (strict or identical). -/
def Par (A B C D : Tpoint) : Prop :=
  Par_strict A B C D ∨ (A ≠ B ∧ C ≠ D ∧ Col A C D ∧ Col B C D)

/-- Definition 13.4: `l` is a valid congruence class of segments. -/
def Q_Cong (l : Tpoint → Tpoint → Prop) : Prop :=
  ∃ A B, ∀ X Y, Cong A B X Y ↔ l X Y

def Len (A B : Tpoint) (l : Tpoint → Tpoint → Prop) : Prop := Q_Cong l ∧ l A B

def Q_Cong_Null (l : Tpoint → Tpoint → Prop) : Prop := Q_Cong l ∧ ∃ A, l A A

def EqL (l1 l2 : Tpoint → Tpoint → Prop) : Prop := ∀ A B, l1 A B ↔ l2 A B

def Q_CongA (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ A B C, A ≠ B ∧ C ≠ B ∧ ∀ X Y Z, CongA A B C X Y Z ↔ a X Y Z

def Ang (A B C : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop) : Prop := Q_CongA a ∧ a A B C

def Ang_Flat (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA a ∧ ∀ A B C, a A B C → Bet A B C

def EqA (a1 a2 : Tpoint → Tpoint → Tpoint → Prop) : Prop := ∀ A B C, a1 A B C ↔ a2 A B C

/-- Definition 13.9: `P` is on a line perpendicular to both `AB` and `CD`. -/
def Perp2 (A B C D P : Tpoint) : Prop :=
  ∃ X Y, Col P X Y ∧ Perp X Y A B ∧ Perp X Y C D

def Q_CongA_Acute (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ A B C, Acute A B C ∧ ∀ X Y Z, CongA A B C X Y Z ↔ a X Y Z

def Ang_Acute (A B C : Tpoint) (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA_Acute a ∧ a A B C

def Q_CongA_nNull (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA a ∧ ∀ A B C, a A B C → ¬ Out B A C

def Q_CongA_nFlat (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA a ∧ ∀ A B C, a A B C → ¬ Bet A B C

def Q_CongA_Null (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA a ∧ ∀ A B C, a A B C → Out B A C

def Q_CongA_Null_Acute (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA_Acute a ∧ ∀ A B C, a A B C → Out B A C

def is_null_anga' (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA_Acute a ∧ ∃ A B C, a A B C ∧ Out B A C

def Q_CongA_nNull_Acute (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_CongA_Acute a ∧ ∀ A B C, a A B C → ¬ Out B A C

def Lcos (lb lc : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  Q_Cong lb ∧ Q_Cong lc ∧ Q_CongA_Acute a ∧
  ∃ A B C, Per C B A ∧ lb A B ∧ lc A C ∧ a B A C

def Eq_Lcos (la : Tpoint → Tpoint → Prop) (a : Tpoint → Tpoint → Tpoint → Prop)
    (lb : Tpoint → Tpoint → Prop) (b : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ lp, Lcos lp la a ∧ Lcos lp lb b

def Lcos2 (lp l : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ la, Lcos la l a ∧ Lcos lp la b

def Eq_Lcos2 (l1 : Tpoint → Tpoint → Prop) (a b : Tpoint → Tpoint → Tpoint → Prop)
    (l2 : Tpoint → Tpoint → Prop) (c d : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ lp, Lcos2 lp l1 a b ∧ Lcos2 lp l2 c d

def Lcos3 (lp l : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ la lab, Lcos la l a ∧ Lcos lab la b ∧ Lcos lp lab c

def Eq_Lcos3 (l1 : Tpoint → Tpoint → Prop) (a b c : Tpoint → Tpoint → Tpoint → Prop)
    (l2 : Tpoint → Tpoint → Prop) (d e f : Tpoint → Tpoint → Tpoint → Prop) : Prop :=
  ∃ lp, Lcos3 lp l1 a b c ∧ Lcos3 lp l2 d e f

/-- Definition 14.1: `A`, `B`, `C` lie on line `OE`. -/
def Ar1 (O E A B C : Tpoint) : Prop :=
  O ≠ E ∧ Col O E A ∧ Col O E B ∧ Col O E C

/-- Definition 14.1: `A`, `B`, `C` lie on line `OE`, with basis `O E E'` non-degenerate. -/
def Ar2 (O E E' A B C : Tpoint) : Prop :=
  ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C

/-- Definition 14.2: `AB` is parallel to `CD`, or `C = D`. -/
def Pj (A B C D : Tpoint) : Prop := Par A B C D ∨ C = D

/-- Definition 14.3: `C = A + B` in the frame `O E E'`. -/
def Sum (O E E' A B C : Tpoint) : Prop :=
  Ar2 O E E' A B C ∧
  ∃ A' C', Pj E E' A A' ∧ Col O E' A' ∧
           Pj O E A' C' ∧
           Pj O E' B C' ∧
           Pj E' E C' C

def Proj (P Q A B X Y : Tpoint) : Prop :=
  A ≠ B ∧ X ≠ Y ∧ ¬ Par A B X Y ∧ Col A B Q ∧ (Par P Q X Y ∨ P = Q)

def Sump (O E E' A B C : Tpoint) : Prop :=
  Col O E A ∧ Col O E B ∧
  ∃ A' C' P', Proj A A' O E' E E' ∧
              Par O E A' P' ∧
              Proj B C' A' P' O E' ∧
              Proj C' C O E E E'

/-- Definition 14.4: `C = A * B` in the frame `O E E'`. -/
def Prod (O E E' A B C : Tpoint) : Prop :=
  Ar2 O E E' A B C ∧
  ∃ B', Pj E E' B B' ∧ Col O E' B' ∧ Pj E' A B' C

def Prodp (O E E' A B C : Tpoint) : Prop :=
  Col O E A ∧ Col O E B ∧
  ∃ B', Proj B B' O E' E E' ∧ Proj B' C O E A E'

/-- Definition 14.8: `B` is the opposite of `A` in the frame `O E E'`. -/
def Opp (O E E' A B : Tpoint) : Prop := Sum O E E' B A O

/-- Definition 14.38: `C = A - B` in the frame `O E E'`. -/
def Diff (O E E' A B C : Tpoint) : Prop :=
  ∃ B', Opp O E E' B B' ∧ Sum O E E' A B' C

def sum3 (O E E' A B C S : Tpoint) : Prop :=
  ∃ AB, Sum O E E' A B AB ∧ Sum O E E' AB C S

def Sum4 (O E E' A B C D S : Tpoint) : Prop :=
  ∃ ABC, sum3 O E E' A B C ABC ∧ Sum O E E' ABC D S

def sum22 (O E E' A B C D S : Tpoint) : Prop :=
  ∃ AB CD, Sum O E E' A B AB ∧ Sum O E E' C D CD ∧ Sum O E E' AB CD S

def Ar2_4 (O E E' A B C D : Tpoint) : Prop :=
  ¬ Col O E E' ∧ Col O E A ∧ Col O E B ∧ Col O E C ∧ Col O E D

/-- Definition 14.34: `A` is on the positive side of `O` towards `E`. -/
def Ps (O E A : Tpoint) : Prop := Out O A E

def Ng (O E A : Tpoint) : Prop := A ≠ O ∧ E ≠ O ∧ Bet A O E

/-- Definition 14.38: `A < B` in the frame `O E E'`. -/
def LtP (O E E' A B : Tpoint) : Prop := ∃ D, Diff O E E' B A D ∧ Ps O E D

def LeP (O E E' A B : Tpoint) : Prop := LtP O E E' A B ∨ A = B

def Length (O E E' A B L : Tpoint) : Prop :=
  O ≠ E ∧ Col O E L ∧ LeP O E E' O L ∧ Cong O L A B

/-- Definition 15.1: `Is_length` — allows the degenerate `O = E` frame. -/
def Is_length (O E E' A B L : Tpoint) : Prop :=
  Length O E E' A B L ∨ (O = E ∧ O = L)

def Sumg (O E E' A B C : Tpoint) : Prop :=
  Sum O E E' A B C ∨ (¬ Ar2 O E E' A B B ∧ C = O)

def Prodg (O E E' A B C : Tpoint) : Prop :=
  Prod O E E' A B C ∨ (¬ Ar2 O E E' A B B ∧ C = O)

def PythRel (O E E' A B C : Tpoint) : Prop :=
  Ar2 O E E' A B C ∧
  ((O = B ∧ (A = C ∨ Opp O E E' A C)) ∨
   ∃ B', Perp O B' O B ∧ Cong O B' O B ∧ Cong O C A B')

def SignEq (O E A B : Tpoint) : Prop :=
  Ps O E A ∧ Ps O E B ∨ Ng O E A ∧ Ng O E B

def LtPs (O E E' A B : Tpoint) : Prop := ∃ D, Ps O E D ∧ Sum O E E' A D B

/-- Definition 16.1: `S U1 U2` is a Cartesian frame of unit length `OE`. -/
def Cs (O E S U1 U2 : Tpoint) : Prop :=
  O ≠ E ∧ Cong O E S U1 ∧ Cong O E S U2 ∧ Per U1 S U2

/-- `Q` is the orthogonal projection of `P` on line `AB`. -/
def Projp (P Q A B : Tpoint) : Prop :=
  A ≠ B ∧ ((Col A B Q ∧ Perp A B P Q) ∨ (Col A B P ∧ P = Q))

/-- Definition 16.5: `P` has coordinates `(X, Y)` in grid `S U1 U2` using unit `OE`. -/
def Cd (O E S U1 U2 P X Y : Tpoint) : Prop :=
  Cs O E S U1 U2 ∧ Coplanar P S U1 U2 ∧
  (∃ PX, Projp P PX S U1 ∧ Cong_3 O E X S U1 PX) ∧
  (∃ PY, Projp P PY S U2 ∧ Cong_3 O E Y S U2 PY)

/-- Sum of segments: `AB + CD = EF`. -/
def SumS (A B C D E F : Tpoint) : Prop :=
  ∃ P Q R, Bet P Q R ∧ Cong P Q A B ∧ Cong Q R C D ∧ Cong P R E F

/-- `PQ` is the perpendicular bisector of segment `AB`. -/
def Perp_bisect (P Q A B : Tpoint) : Prop := ReflectL A B P Q ∧ A ≠ B

def Perp_bisect_bis (P Q A B : Tpoint) : Prop :=
  ∃ I, Perp_at I P Q A B ∧ Midpoint I A B

def Is_on_perp_bisect (P A B : Tpoint) : Prop := Cong A P P B

/-- Sum of angles: angle `ABC` + angle `DEF` = angle `GHI`. -/
def SumA (A B C D E F G H I : Tpoint) : Prop :=
  ∃ J, CongA C B J D E F ∧ ¬ OS B C A J ∧ Coplanar A B C J ∧ CongA A B J G H I

/-- The sum of angles `ABC` and `DEF` is "at most straight". -/
def SAMS (A B C D E F : Tpoint) : Prop :=
  A ≠ B ∧ (Out E D F ∨ ¬ Bet A B C) ∧
  ∃ J, CongA C B J D E F ∧ ¬ OS B C A J ∧ ¬ TS A B C J ∧ Coplanar A B C J

/-- Supplementary angles. -/
def SuppA (A B C D E F : Tpoint) : Prop :=
  A ≠ B ∧ ∃ A', Bet A B A' ∧ CongA D E F C B A'

/-- Sum of the interior angles of triangle `ABC` equals angle `DEF`. -/
def TriSumA (A B C D E F : Tpoint) : Prop :=
  ∃ G H I, SumA A B C B C A G H I ∧ SumA G H I C A B D E F

/-- Difference between a straight angle and the sum of the angles of triangle `ABC`. -/
def Defect (A B C D E F : Tpoint) : Prop :=
  ∃ G H I, TriSumA A B C G H I ∧ SuppA G H I D E F

/-- `P` is on the circle of center `A` through `B`. -/
def OnCircle (P A B : Tpoint) : Prop := Cong A P A B

/-- `P` is inside or on the circle of center `A` through `B`. -/
def InCircle (P A B : Tpoint) : Prop := Le A P A B

/-- `P` is outside or on the circle of center `A` through `B`. -/
def OutCircle (P A B : Tpoint) : Prop := Le A B A P

/-- `P` is strictly inside the circle of center `A` through `B`. -/
def InCircleS (P A B : Tpoint) : Prop := Lt A P A B

/-- `P` is strictly outside the circle of center `A` through `B`. -/
def OutCircleS (P A B : Tpoint) : Prop := Lt A B A P

/-- `AB` is a diameter of the circle of center `O` through `P`. -/
def Diam (A B O P : Tpoint) : Prop := Bet A O B ∧ OnCircle A O P ∧ OnCircle B O P

def EqC (A B C D : Tpoint) : Prop := ∀ X, OnCircle X A B ↔ OnCircle X C D

/-- The circles `(A,B)` and `(C,D)` intersect at the two distinct points `P`, `Q`. -/
def InterCCAt (A B C D P Q : Tpoint) : Prop :=
  ¬ EqC A B C D ∧
  P ≠ Q ∧ OnCircle P C D ∧ OnCircle Q C D ∧ OnCircle P A B ∧ OnCircle Q A B

/-- The circles `(A,B)` and `(C,D)` have two distinct intersections. -/
def InterCC (A B C D : Tpoint) : Prop := ∃ P Q, InterCCAt A B C D P Q

/-- The circles `(A,B)` and `(C,D)` are tangent. -/
def TangentCC (A B C D : Tpoint) : Prop :=
  ∃ X, (OnCircle X A B ∧ OnCircle X C D) ∧
    ∀ Y, (OnCircle Y A B ∧ OnCircle Y C D) → Y = X

/-- Line `AB` is tangent to the circle `(O,P)`. -/
def Tangent (A B O P : Tpoint) : Prop :=
  ∃ X, (Col A B X ∧ OnCircle X O P) ∧
    ∀ Y, (Col A B Y ∧ OnCircle Y O P) → Y = X

def TangentAt (A B O P T : Tpoint) : Prop :=
  Tangent A B O P ∧ Col A B T ∧ OnCircle T O P

/-- `A`, `B`, `C`, `D` belong to a common circle. -/
def Concyclic (A B C D : Tpoint) : Prop :=
  Coplanar A B C D ∧
  ∃ O P, OnCircle A O P ∧ OnCircle B O P ∧ OnCircle C O P ∧ OnCircle D O P

/-- `A`, `B`, `C`, `D` are concyclic or collinear. -/
def Concyclic_gen (A B C D : Tpoint) : Prop :=
  Concyclic A B C D ∨ (Col A B C ∧ Col A B D ∧ Col A C D ∧ Col B C D)

/-- `C` is on the graduation based on segment `AB`. -/
inductive Grad : Tpoint → Tpoint → Tpoint → Prop where
  | grad_init (A B : Tpoint) : Grad A B B
  | grad_stab (A B C C' : Tpoint) :
      Grad A B C → Bet A C C' → Cong A B C C' → Grad A B C'

def Reach (A B C D : Tpoint) : Prop := ∃ B', Grad A B B' ∧ Le C D A B'

/-- There exists `n` such that `AC = n·AB` and `DF = n·DE`. -/
inductive Grad2 : Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Prop where
  | grad2_init (A B D E : Tpoint) : Grad2 A B B D E E
  | grad2_stab (A B C C' D E F F' : Tpoint) :
      Grad2 A B C D E F →
      Bet A C C' → Cong A B C C' →
      Bet D F F' → Cong D E F F' →
      Grad2 A B C' D E F'

/-- Graduation based on the powers of 2. -/
inductive GradExp : Tpoint → Tpoint → Tpoint → Prop where
  | gradexp_init (A B : Tpoint) : GradExp A B B
  | gradexp_stab (A B C C' : Tpoint) :
      GradExp A B C → Bet A C C' → Cong A C C C' → GradExp A B C'

inductive GradExp2 : Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Prop where
  | gradexp2_init (A B D E : Tpoint) : GradExp2 A B B D E E
  | gradexp2_stab (A B C C' D E F F' : Tpoint) :
      GradExp2 A B C D E F →
      Bet A C C' → Cong A C C C' →
      Bet D F F' → Cong D F F F' →
      GradExp2 A B C' D E F'

/-- There exists `n` such that angle `DEF ≅ n·(angle ABC)`. -/
inductive GradA : Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Prop where
  | grada_init (A B C D E F : Tpoint) : CongA A B C D E F → GradA A B C D E F
  | grada_stab (A B C D E F G H I : Tpoint) :
      GradA A B C D E F →
      SAMS D E F A B C → SumA D E F A B C G H I →
      GradA A B C G H I

/-- There exists `n` such that angle `DEF ≅ 2ⁿ·(angle ABC)`. -/
inductive GradAExp : Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Tpoint → Prop where
  | gradaexp_init (A B C D E F : Tpoint) : CongA A B C D E F → GradAExp A B C D E F
  | gradaexp_stab (A B C D E F G H I : Tpoint) :
      GradAExp A B C D E F →
      SAMS D E F D E F → SumA D E F D E F G H I →
      GradAExp A B C G H I

/-- Parallelogram (strict case: `B`, `C` on opposite sides of `AA'`). -/
def Parallelogram_strict (A B A' B' : Tpoint) : Prop :=
  TS A A' B B' ∧ Par A B A' B' ∧ Cong A B A' B'

/-- Parallelogram (degenerate/flat case). -/
def Parallelogram_flat (A B A' B' : Tpoint) : Prop :=
  Col A B A' ∧ Col A B B' ∧
  Cong A B A' B' ∧ Cong A B' A' B ∧
  (A ≠ A' ∨ B ≠ B')

def Parallelogram (A B A' B' : Tpoint) : Prop :=
  Parallelogram_strict A B A' B' ∨ Parallelogram_flat A B A' B'

def Plg (A B C D : Tpoint) : Prop :=
  (A ≠ C ∨ B ≠ D) ∧ ∃ M, Midpoint M A C ∧ Midpoint M B D

/-- Rhombus. -/
def Rhombus (A B C D : Tpoint) : Prop := Plg A B C D ∧ Cong A B B C

/-- Rectangle. -/
def Rectangle (A B C D : Tpoint) : Prop := Plg A B C D ∧ Cong A C B D

/-- Square. -/
def Square (A B C D : Tpoint) : Prop := Rectangle A B C D ∧ Cong A B B C

/-- Kite. -/
def Kite (A B C D : Tpoint) : Prop := Cong B C C D ∧ Cong D A A B

/-- Lambert quadrilateral. -/
def Lambert (A B C D : Tpoint) : Prop :=
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ A ≠ D ∧
  Per B A D ∧ Per A D C ∧ Per A B C ∧ Coplanar A B C D

/-- Vector equality. -/
def EqV (A B C D : Tpoint) : Prop := Parallelogram A B D C ∨ (A = B ∧ C = D)

def SumV (A B C D E F : Tpoint) : Prop := ∀ D', EqV C D B D' → EqV A D' E F

def SumV_exists (A B C D E F : Tpoint) : Prop := ∃ D', EqV B D' C D ∧ EqV A D' E F

def Same_dir (A B C D : Tpoint) : Prop :=
  (A = B ∧ C = D) ∨ ∃ D', Out C D D' ∧ EqV A B C D'

def Opp_dir (A B C D : Tpoint) : Prop := Same_dir A B D C

/-- `ABC` and `A'B'C'` have the same triple of angle congruences. -/
def CongA_3 (A B C A' B' C' : Tpoint) : Prop :=
  CongA A B C A' B' C' ∧ CongA B C A B' C' A' ∧ CongA C A B C' A' B'

end GeocoqTranslate.Tarski
