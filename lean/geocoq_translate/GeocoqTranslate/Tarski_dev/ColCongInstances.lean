/-
Wires the ported reflective automation (`ColR`/`CongR`, i.e. the `colr`/`cong_r`
tactics) to the REAL Tarski `Col`/`Cong` predicates, for the first time in the
`Ch02.lean..Ch10.lean` climb chain — see docs/session_progress.md Item 11
addendum and docs/ch09_ch10_closure_architecture.md §1/Stage 0 for the full
story: the chain never invoked this already-verified automation, transliterating
Coq's raw (ColR/Col5-expanded) proof terms literally instead, which is why it
needed an ever-growing tail of individual permutation/transitivity lemmas.

`col3` (GeoCoq's `col_transitivity`) needs no assumption — unlike the earlier
`PilotCh06.lean` demo, which used an explicit `Col3Assumption` placeholder
because the Ch02-Ch05 cone wasn't ported yet at the time. It's derived here
unconditionally from lemmas already proven in this chain: `col_transitivity_1_c`
+ `l6_16_1_c` (Ch06.lean) + `col_permutation_2_c`/`col_permutation_3_c`
(Ch04.lean). `CongTheory`'s four fields are likewise sourced directly from
Ch02.lean's already-proven `cong_reflexivity_c`/`cong_left_commutativity_c`/
`cong_symmetry_c`/`cong_transitivity_c` — no re-derivation needed.

Validated: `ScratchColRTest.lean` (kept as regression evidence) shows `colr`
closing both pure-permutation and transitivity-shaped `Col` goals in one
tactic call once this instance is in scope.
-/
import GeocoqTranslate.Tarski_dev.Ch06
import GeocoqTranslate.Tarski_dev.ColR
import GeocoqTranslate.Tarski_dev.CongR

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-- `col3` : the one non-permutation fact `ColTheory` needs, proven outright
from `col_transitivity_1_c` (pivot `X`) + `l6_16_1_c` (transport the pivot to
`A` when `A ≠ X`) + `col_transitivity_1_c` again (pivot `A`). -/
theorem col3_real (X Y A B C : Tpoint) (hXY : X ≠ Y)
    (hA : Col X Y A) (hB : Col X Y B) (hC : Col X Y C) : Col A B C := by
  rcases point_equality_decidability A X with e | hAX
  · rw [e]
    exact col_transitivity_1_c X Y B C hXY hB hC
  · have hAXY : Col A X Y := col_permutation_2_c X Y A hA
    have hBXY : Col B X Y := col_permutation_2_c X Y B hB
    have hCXY : Col C X Y := col_permutation_2_c X Y C hC
    have hBXA : Col B X A := l6_16_1_c X Y A B hXY hAXY hBXY
    have hCXA : Col C X A := l6_16_1_c X Y A C hXY hAXY hCXY
    have hAXB : Col A X B := col_permutation_3_c B X A hBXA
    have hAXC : Col A X C := col_permutation_3_c C X A hCXA
    exact col_transitivity_1_c A X B C hAX hAXB hAXC

instance realColThy : ColR.ColTheory Tpoint Col where
  trivial := col_trivial_1_c
  perm1 := fun _ _ _ h => col_permutation_1_c _ _ _ h
  perm2 := fun _ _ _ h => col_permutation_5_c _ _ _ h
  col3 := col3_real

instance realCongThy : CongR.CongTheory Tpoint Cong where
  refl := cong_reflexivity_c
  left_comm := fun _ _ _ _ h => cong_left_commutativity_c _ _ _ _ h
  sym := fun _ _ _ _ h => cong_symmetry_c _ _ _ _ h
  trans := fun _ _ _ _ _ _ h1 h2 => cong_transitivity_c _ _ _ _ _ _ h1 h2

end GeocoqTranslate.Tarski.Base
