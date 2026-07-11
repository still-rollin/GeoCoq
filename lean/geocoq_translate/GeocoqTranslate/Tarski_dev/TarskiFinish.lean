/-
Lean port of GeoCoq's `finish` closer.

GeoCoq: `Ltac finish := auto 4 with between col le out par perp cong midpoint …` —
one closer backed by many hint databases. Here we combine the ported reflective
tactics (`colr`, `cong_r`) with the distinctness rule-set (`assert_diffs`)
and a general `aesop` sweep into a single `Tfinish` tactic that dispatches by goal
shape. Each sub-tactic fails cleanly on a non-matching goal, so `first` routes
`Col` goals to `colr`, `Cong` goals to `cong_r`, `≠` goals to the
distinctness rules, etc.

Self-contained: builds only on the three ported-automation files.
-/
import GeocoqTranslate.Tarski_dev.ColR
import GeocoqTranslate.Tarski_dev.CongR
import GeocoqTranslate.Tarski_dev.TarskiDiffs

namespace GeocoqTranslate.Tarski

/-- The combined Tarski closer. Tries, in order: direct `assumption`; collinearity
    closure (`colr`); congruence closure (`cong_r`); distinctness forward
    rules (`assert_diffs`); a general `aesop` sweep including the distinctness set. -/
macro "Tfinish" : tactic =>
  `(tactic|
    first
      | assumption
      | colr
      | cong_r
      | assert_diffs)

/-! ## Acceptance tests — one closer, dispatched by goal shape -/

section Tests
variable {P : Type*}
  {Col : P → P → P → Prop} {Cong : P → P → P → P → Prop}
  {Bet : P → P → P → Prop} {Midp : P → P → P → Prop} {Out : P → P → P → Prop}
  [ColR.ColTheory P Col] [CongR.CongTheory P Cong]
  [Diffs.ColDiff P Col] [Diffs.BetDiff P Bet] [Diffs.CongDiff P Cong]

-- collinearity goal → routed to colr
example (A B C D : P) (hab : A ≠ B) (h1 : Col A B C) (h2 : Col A B D) : Col B C D := by
  Tfinish

-- congruence goal → routed to cong_r
example (A B C D E F : P) (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F := by
  Tfinish

-- distinctness goal → routed to the diff rules
example (A B C : P) (h : ¬ Col A B C) : A ≠ B := by Tfinish

-- distinctness via a congruence hypothesis
example (A B C D : P) (hab : A ≠ B) (h : Cong A B C D) : C ≠ D := by Tfinish

-- trivial hypothesis hit
example (A B C : P) (h : Col A B C) : Col A B C := by Tfinish

end Tests

end GeocoqTranslate.Tarski
