/-
End-to-end reconstruction PILOT (Layer 3) — see docs/tarski_architecture.md §5.1.

Demonstrates the whole Tarski pipeline on three REAL Ch06 lemmas
(`l6_16_1`, `col_transitivity_1`, `col_transitivity_2`):

  · the *statement* of each is produced verbatim by
    `transpiler/tarski_statements.py` (Layer 2 — deterministic translation), and
  · the *proof* is reconstructed by the ported `colr` automation (Layer 1),
    collapsing GeoCoq's multi-line case-split proofs (`induction … Between`,
    `l5_1`/`l5_2`/`l5_3`, …) to a single tactic word.

HONESTY. The collinearity interface `ColR.ColTheory` needs one deep fact,
`col3` (GeoCoq `col_transitivity`), whose Lean proof requires the Ch02–Ch05 cone
that is not yet ported. Per the current plan we ASSUME it — but only as an
*explicit typeclass hypothesis* `Col3Assumption`, so every reconstructed theorem
carries it in its signature (visible to the kernel). No `sorry`, no `axiom`, no
`admit`. Everything else is proven outright from the Tarski axioms:

  · the other three `ColTheory` fields — `trivial`, `perm1`, `perm2` — and
  · ALL FOUR `CongTheory` fields — `refl`, `left_comm`, `sym`, `trans`,

using only Ch02-level facts (`bet_trivial`, `bet_sym`) that are themselves proven
here from the raw axioms (`segment_construction`, `inner_pasch`, the `Cong`
axioms) — self-contained, no geometric cone. So the `Cong` side needs no
assumption at all; the `Col` side needs exactly `col3`.
-/
import GeocoqTranslate.Tarski_dev.ColR
import GeocoqTranslate.Tarski_dev.CongR
import GeocoqTranslate.Tarski.Definitions

namespace GeocoqTranslate.Tarski.Pilot
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-! ## Ch02-level facts, proven from the Tarski axioms (no geometric cone) -/

/-- `Bet A B B` — from `segment_construction` + `cong_identity`. (Public: a reusable
    Ch02 base brick, e.g. for the oracle-guided reconstruction in `OracleReconstruct`.) -/
theorem bet_trivial (A B : Tpoint) : Bet A B B := by
  obtain ⟨E, hbet, hcong⟩ := segment_construction A B B B
  have hE : E = B := (cong_identity B E B hcong).symm
  subst hE; exact hbet

/-- `Bet A B C → Bet C B A` — the classic `inner_pasch` derivation of betweenness
    symmetry (choose the Pasch point on the degenerate side, force it to `B`). -/
theorem bet_sym {A B C : Tpoint} (h : Bet A B C) : Bet C B A := by
  obtain ⟨X, hBXB, hCXA⟩ := inner_pasch A B C B C h (bet_trivial B C)
  have hX : X = B := (between_identity B X hBXB).symm
  subst hX; exact hCXA

/-! ## `CongTheory` — proven outright from the `Cong` axioms (no assumption) -/

private theorem cong_refl' (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B (cong_pseudo_reflexivity B A) (cong_pseudo_reflexivity B A)

private theorem cong_sym' {A B C D : Tpoint} (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_refl' A B)

private theorem cong_trans' {A B C D E F : Tpoint}
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_sym' h1) h2

private theorem cong_left_comm' {A B C D : Tpoint} (h : Cong A B C D) : Cong B A C D :=
  cong_trans' (cong_pseudo_reflexivity B A) h

instance congThy : CongR.CongTheory Tpoint Cong where
  refl := cong_refl'
  left_comm := fun _ _ _ _ h => cong_left_comm' h
  sym := fun _ _ _ _ h => cong_sym' h
  trans := fun _ _ _ _ _ _ h1 h2 => cong_trans' h1 h2

/-! ## `ColTheory` — three fields proven; `col3` assumed via a named typeclass -/

private theorem col_trivial' (A B : Tpoint) : Col A A B := by
  simp only [Col]; exact Or.inr (Or.inr (bet_trivial B A))

private theorem col_perm1' {A B C : Tpoint} (h : Col A B C) : Col B C A := by
  simp only [Col] at h ⊢; tauto

private theorem col_perm2' {A B C : Tpoint} (h : Col A B C) : Col A C B := by
  simp only [Col] at h ⊢
  rcases h with h | h | h
  · exact Or.inr (Or.inl (bet_sym h))
  · exact Or.inl (bet_sym h)
  · exact Or.inr (Or.inr (bet_sym h))

/-- The single assumed fact: GeoCoq's `col_transitivity` (`col3`). Its Lean proof
    needs the Ch02–Ch05 cone (`col_transitivity_1 → l6_16_1 → l5_x → …`) that is
    not yet ported. Stated as a typeclass so the `ColTheory` instance below can be
    synthesised and every reconstructed theorem carries `[Col3Assumption Tpoint]`
    explicitly — no `sorry`/`axiom`. -/
class Col3Assumption (Tpoint : Type) [Tarski_neutral_dimensionless Tpoint] : Prop where
  col3 : ∀ X Y A B C : Tpoint,
    X ≠ Y → Col X Y A → Col X Y B → Col X Y C → Col A B C

variable [Col3Assumption Tpoint]

instance colThy : ColR.ColTheory Tpoint Col where
  trivial := col_trivial'
  perm1 := fun _ _ _ h => col_perm1' h
  perm2 := fun _ _ _ h => col_perm2' h
  col3 := Col3Assumption.col3

/-! ## The pilot — real Ch06 statements (Layer 2), reconstructed by `colr`

Each statement below is exactly what `tarski_statements.py` emits for the named
Ch06 lemma (only the trailing `:= by sorry` is replaced by the real proof). Every
GeoCoq proof of these is a multi-line betweenness case-split; here each is a single
`colr`. -/

-- NOTE ON THE PROOFS BELOW. `colr` reads the `Col`/`≠` facts from the *local
-- context* and runs the collinearity closure — it is NOT a goal-syntax-only tactic.
-- The hypotheses are therefore named (not `_`) and genuinely consumed; they only
-- look "unused" to the syntactic linter because the tactic uses them semantically,
-- not by name. That the proofs actually *depend* on them is proven by the
-- falsifiability guards in the `Soundness` section below (drop any hypothesis and
-- `colr` fails, as it must, since the conclusion is false for arbitrary points).
set_option linter.unusedVariables false

/-- Ch06 `l6_16_1`. GeoCoq: `eq_dec` split + `induction H0; induction H1` +
    `l5_2`/`l5_1`/`l5_3`. Here: one `colr` (merges lines `{S,P,Q}`, `{X,P,Q}`
    on the distinct pair `(P,Q)` via `col3`). -/
theorem l6_16_1 :
    ∀ (P Q S X : Tpoint), P ≠ Q → Col S P Q → Col X P Q → Col X P S := by
  intro P Q S X hPQ hSPQ hXPQ; colr

/-- Ch06 `col_transitivity_1`. Merges `{P,Q,A}`, `{P,Q,B}` on `(P,Q)`. -/
theorem col_transitivity_1 :
    ∀ (P Q A B : Tpoint), P ≠ Q → Col P Q A → Col P Q B → Col P A B := by
  intro P Q A B hPQ hPQA hPQB; colr

/-- Ch06 `col_transitivity_2`. -/
theorem col_transitivity_2 :
    ∀ (P Q A B : Tpoint), P ≠ Q → Col P Q A → Col P Q B → Col Q A B := by
  intro P Q A B hPQ hPQA hPQB; colr

/-! ## `colr` does more than a single `col3` — iterated saturation

Answering the fair critique that the three lemmas above are each essentially one
application of the assumed `col3`. Here `colr` closes a goal that **no single
`col3` step can reach**: it must merge line `PQ` (from `P≠Q`), independently merge
line `AB` (from `A≠B`), then merge those two on the shared pair `(A,B)` — three
saturation steps — before `Col P R S` falls out. This is genuine closure work by
the ported procedure, independent of how strong the `col3` axiom is. -/

example (P Q A B R S : Tpoint) (hPQ : P ≠ Q) (hAB : A ≠ B)
    (h1 : Col P Q A) (h2 : Col P Q B) (h3 : Col A B R) (h4 : Col A B S) :
    Col P R S := by colr

/-! ## Congruence side — no assumption needed (`CongTheory` fully proven)

A concrete `Cong` goal over the real Tarski `Cong`, reconstructed by `cong_r`
through the outright-proven `congThy` instance. Contrast the `Col` theorems above:
the `Cong` closure needs no `Col3Assumption`. -/

example (A B C D E F : Tpoint) (h1 : Cong A B C D) (h2 : Cong C D E F) :
    Cong A B E F := by cong_r

example (A B C D : Tpoint) (h : Cong A B C D) : Cong D C B A := by cong_r

/-! ## Soundness / falsifiability guards (answering "is `colr` sound?")

`colr` (GeoCoq's `ColR`) is NOT a reflexivity tactic — it is a **reflective
decision procedure** that reads `Col`/`≠` facts from the *local context*
(including inaccessible `_` hypotheses, which are not implementation-detail decls)
and runs the collinearity closure, then discharges it with a kernel-checked
soundness lemma.

The concern that matters: `Col P A B` is FALSE for arbitrary points, so the tactic
must FAIL whenever the hypotheses that actually entail the goal are absent. Each
`fail_if_success` below is a regression guard that stays green *iff* `colr`
genuinely depends on the hypotheses — i.e. iff it is sound. If any guard's inner
`colr` ever wrongly succeeded, that `example` would stop compiling. -/

section Soundness
variable [Col3Assumption Tpoint]

-- (1) NO hypotheses → `Col P A B` is false → must FAIL.
example (P A B : Tpoint) : True := by
  fail_if_success (have : Col P A B := by colr)
  trivial

-- (2) both `Col` hyps present but distinctness `P ≠ Q` MISSING → the merge rule
--     (`col3`) cannot fire (matches GeoCoq: no distinctness ⇒ no transitivity) → FAIL.
example (P Q A B : Tpoint) (h1 : Col P Q A) (h2 : Col P Q B) : True := by
  fail_if_success (have : Col P A B := by colr)
  trivial

-- (3) distinctness present but only ONE `Col` hyp → not enough to merge → FAIL.
example (P Q A B : Tpoint) (hpq : P ≠ Q) (h1 : Col P Q A) : True := by
  fail_if_success (have : Col P A B := by colr)
  trivial

-- (4) UNSOUNDNESS probe: the real hyps hold, but the goal names a FRESH point `R`
--     not constrained by anything → `colr` must NOT hallucinate `Col A B R`.
example (P Q A B R : Tpoint) (hpq : P ≠ Q) (h1 : Col P Q A) (h2 : Col P Q B) :
    True := by
  fail_if_success (have : Col A B R := by colr)
  trivial

-- (5) all three genuine hyps present → SUCCEEDS (the real derivation, via `col3`).
example (P Q A B : Tpoint) (hpq : P ≠ Q) (h1 : Col P Q A) (h2 : Col P Q B) :
    Col P A B := by colr

end Soundness

end GeocoqTranslate.Tarski.Pilot
