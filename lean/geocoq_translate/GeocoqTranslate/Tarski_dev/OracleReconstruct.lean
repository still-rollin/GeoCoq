/-
Layer-3 oracle-guided reconstruction — PROTOTYPE (see docs/tarski_architecture.md §5.1).

Julien's method: the GeoCoq proof is used as an ORACLE for the *structure* of the
Lean reconstruction — the intermediate statements and, crucially, the new-point
constructions — while the final proof is kernel-checked. `transpiler/oracle_skeleton.py`
extracts that structure from a lemma's Ltac proof.

This file demonstrates the loop end-to-end on Ch06 `out_col`, and records the honest
finding that richer Ch06 lemmas need a *base* of ported betweenness/`Out` lemmas —
a base the oracle itself pinpoints (its "justification base needed" list).
-/
import GeocoqTranslate.Tarski_dev.PilotCh06
import GeocoqTranslate.Tarski_dev.TarskiFinish

namespace GeocoqTranslate.Tarski.Reconstruct
open Tarski_neutral_dimensionless GeocoqTranslate.Tarski GeocoqTranslate.Tarski.Pilot

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-! ## `out_col` — closure automation alone fails; the oracle skeleton reconstructs it

`out_col : Out A B C → Col A B C`. Running the oracle extractor:

    $ python3 transpiler/oracle_skeleton.py …/Ch06_out_lines.v out_col
    ── out_col  (0 intermediate stmt(s), 0 new-point, 0 justifying lemma(s)) ──

i.e. GeoCoq's proof is `unfold Out; spliter; induction H1; Between` — no lemmas, no
new points: the skeleton is "unfold `Out`, split the ray disjunction, close each
branch by a betweenness fact". The reconstruction below mirrors that structure
exactly, using the reusable base brick `bet_sym`. -/

-- Direct `Tfinish` cannot close it: the hypothesis is an `Out`, not a `Col`/`Cong`/`≠`
-- fact the closure tactics read. (Guard stays green iff `Tfinish` indeed fails here.)
example (A B C : Tpoint) (_h : Out A B C) : True := by
  fail_if_success (have : Col A B C := by Tfinish)  -- `Out` hyp present, still can't close
  trivial

-- Oracle-structure-guided reconstruction (mirrors `unfold Out; case; Between`):
theorem out_col (A B C : Tpoint) (h : Out A B C) : Col A B C := by
  unfold Out at h
  simp only [Col]
  obtain ⟨_, _, hb | hb⟩ := h
  · exact Or.inl hb                      -- Bet A B C          ⇒ Col A B C
  · exact Or.inr (Or.inl (bet_sym hb))   -- Bet A C B ⇒ Bet B C A ⇒ Col A B C

/-! ## The honest boundary — what a richer reconstruction still needs

For the new-point lemma `l6_3_1` the oracle correctly flags the construction step:

    ── l6_3_1  (2 intermediate stmt(s), 2 new-point, 1 justifying lemma(s)) ──
       point-creation ops (KEEP, per heuristic): point_construction_different
       ◆ NEW-POINT  exists C, Bet A P C /\ P <> C   ⇢  ∃ C, Bet A P C ∧ P <> C

The reconstruction would `obtain` that `C` (from `segment_construction`, which we
have as an axiom) and then discharge `Bet B P C` — but that piece needs betweenness
transitivity (`l5_2`/`between_exchange`), not collinearity closure. So `out_col`
closes now; `l6_3_1` and most of Ch06 wait on a ported betweenness base.

Key point: the oracle's "justification base needed" output is a **dependency map** —
aggregated over a chapter it yields the porting order (base lemmas first). That map,
not more tactics, is the critical path from 3/53 to full coverage. -/

end GeocoqTranslate.Tarski.Reconstruct
