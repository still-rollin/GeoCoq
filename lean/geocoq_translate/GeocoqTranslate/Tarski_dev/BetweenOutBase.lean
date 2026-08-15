/-
Betweenness + `Out` base lemmas — Tier 1 of the porting critical path.

These are the most-called base lemmas in the Ch06 oracle dependency map
(`transpiler/oracle_skeleton.py --all`): `between_symmetry` (10×),
`l6_6` (8×), `bet_out` (5×), `between_equality`/`between_inner_transitivity` (4×), …
All are proven OUTRIGHT from the Tarski axioms via `inner_pasch` / `between_identity`
/ `segment_construction` — no five-segment, no Ch04 segment machinery, and crucially
NO assumption (unlike `col3`/`Col3Assumption`). Names match GeoCoq so the
oracle-guided reconstruction can call them verbatim.

The deeper `l5_1` (Ch05 connectivity) and thus `l5_2`/`l5_3` — and `col3` — sit on
the full Ch02–Ch04 cone (`l2_11`, `FSC`/`IFSC`, `l4_x`, `construction_uniqueness`),
which is the next, larger tier.
-/
import GeocoqTranslate.Tarski.Definitions

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-! ## Betweenness (Ch03, from `inner_pasch` / `between_identity`) -/

/-- `Bet A B B` (GeoCoq `between_trivial`). -/
theorem between_trivial (A B : Tpoint) : Bet A B B := by
  obtain ⟨E, hbet, hcong⟩ := segment_construction A B B B
  have hE : E = B := (cong_identity B E B hcong).symm
  subst hE; exact hbet

/-- `Bet A B C → Bet C B A` (GeoCoq `between_symmetry`). The classic `inner_pasch`
    derivation: put the Pasch point on the degenerate side and force it to `B`. -/
theorem between_symmetry {A B C : Tpoint} (h : Bet A B C) : Bet C B A := by
  obtain ⟨X, hBXB, hCXA⟩ := inner_pasch A B C B C h (between_trivial B C)
  have hX : X = B := (between_identity B X hBXB).symm
  subst hX; exact hCXA

/-- `Bet A A B` (GeoCoq `between_trivial2`). -/
theorem between_trivial2 (A B : Tpoint) : Bet A A B :=
  between_symmetry (between_trivial B A)

/-- `Bet A B C → Bet B A C → A = B` (GeoCoq `between_equality`). -/
theorem between_equality {A B C : Tpoint} (h1 : Bet A B C) (h2 : Bet B A C) : A = B := by
  obtain ⟨x, hBxB, hAxA⟩ := inner_pasch A B C B A h1 h2
  have e1 : B = x := between_identity B x hBxB
  have e2 : A = x := between_identity A x hAxA
  exact e2.trans e1.symm

/-- `Bet A B C → Bet A C B → B = C` (GeoCoq `between_equality_2`). -/
theorem between_equality_2 {A B C : Tpoint} (h1 : Bet A B C) (h2 : Bet A C B) : B = C :=
  between_equality (between_symmetry h2) (between_symmetry h1)

/-- `Bet A B C → Bet A C D → Bet B C D` (GeoCoq `between_exchange3`). -/
theorem between_exchange3 {A B C D : Tpoint} (h1 : Bet A B C) (h2 : Bet A C D) :
    Bet B C D := by
  obtain ⟨x, hCxC, hBxD⟩ := inner_pasch D C A C B (between_symmetry h2) (between_symmetry h1)
  have hx : C = x := between_identity C x hCxC
  subst hx; exact hBxD

/-- `Bet A B D → Bet B C D → Bet A B C` (GeoCoq `between_inner_transitivity`). -/
theorem between_inner_transitivity {A B C D : Tpoint} (h1 : Bet A B D) (h2 : Bet B C D) :
    Bet A B C := by
  obtain ⟨x, hBxB, hCxA⟩ := inner_pasch A B D B C h1 h2
  have hx : B = x := between_identity B x hBxB
  subst hx; exact between_symmetry hCxA

/-! ### Distinctness from betweenness (GeoCoq `bet_neq*_neq`) -/

theorem bet_neq12_neq {A B C : Tpoint} (h : Bet A B C) (hAB : A ≠ B) : A ≠ C := by
  intro heq; rw [← heq] at h; exact hAB (between_identity A B h)

theorem bet_neq21_neq {A B C : Tpoint} (h : Bet A B C) (hBA : B ≠ A) : A ≠ C :=
  bet_neq12_neq h (Ne.symm hBA)

theorem bet_neq23_neq {A B C : Tpoint} (h : Bet A B C) (hBC : B ≠ C) : A ≠ C := by
  intro heq; rw [← heq] at h
  exact hBC ((between_identity A B h).symm.trans heq)

theorem bet_neq32_neq {A B C : Tpoint} (h : Bet A B C) (hCB : C ≠ B) : A ≠ C :=
  bet_neq23_neq h (Ne.symm hCB)

/-! ## `Out` base (Ch06, from the betweenness base) -/

/-- `Out A B C → Col A B C` (GeoCoq `out_col`). -/
theorem out_col {A B C : Tpoint} (h : Out A B C) : Col A B C := by
  obtain ⟨_, _, hb | hb⟩ := h
  · exact Or.inl hb
  · exact Or.inr (Or.inl (between_symmetry hb))

/-- `Out P A B → Out P B A` (GeoCoq `l6_6`, out symmetry). -/
theorem l6_6 {P A B : Tpoint} (h : Out P A B) : Out P B A := by
  obtain ⟨ha, hb, hbet⟩ := h
  exact ⟨hb, ha, hbet.symm⟩

/-- `B ≠ A → Bet A B C → Out A B C` (GeoCoq `bet_out`). -/
theorem bet_out {A B C : Tpoint} (hBA : B ≠ A) (h : Bet A B C) : Out A B C :=
  ⟨hBA, Ne.symm (bet_neq21_neq h hBA), Or.inl h⟩

/-- `B ≠ A → Bet C B A → Out A B C` (GeoCoq `bet_out_1`). -/
theorem bet_out_1 {A B C : Tpoint} (hBA : B ≠ A) (h : Bet C B A) : Out A B C :=
  bet_out hBA (between_symmetry h)

/-- `A ≠ P → Out P A A` (GeoCoq `out_trivial`, out reflexivity). -/
theorem out_trivial {P A : Tpoint} (h : A ≠ P) : Out P A A :=
  ⟨h, h, Or.inl (between_trivial P A)⟩

/-- `Out A B C → B ≠ A` (GeoCoq `out_diff1`). -/
theorem out_diff1 {A B C : Tpoint} (h : Out A B C) : B ≠ A := h.1

/-- `Out A B C → C ≠ A` (GeoCoq `out_diff2`). -/
theorem out_diff2 {A B C : Tpoint} (h : Out A B C) : C ≠ A := h.2.1

end GeocoqTranslate.Tarski.Base
