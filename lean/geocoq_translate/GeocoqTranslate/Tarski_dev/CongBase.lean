/-
Congruence base (Ch02) + segment addition `l2_11` — Tier 2, foundation of the cone.

All proven OUTRIGHT from the `Cong` axioms (`cong_pseudo_reflexivity`,
`cong_inner_transitivity`, `cong_identity`) and `segment_construction` /
`five_segment` — no assumption, names verbatim from GeoCoq. `l2_11` (segment
addition) is the first lemma above the Ch02 base that the `col3` cone needs.
-/
import GeocoqTranslate.Tarski.Definitions

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-! ## Congruence is an equivalence with endpoint swaps (GeoCoq Ch02) -/

/-- `Cong A B A B` (GeoCoq `cong_reflexivity`). -/
theorem cong_reflexivity (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B (cong_pseudo_reflexivity B A) (cong_pseudo_reflexivity B A)

/-- `Cong A B C D → Cong C D A B` (GeoCoq `cong_symmetry`). -/
theorem cong_symmetry {A B C D : Tpoint} (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_reflexivity A B)

/-- `Cong A B C D → Cong C D E F → Cong A B E F` (GeoCoq `cong_transitivity`). -/
theorem cong_transitivity {A B C D E F : Tpoint}
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symmetry h1) h2

/-- `Cong A B C D → Cong B A C D` (GeoCoq `cong_left_commutativity`). -/
theorem cong_left_commutativity {A B C D : Tpoint} (h : Cong A B C D) : Cong B A C D :=
  cong_transitivity (cong_pseudo_reflexivity B A) h

/-- `Cong A B C D → Cong A B D C` (GeoCoq `cong_right_commutativity`). -/
theorem cong_right_commutativity {A B C D : Tpoint} (h : Cong A B C D) : Cong A B D C :=
  cong_symmetry (cong_left_commutativity (cong_symmetry h))

/-- `Cong A B C D → Cong B A D C` (GeoCoq `cong_commutativity`). -/
theorem cong_commutativity {A B C D : Tpoint} (h : Cong A B C D) : Cong B A D C :=
  cong_left_commutativity (cong_right_commutativity h)

/-- `Cong A A B B` (GeoCoq `cong_trivial_identity`). -/
theorem cong_trivial_identity (A B : Tpoint) : Cong A A B B := by
  obtain ⟨E, _, hcong⟩ := segment_construction B A B B
  have hE : A = E := cong_identity A E B hcong
  subst hE; exact hcong

/-- `Cong A A C D → C = D` (GeoCoq `cong_reverse_identity`). -/
theorem cong_reverse_identity {A C D : Tpoint} (h : Cong A A C D) : C = D :=
  cong_identity C D A (cong_symmetry h)

/-- `A ≠ B → Cong A B C D → C ≠ D` (GeoCoq `cong_diff`). -/
theorem cong_diff {A B C D : Tpoint} (hAB : A ≠ B) (h : Cong A B C D) : C ≠ D := by
  intro heq; subst heq; exact hAB (cong_identity A B C h)

/-! ## Five-segment with the `OFSC` definition, and segment addition -/

/-- `OFSC … → A ≠ B → Cong C D C' D'` (GeoCoq `five_segment_with_def`). -/
theorem five_segment_with_def {A B C D A' B' C' D' : Tpoint}
    (h : OFSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨hb1, hb2, c1, c2, c3, c4⟩ := h
  exact five_segment A A' B B' C C' D D' c1 c2 c3 c4 hb1 hb2 hAB

/-- Segment addition: colinear congruent pieces sum to congruent wholes
    (GeoCoq `l2_11`). Proof: degenerate `A = B` via `cong_identity`; otherwise
    `five_segment` with `D := A`, `D' := A'`. -/
theorem l2_11 {A B C A' B' C' : Tpoint}
    (h1 : Bet A B C) (h2 : Bet A' B' C')
    (hab : Cong A B A' B') (hbc : Cong B C B' C') : Cong A C A' C' := by
  by_cases hAB : A = B
  · subst hAB
    have hA'B' : A' = B' := cong_identity _ _ _ (cong_symmetry hab)
    subst hA'B'; exact hbc
  · apply cong_commutativity
    exact five_segment A A' B B' C C' A A' hab hbc
      (cong_trivial_identity A A') (cong_commutativity hab) h1 h2 hAB

end GeocoqTranslate.Tarski.Base
