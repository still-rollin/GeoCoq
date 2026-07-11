/-
Ch04 congruence/betweenness (`l4_2` .. `l4_17`) — the segment machinery the cone
needs before `l5_1`. Proven outright from the axioms + the Ch02/Ch03 base.

`l4_2` (inner five segment) is the hard one; the rest chain off it. The many `Cong`
normalisation steps (GeoCoq's `Cong`/`CongR` tactic) are discharged here by the
ported `cong_r`, via a `CongTheory` instance built from the proven `Cong` base.
-/
import GeocoqTranslate.Tarski_dev.SegmentCone
import GeocoqTranslate.Tarski_dev.CongR

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-- `CongTheory` for the real Tarski `Cong`, from the proven Ch02 base — so `cong_r`
    closes the congruence-closure goals below. Fully proven, no assumption. -/
instance congBaseTheory : CongR.CongTheory Tpoint Cong where
  refl := cong_reflexivity
  left_comm := fun _ _ _ _ h => cong_left_commutativity h
  sym := fun _ _ _ _ h => cong_symmetry h
  trans := fun _ _ _ _ _ _ h1 h2 => cong_transitivity h1 h2

/-- Inner five segment (GeoCoq `l4_2`): `IFSC … → Cong B D B' D'`. -/
theorem l4_2 {A B C D A' B' C' D' : Tpoint} (h : IFSC A B C D A' B' C' D') :
    Cong B D B' D' := by
  obtain ⟨hABC, hA'B'C', hAC, hBC, hAD, hCD⟩ := h
  by_cases hAC2 : A = C
  · -- degenerate `A = C`: forces `A = B` and `A' = B'`, then `Cong A D A' D'` is the goal
    rw [← hAC2] at hABC hAC
    have hAB : A = B := between_identity A B hABC
    have hA'C' : A' = C' := cong_reverse_identity hAC
    rw [← hA'C'] at hA'B'C'
    have hA'B' : A' = B' := between_identity A' B' hA'B'C'
    rw [← hAB, ← hA'B']; exact hAD
  · -- extend `AC` to `E` beyond `C`, copy on the primed side, apply five-segment twice
    obtain ⟨E, hACE, hCE⟩ := point_construction_different A C
    obtain ⟨E', hA'C'E', hcE'⟩ := segment_construction A' C' C E
    have hED : Cong E D E' D' :=
      five_segment_with_def
        (show OFSC A C E D A' C' E' D' from ⟨hACE, hA'C'E', hAC, by cong_r, hAD, hCD⟩) hAC2
    have hBCE : Bet E C B := between_symmetry (between_exchange3 hABC hACE)
    have hB'C'E' : Bet E' C' B' := between_symmetry (between_exchange3 hA'B'C' hA'C'E')
    exact five_segment_with_def
      (show OFSC E C B D E' C' B' D' from ⟨hBCE, hB'C'E', by cong_r, by cong_r, hED, hCD⟩)
      (Ne.symm hCE)

/-- GeoCoq `l4_3`: `Bet A B C → Bet A' B' C' → Cong A C A' C' → Cong B C B' C' → Cong A B A' B'`. -/
theorem l4_3 {A B C A' B' C' : Tpoint} (h1 : Bet A B C) (h2 : Bet A' B' C')
    (hAC : Cong A C A' C') (hBC : Cong B C B' C') : Cong A B A' B' :=
  cong_commutativity (l4_2 (show IFSC A B C A A' B' C' A' from
    ⟨h1, h2, hAC, hBC, cong_trivial_identity A A', by cong_r⟩))

/-- GeoCoq `l4_3_1`: `Bet A B C → Bet A' B' C' → Cong A B A' B' → Cong A C A' C' → Cong B C B' C'`. -/
theorem l4_3_1 {A B C A' B' C' : Tpoint} (h1 : Bet A B C) (h2 : Bet A' B' C')
    (hAB : Cong A B A' B') (hAC : Cong A C A' C') : Cong B C B' C' :=
  cong_commutativity (l4_3 (between_symmetry h1) (between_symmetry h2) (by cong_r) (by cong_r))

/-- GeoCoq `l4_5`: a betweenness point can be copied onto a congruent segment. -/
theorem l4_5 {A B C A' C' : Tpoint} (h : Bet A B C) (hAC : Cong A C A' C') :
    ∃ B', Bet A' B' C' ∧ Cong_3 A B C A' B' C' := by
  obtain ⟨x', hx'bet, hx'ne⟩ := point_construction_different C' A'
  obtain ⟨B', hb1, hc1⟩ := segment_construction x' A' A B
  obtain ⟨C'', hb2, hc2⟩ := segment_construction x' B' B C
  have hA'B'C'' : Bet A' B' C'' := between_exchange3 hb1 hb2
  have hxA'C'' : Bet x' A' C'' := between_exchange4 hb1 hb2
  have hC'' : C'' = C' :=
    construction_uniqueness (Ne.symm hx'ne) hxA'C''
      (l2_11 hA'B'C'' h hc1 hc2) (between_symmetry hx'bet) (by cong_r)
  subst hC''
  exact ⟨B', hA'B'C'', by cong_r, hAC, by cong_r⟩

/-- GeoCoq `l4_6`: betweenness transfers along a triangle congruence. -/
theorem l4_6 {A B C A' B' C' : Tpoint} (h : Bet A B C) (hc3 : Cong_3 A B C A' B' C') :
    Bet A' B' C' := by
  obtain ⟨hAB, hAC, hBC⟩ := hc3
  obtain ⟨B'', hbet'', hc3''⟩ := l4_5 h hAC
  obtain ⟨hAB'', hAC'', hBC''⟩ := hc3''
  have hxx : Cong B'' B'' B'' B' :=
    l4_2 (show IFSC A' B'' C' B'' A' B'' C' B' from
      ⟨hbet'', hbet'', by cong_r, by cong_r, by cong_r, by cong_r⟩)
  have hBB : B'' = B' := cong_reverse_identity hxx
  rw [hBB] at hbet''; exact hbet''

/-- GeoCoq `l4_16`: five-segment with collinearity (`FSC`). Case split on `Col A B C`. -/
theorem l4_16 {A B C D A' B' C' D' : Tpoint} (h : FSC A B C D A' B' C' D') (hAB : A ≠ B) :
    Cong C D C' D' := by
  obtain ⟨hcol, ⟨hc3AB, hc3AC, hc3BC⟩, hAD, hBD⟩ := h
  rcases hcol with hb | hb | hb
  · -- Bet A B C
    have hb' : Bet A' B' C' := l4_6 hb ⟨hc3AB, hc3AC, hc3BC⟩
    exact five_segment_with_def
      (show OFSC A B C D A' B' C' D' from ⟨hb, hb', hc3AB, hc3BC, hAD, hBD⟩) hAB
  · -- Bet B C A
    have hb' : Bet B' C' A' := l4_6 hb ⟨hc3BC, by cong_r, by cong_r⟩
    exact l4_2 (show IFSC B C A D B' C' A' D' from
      ⟨hb, hb', by cong_r, by cong_r, hBD, hAD⟩)
  · -- Bet C A B
    have hb' : Bet C' A' B' := l4_6 hb ⟨by cong_r, by cong_r, hc3AB⟩
    exact five_segment_with_def
      (show OFSC B A C D B' A' C' D' from
        ⟨between_symmetry hb, between_symmetry hb', by cong_r, by cong_r, hBD, hAD⟩)
      (Ne.symm hAB)

/-- GeoCoq `l4_17`: three points collinear with `A ≠ B`, equidistant from `P` and `Q`
    at `A` and `B`, are also equidistant at any collinear `C`. -/
theorem l4_17 {A B C P Q : Tpoint} (hAB : A ≠ B) (hcol : Col A B C)
    (hAP : Cong A P A Q) (hBP : Cong B P B Q) : Cong C P C Q :=
  l4_16 (show FSC A B C P A B C Q from
    ⟨hcol, ⟨cong_reflexivity A B, cong_reflexivity A C, cong_reflexivity B C⟩, hAP, hBP⟩) hAB

end GeocoqTranslate.Tarski.Base
