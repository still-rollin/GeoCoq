/-
Segment cone, next layer (Ch02 `construction_uniqueness` + Ch03 outer transitivity).

Builds on `CongBase` (`l2_11`, the `Cong` base) and `BetweenOutBase`
(`between_exchange3`, `between_inner_transitivity`, `between_symmetry`). All proven
outright from the axioms — no assumption. These are the outer-connectivity
betweenness lemmas (`between_exchange2/4`, `outer_transitivity_between`) that the
Ch06 oracle map calls (`between_exchange4` 3×, `outer_transitivity_between` 3×), and
they are prerequisites of the Ch04/Ch05 climb toward `l5_1` → `col3`.
-/
import GeocoqTranslate.Tarski_dev.CongBase
import GeocoqTranslate.Tarski_dev.BetweenOutBase

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-- Uniqueness of segment construction (GeoCoq `construction_uniqueness`): two points
    built the same distance beyond `A` from `Q` coincide. Uses `l2_11` + `five_segment`. -/
theorem construction_uniqueness {Q A B C X Y : Tpoint} (hQA : Q ≠ A)
    (hX : Bet Q A X) (hcX : Cong A X B C) (hY : Bet Q A Y) (hcY : Cong A Y B C) : X = Y := by
  have hAXY : Cong A X A Y := cong_transitivity hcX (cong_symmetry hcY)
  have hQXY : Cong Q X Q Y := l2_11 hX hY (cong_reflexivity Q A) hAXY
  have hofsc : OFSC Q A X Y Q A X X :=
    ⟨hX, hX, cong_reflexivity Q A, cong_reflexivity A X, cong_symmetry hQXY, cong_symmetry hAXY⟩
  exact cong_identity X Y X (five_segment_with_def hofsc hQA)

/-- `Bet A B C → Bet B C D → B ≠ C → Bet A C D` (GeoCoq `outer_transitivity_between2`). -/
theorem outer_transitivity_between2 {A B C D : Tpoint}
    (h1 : Bet A B C) (h2 : Bet B C D) (hBC : B ≠ C) : Bet A C D := by
  obtain ⟨x, hACx, hCxCD⟩ := segment_construction A C C D
  have hBCx : Bet B C x := between_exchange3 h1 hACx
  have hxD : x = D := construction_uniqueness hBC hBCx hCxCD h2 (cong_reflexivity C D)
  subst hxD; exact hACx

/-- `Bet A B D → Bet B C D → Bet A C D` (GeoCoq `between_exchange2`). -/
theorem between_exchange2 {A B C D : Tpoint} (h1 : Bet A B D) (h2 : Bet B C D) :
    Bet A C D := by
  by_cases hBC : B = C
  · subst hBC; exact h1
  · exact outer_transitivity_between2 (between_inner_transitivity h1 h2) h2 hBC

/-- `Bet A B C → Bet B C D → B ≠ C → Bet A B D` (GeoCoq `outer_transitivity_between`). -/
theorem outer_transitivity_between {A B C D : Tpoint}
    (h1 : Bet A B C) (h2 : Bet B C D) (hBC : B ≠ C) : Bet A B D :=
  between_symmetry (outer_transitivity_between2 (between_symmetry h2) (between_symmetry h1)
    (Ne.symm hBC))

/-- `Bet A B C → Bet A C D → Bet A B D` (GeoCoq `between_exchange4`). -/
theorem between_exchange4 {A B C D : Tpoint} (h1 : Bet A B C) (h2 : Bet A C D) :
    Bet A B D :=
  between_symmetry (between_exchange2 (between_symmetry h2) (between_symmetry h1))

/-! ## Existence of distinct points, and point construction (Ch03, from `lower_dim`) -/

/-- The lower-dimension axiom, packaged existentially (GeoCoq `lower_dim_ex`). -/
theorem lower_dim_ex : ∃ A B C : Tpoint, ¬ (Bet A B C ∨ Bet B C A ∨ Bet C A B) :=
  ⟨_, _, _, lower_dim⟩

/-- `∃ X Y, X ≠ Y` (GeoCoq `two_distinct_points`): two of the lower-dim points differ. -/
theorem two_distinct_points : ∃ X Y : Tpoint, X ≠ Y := by
  obtain ⟨A, B, C, h⟩ := lower_dim_ex (Tpoint := Tpoint)
  refine ⟨A, B, fun hAB => ?_⟩
  subst hAB; exact h (Or.inl (between_trivial2 A C))

/-- `∃ C, Bet A B C ∧ B ≠ C` (GeoCoq `point_construction_different`): extend `AB` to a
    strictly longer segment. The heuristic-flagged new-point step of the oracle. -/
theorem point_construction_different (A B : Tpoint) : ∃ C, Bet A B C ∧ B ≠ C := by
  obtain ⟨x, y, hxy⟩ := two_distinct_points (Tpoint := Tpoint)
  obtain ⟨F, hbet, hcong⟩ := segment_construction A B x y
  exact ⟨F, hbet, fun hBF => hxy (cong_reverse_identity (hBF ▸ hcong))⟩

end GeocoqTranslate.Tarski.Base
