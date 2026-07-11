/-
Ch05 connectivity of betweenness — the capstone of the cone.

`l5_1` (`A ≠ B → Bet A B C → Bet A B D → Bet A C D ∨ Bet A D C`) is GeoCoq's ~100-line
proof, ported outright from the axioms + the Ch02–Ch04 base (`l2_11`, `l4_2`, `l4_16`,
`l4_17`, `construction_uniqueness`, `inner_pasch`, …); the many `Cong` normalisations
are discharged by `cong_r`. `l5_2`/`l5_3` reduce to it. These unblock `l6_16_1` →
`col_transitivity` = `col3`, which discharges `Col3Assumption`.
-/
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

/-- GeoCoq `l5_1`: two segments from `A` through `B` are nested one way or the other. -/
theorem l5_1 {A B C D : Tpoint} (hAB : A ≠ B) (hABC : Bet A B C) (hABD : Bet A B D) :
    Bet A C D ∨ Bet A D C := by
  obtain ⟨C', hADC', hDC'⟩ := segment_construction A D C D
  obtain ⟨D', hACD', hCD'⟩ := segment_construction A C C D
  obtain ⟨B', hAC'B', hC'B'⟩ := segment_construction A C' C B
  obtain ⟨B'', hAD'B'', hD'B''⟩ := segment_construction A D' D B
  -- H10 : Cong B C' B'' C
  have hBDC' : Bet B D C' := between_exchange3 hABD hADC'
  have hB''D'C : Bet B'' D' C :=
    between_inner_transitivity (between_symmetry hAD'B'') (between_symmetry hACD')
  have h10 : Cong B C' B'' C := l2_11 hBDC' hB''D'C (by cong_r) (by cong_r)
  -- Bet A B C'
  have hABC' : Bet A B C' := by
    by_cases hBD : B = D
    · subst hBD; exact hADC'
    · exact between_symmetry
        (outer_transitivity_between2 (between_symmetry hBDC') (between_symmetry hABD) (Ne.symm hBD))
  have hBC'B' : Bet B C' B' := between_exchange3 hABC' hAC'B'
  -- Bet B'' C B
  have hB''CB : Bet B'' C B := by
    by_cases hCD'e : C = D'
    · subst hCD'e; exact between_symmetry (between_exchange3 hABC hAD'B'')
    · exact outer_transitivity_between2 hB''D'C
        (between_symmetry (between_exchange3 hABC hACD')) (Ne.symm hCD'e)
  -- H11 : Cong B B' B'' B
  have h11 : Cong B B' B'' B := l2_11 hBC'B' hB''CB h10 hC'B'
  -- H12 : B'' = B'
  have hBB : B' = B'' :=
    (construction_uniqueness (Q := A) (A := B) (B := B) (C := B'') hAB
      (between_exchange4 (between_exchange4 hABC hACD') hAD'B'') (by cong_r)
      (between_exchange4 hABC' hAC'B') (by cong_r)).symm
  subst hBB
  -- Bet B C D'
  have hBCD' : Bet B C D' := between_exchange3 hABC hACD'
  -- FSC B C D' C' B' C' D C  (H13)
  have hfsc : FSC B C D' C' B' C' D C :=
    ⟨Or.inl hBCD',
     ⟨by cong_r,
      l2_11 hBCD' (between_symmetry (between_exchange3 hADC' hAC'B')) (by cong_r) (by cong_r),
      by cong_r⟩,
     by cong_r, cong_right_commutativity (cong_reflexivity C C')⟩
  -- degenerate B = C closes the goal directly
  by_cases hBC : B = C
  · subst hBC; exact Or.inl hABD
  -- Cong D' C' D C, the Pasch point E, and the two inner-five-segment facts
  have hD'C' : Cong D' C' D C := l4_16 hfsc hBC
  obtain ⟨E, hCEC', hDED'⟩ :=
    inner_pasch D' C' A C D (between_symmetry hACD') (between_symmetry hADC')
  have hifsc1 : IFSC D E D' C D E D' C' :=
    ⟨hDED', hDED', cong_reflexivity D D', cong_reflexivity E D', by cong_r, by cong_r⟩
  have hifsc2 : IFSC C E C' D C E C' D' :=
    ⟨hCEC', hCEC', cong_reflexivity C C', cong_reflexivity E C', by cong_r, by cong_r⟩
  have hECE : Cong E C E C' := l4_2 hifsc1
  have hEDE : Cong E D E D' := l4_2 hifsc2
  -- degenerate C = C' closes the goal directly
  by_cases hCC' : C = C'
  · subst hCC'; exact Or.inr hADC'
  -- distinctness: C ≠ D (else C = C') and C ≠ D' (else C = D)
  have hCDne : C ≠ D := fun h => by subst h; exact hCC' (cong_identity _ _ _ hDC')
  have hCD'ne : C ≠ D' := fun h => by subst h; exact hCDne (cong_reverse_identity hCD')
  -- three constructions P, R, Q
  obtain ⟨P, hC'CP, hCP⟩ := segment_construction C' C C D'
  obtain ⟨R, hD'CR, hCR⟩ := segment_construction D' C C E
  obtain ⟨Q, hPRQ, hRQ⟩ := segment_construction P R R P
  have hBetPCE : Bet P C E := between_inner_transitivity (between_symmetry hC'CP) hCEC'
  have hfsc3 : FSC D' C R P P C E D' :=
    ⟨Or.inl hD'CR,
     ⟨by cong_r, l2_11 hD'CR hBetPCE (by cong_r) hCR, hCR⟩,
     cong_right_commutativity (cong_reflexivity D' P), hCP⟩
  have hRP : Cong R P E D' := l4_16 hfsc3 (Ne.symm hCD'ne)
  have hRQ2 : Cong R Q E D := by cong_r
  have hfsc4 : FSC D' E D C P R Q C :=
    ⟨Or.inl (between_symmetry hDED'),
     ⟨by cong_r, l2_11 (between_symmetry hDED') hPRQ (by cong_r) (by cong_r), by cong_r⟩,
     by cong_r, by cong_r⟩
  have hDCQC : Cong D C Q C := by
    by_cases hD'E : D' = E
    · subst hD'E
      have hD'D : D' = D := cong_identity _ _ _ hEDE
      have hQP : Q = P :=
        (cong_identity _ _ _ (hD'D ▸ hRQ2)).symm.trans (cong_identity _ _ _ hRP)
      have base : Cong D' C P C := by cong_r
      rw [hD'D, ← hQP] at base; exact base
    · exact l4_16 hfsc4 hD'E
  have hCPCQ : Cong C P C Q := by cong_r
  -- distinctness R ≠ C (else C = E = C')
  have hRCne : R ≠ C := by
    intro h
    rw [h] at hCR
    have hCE : C = E := cong_reverse_identity hCR
    rw [hCE] at hECE
    exact hCC' (hCE.trans (cong_reverse_identity hECE))
  have hD'PD'Q : Cong D' P D' Q :=
    l4_17 hRCne (Or.inl (between_symmetry hD'CR)) (by cong_r) hCPCQ
  have hBPBQ : Cong B P B Q :=
    l4_17 hCD'ne (Or.inr (Or.inr (between_exchange3 hABC hACD'))) hCPCQ hD'PD'Q
  have hB'PB'Q : Cong B' P B' Q :=
    l4_17 hCD'ne (Or.inl (between_exchange3 hACD' hAD'B'')) hCPCQ hD'PD'Q
  have hBetBC'B' : Bet B C' B' := between_exchange3 hABC' hAC'B'
  have hBB'ne : B ≠ B' := by
    intro h
    have hBC' : B = C' := between_equality_2 hABC' (h.symm ▸ hAC'B')
    rw [← hBC', ← h] at hC'B'
    exact hBC (cong_reverse_identity hC'B').symm
  have hC'PC'Q : Cong C' P C' Q :=
    l4_17 hBB'ne (Or.inr (Or.inl (between_symmetry hBetBC'B'))) hBPBQ hB'PB'Q
  have hPPPQ : Cong P P P Q :=
    l4_17 hCC' (Or.inr (Or.inr (between_symmetry hC'CP))) hCPCQ hC'PC'Q
  -- the constructions collapse: P = Q ⟹ R = P ⟹ E = D' ⟹ D' = D, giving Bet A C D
  have hPQ : P = Q := cong_reverse_identity hPPPQ
  have hPR : P = R := between_identity P R (hPQ.symm ▸ hPRQ)
  have hED' : E = D' := cong_reverse_identity (hPR.symm ▸ hRP)
  have hD'D2 : D' = D := cong_identity _ _ _ (hED' ▸ hEDE)
  exact Or.inl (hD'D2 ▸ hACD')

/-- GeoCoq `l5_2`. -/
theorem l5_2 {A B C D : Tpoint} (hAB : A ≠ B) (hABC : Bet A B C) (hABD : Bet A B D) :
    Bet B C D ∨ Bet B D C := by
  rcases l5_1 hAB hABC hABD with h | h
  · exact Or.inl (between_exchange3 hABC h)
  · exact Or.inr (between_exchange3 hABD h)

/-- GeoCoq `l5_3`. -/
theorem l5_3 {A B C D : Tpoint} (h1 : Bet A B D) (h2 : Bet A C D) :
    Bet A B C ∨ Bet A C B := by
  obtain ⟨P, hDAP, hAP⟩ := point_construction_different D A
  exact l5_2 (Ne.symm hAP)
    (between_inner_transitivity (between_symmetry hDAP) h1)
    (between_inner_transitivity (between_symmetry hDAP) h2)

end GeocoqTranslate.Tarski.Base
