import GeocoqTranslate.Tarski_dev.Ch05Bet
import GeocoqTranslate.Tarski_dev.Ch04Cong

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l4_2_c (A B C D A' B' C' D' : Tpoint)
    (h : IFSC A B C D A' B' C' D') : Cong B D B' D' := sorry

theorem l4_3_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A C A' C') (h₄ : Cong B C B' C') : Cong A B A' B' :=
  cong_commutativity (l4_2 (⟨h₁, (⟨h₂, (⟨h₃, (⟨h₄, (⟨(cong_trivial_identity A A'), (cong_symmetry (cong_symmetry (cong_commutativity h₃)))⟩)⟩)⟩)⟩)⟩))

theorem l4_3_1_c (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A B A' B') (h₄ : Cong A C A' C') : Cong B C B' C' :=
  cong_commutativity (l4_3 (between_symmetry h₁) (between_symmetry h₂) (cong_symmetry (cong_symmetry (cong_commutativity h₄))) (cong_symmetry (cong_symmetry (cong_commutativity h₃))))

theorem l4_5_c (A B C A' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong A C A' C') :
    ∃ B', Bet A' B' C' ∧ Cong_3 A B C A' B' C' := by
  have H1 := point_construction_different C' A'
  obtain ⟨x', H2⟩ := H1
  obtain ⟨H3, H4⟩ := H2
  have sg := segment_construction x' A' A B
  obtain ⟨B', H5⟩ := sg
  obtain ⟨H6, H7⟩ := H5
  have sg0 := segment_construction x' B' B C
  obtain ⟨C'', H8⟩ := sg0
  obtain ⟨H9, H10⟩ := H8
  have H11 := between_symmetry (between_symmetry (between_exchange3 H6 H9))
  have H12 := construction_uniqueness (Ne.symm H4) (between_symmetry (between_symmetry (between_exchange4 H6 H9))) (l2_11 H11 hBet H7 H10) (between_symmetry H3) (cong_symmetry hCong)
  subst H12
  exact ⟨B', (⟨H11, (⟨(cong_symmetry H7), (⟨hCong, (cong_symmetry H10)⟩)⟩)⟩)⟩

theorem l4_6_c (A B C A' B' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A' B' C') : Bet A' B' C' := sorry

theorem cong3_bet_eq_c (A B C X : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A X C) : X = B := sorry

#print axioms GeocoqTranslate.Tarski.Base.l4_2_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_c
#print axioms GeocoqTranslate.Tarski.Base.l4_3_1_c
#print axioms GeocoqTranslate.Tarski.Base.l4_5_c
#print axioms GeocoqTranslate.Tarski.Base.l4_6_c
#print axioms GeocoqTranslate.Tarski.Base.cong3_bet_eq_c
end GeocoqTranslate.Tarski.Base