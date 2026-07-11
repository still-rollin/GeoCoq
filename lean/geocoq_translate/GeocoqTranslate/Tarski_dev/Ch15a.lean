import GeocoqTranslate.Tarski_dev.Ch14c

namespace GeocoqTranslate.Tarski.Base
open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint] [Tarski_2D Tpoint] [Tarski_euclidean Tpoint]

theorem length_pos_c :
    ∀ (O E E' A B L : Tpoint), Length O E E' A B L → LeP O E E' O L := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H1⟩ := b6
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  exact H3
theorem length_id_1_c :
    ∀ (O E E' A B : Tpoint), Length O E E' A B O → A=B := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨_, H0⟩ := b5
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  have H3 := (by cong_r)
  have H4 := cong_identity b3 b4 b0 H3
  subst H4
  exact rfl
theorem length_id_2_c :
    ∀ (O E E' A : Tpoint), O ≠ E → Length O E E' A A O :=
  fun b0 b1 b2 b3 b4 =>
  ⟨b4, (⟨((by colr)), (⟨(Or.inr rfl), (cong_trivial_identity b0 b3)⟩)⟩)⟩
theorem length_id_c :
    ∀ (O E E' A B : Tpoint), Length O E E' A B O ↔ (A=B ∧ O ≠ E) := by
  intro b0 b1 b2 b3 b4
  exact ⟨(fun H => ⟨(length_id_1_c b0 b1 b2 b3 b4 H), (((fun H0 => (by
  obtain ⟨H1, H2⟩ := H
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, _⟩ := H3
  have H4 := H1 H0
  exact (H4).elim))))⟩), (fun H => (by
  obtain ⟨H0, H1⟩ := H
  subst H0
  exact length_id_2_c b0 b1 b2 b4 H1))⟩
theorem length_eq_cong_1_c :
    ∀ (O E E' A B C D AB : Tpoint), Length O E E' A B AB → Length O E E' C D AB → Cong A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨_, H1⟩ := b9
  obtain ⟨_, H2⟩ := H1
  obtain ⟨_, H3⟩ := H2
  obtain ⟨_, H4⟩ := b8
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  exact (by cong_r)
theorem length_eq_cong_2_c :
    ∀ (O E E' A B C D AB : Tpoint), Length O E E' A B AB → Cong A B C D → Length O E E' C D AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  obtain ⟨H1, H2⟩ := b8
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  exact ⟨H1, (⟨H3, (⟨H5, ((by cong_r))⟩)⟩)⟩
theorem ltP_pos_c :
    ∀ (O E E' A : Tpoint), LtP O E E' O A → Ps O E A := by
  intro b0 b1 b2 b3 b4
  obtain ⟨A', H0⟩ := b4
  obtain ⟨H1, H2⟩ := H0
  have H3 := (by
  obtain ⟨X, H3⟩ := H1
  obtain ⟨_, H4⟩ := H3
  obtain ⟨H5, _⟩ := H4
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, _⟩ := H9
  exact ⟨((fun H10 => (let H11 := H6 H10; (H11).elim))), H8⟩)
  obtain ⟨H4, H5⟩ := H3
  have HH := diff_A_O_c b0 b1 b2 b3 H4 H5
  have H6 := diff_uniqueness_c b0 b1 b2 b3 b0 b3 A' HH H1
  subst H6
  exact H2
theorem bet_leP_c :
    ∀ (O E E' AB CD : Tpoint), Bet O AB CD → LeP O E E' O AB → LeP O E E' O CD → LeP O E E' AB CD := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b6 with H2 | H2
  · rcases b7 with H3 | H3
    · obtain ⟨P, H4⟩ := H2
      obtain ⟨H5, H6⟩ := H4
      obtain ⟨Q, H7⟩ := H3
      obtain ⟨H8, H9⟩ := H7
      have H10 := (by
  obtain ⟨X, H10⟩ := H5
  obtain ⟨_, H11⟩ := H10
  obtain ⟨Y, H12⟩ := H8
  obtain ⟨_, H13⟩ := H12
  obtain ⟨H14, _⟩ := H13
  obtain ⟨H15, _⟩ := H11
  obtain ⟨H16, H17⟩ := H14
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨_, H20⟩ := H19
  obtain ⟨_, H21⟩ := H15
  obtain ⟨H22, H23⟩ := H21
  obtain ⟨_, H24⟩ := H23
  exact ⟨(⟨H16, (⟨H22, (⟨H18, H24⟩)⟩)⟩), H20⟩)
      obtain ⟨H11, H12⟩ := H10
      obtain ⟨H13, H14⟩ := H11
      obtain ⟨H15, H16⟩ := H14
      obtain ⟨H17, H18⟩ := H16
      have H19 := diff_uniqueness_c b0 b1 b2 b3 b0 P b3 H5 (diff_A_O_c b0 b1 b2 b3 H13 H15)
      subst H19
      have H21 := diff_uniqueness_c b0 b1 b2 b4 b0 Q b4 H8 (diff_A_O_c b0 b1 b2 b4 H13 H17)
      subst H21
      have o := point_equality_decidability b3 b4
      rcases o with H23 | H23
      · exact Or.inr H23
      · exact Or.inl ((let HH := opp_exists_c b3 H15; (by
  obtain ⟨AB', H24⟩ := HH
  have H25 := sum_exists_c b4 AB' H17 ((by
  obtain ⟨H25, _⟩ := H24
  obtain ⟨_, H26⟩ := H25
  obtain ⟨H27, H28⟩ := H26
  obtain ⟨_, _⟩ := H28
  exact H27))
  obtain ⟨P0, H26⟩ := H25
  exact ⟨P0, (⟨(⟨AB', (⟨H24, H26⟩)⟩), ((let H27 := ⟨AB', (⟨H24, H26⟩)⟩; (let H28 := diff_sum_c b0 b1 b2 b3 P0 b4 H27; (let o0 := point_equality_decidability b3 b0; (by
  rcases o0 with H29 | H29
  · subst H29
    obtain ⟨H31, H32⟩ := H6
    obtain ⟨_, H33⟩ := H32
    rcases H33 with _ | _
    · have H34 := (let H34 := rfl; H31 H34)
      exact (H34).elim
    · have H34 := (let H34 := rfl; H31 H34)
      exact (H34).elim
  · have H30 := sum_cong_c b3 P0 b4 H28 (Or.inl H29)
    obtain ⟨H31, H32⟩ := H30
    obtain ⟨H33, H34⟩ := H32
    obtain ⟨H35, H36⟩ := H34
    obtain ⟨H37, H38⟩ := H36
    have H39 := l4_6 b5 (⟨H35, (⟨((by cong_r)), ((by cong_r))⟩)⟩)
    exact ⟨((fun H40 => (by
  subst H40
  have H47 := (let H47 := (by cong_r); cong_identity b3 b4 b0 ((by cong_r)))
  subst H47
  rcases H38 with _ | _
  · have H50 := (let H50 := rfl; H23 H50)
    exact (H50).elim
  · have H50 := (let H50 := rfl; H23 H50)
    exact (H50).elim))), (⟨((fun H40 => (by
  subst H40
  exact H13 ((by colr))))), ((by
  obtain ⟨_, H40⟩ := H9
  obtain ⟨_, H41⟩ := H40
  rcases H41 with H42 | H42
  · exact Or.inl (between_exchange4 (between_symmetry H39) H42)
  · exact l5_3 (between_symmetry H39) H42))⟩)⟩)))))⟩)⟩)))
    · subst H3
      have H5 := between_identity b0 b3 b5
      subst H5
      exact Or.inr rfl
  · rcases b7 with H3 | H3
    · subst H2
      exact Or.inl H3
    · subst H2
      subst H3
      exact Or.inr rfl
theorem leP_bet_c :
    ∀ (O E E' AB CD : Tpoint), LeP O E E' AB CD → LeP O E E' O AB → LeP O E E' O CD → Bet O AB CD := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  rcases b5 with H2 | H2
  · obtain ⟨X, H3⟩ := H2
    obtain ⟨H4, H5⟩ := H3
    have H6 := diff_sum_c b0 b1 b2 b3 X b4 H4
    have H7 := (by
  rcases b6 with H7 | H7
  · exact Or.inl ((let H8 := ltP_pos_c b0 b1 b2 b3 H7; l6_7_c b0 b3 b1 X H8 (l6_6 H5)))
  · exact Or.inr (Eq.symm H7))
    rcases H7 with H8 | H8
    · exact l14_36_a_c b0 b1 b2 b3 X b4 H6 H8
    · subst H8
      exact between_trivial2 b0 b4
  · subst H2
    exact between_trivial b0 b3
theorem length_Ar2_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → (Col O E AB ∧ ¬ Col O E E') ∨ AB = O := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H0⟩ := b6
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, _⟩ := H2
  rcases H3 with H4 | H4
  · exact Or.inl (⟨H1, ((by
  obtain ⟨P, H5⟩ := H4
  obtain ⟨H6, _⟩ := H5
  obtain ⟨Q, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨H9, _⟩ := H8
  intro H10
  obtain ⟨H11, H12⟩ := H9
  obtain ⟨_, H13⟩ := H12
  obtain ⟨_, _⟩ := H13
  have H14 := H11 H10
  exact (H14).elim))⟩)
  · exact Or.inr (Eq.symm H4)
theorem length_leP_le_1_c :
    ∀ (O E E' A B C D AB CD : Tpoint), Length O E E' A B AB → Length O E E' C D CD → LeP O E E' AB CD → Le A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨_, H2⟩ := b10
  obtain ⟨_, H3⟩ := H2
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨_, H6⟩ := b9
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  have H10 := leP_bet_c b0 b1 b2 b7 b8 b11 H8 H4
  have sg := segment_construction b6 b5 b3 b4
  obtain ⟨M', H11⟩ := sg
  obtain ⟨_, H12⟩ := H11
  have HH := symmetric_point_construction_c M' b5
  obtain ⟨M, H13⟩ := HH
  obtain ⟨_, H14⟩ := H13
  have H15 := (by cong_r)
  exact le_transitivity_c b3 b4 b5 M b5 b6 (⟨M, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial b5 M))))), H15⟩)⟩) ((let H16 := ⟨b7, (⟨H10, ((by cong_r))⟩)⟩; l5_6_c b0 b7 b0 b8 b5 M b5 b6 H16 ((by cong_r)) H5))
theorem length_leP_le_2_c :
    ∀ (O E E' A B C D AB CD : Tpoint), Length O E E' A B AB → Length O E E' C D CD → Le A B C D → LeP O E E' AB CD := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have HH1 := length_Ar2_c b0 b1 b2 b3 b4 b7 b9
  have HH2 := length_Ar2_c b0 b1 b2 b5 b6 b8 b10
  obtain ⟨_, H2⟩ := b10
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨_, H7⟩ := b9
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  exact bet_leP_c b0 b1 b2 b7 b8 ((let o := point_equality_decidability b0 b8; (by
  rcases o with H12 | H12
  · subst H12
    have H14 := (by cong_r)
    have H15 := cong_identity b5 b6 b0 H14
    subst H15
    obtain ⟨X, H17⟩ := b11
    obtain ⟨H18, H19⟩ := H17
    have H20 := between_identity b5 X H18
    subst H20
    have H22 := cong_identity b3 b4 b5 H19
    subst H22
    have H24 := cong_identity b0 b7 b3 H11
    subst H24
    exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b0))))
  · have H13 := l5_6_c b3 b4 b5 b6 b0 b7 b0 b8 b11 ((by cong_r)) ((by cong_r))
    obtain ⟨M, H14⟩ := H13
    obtain ⟨H15, H16⟩ := H14
    rcases HH1 with H17 | H17
    · rcases HH2 with H18 | H18
      · obtain ⟨H19, H20⟩ := H18
        obtain ⟨H21, _⟩ := H17
        obtain ⟨P, H22⟩ := b11
        obtain ⟨_, _⟩ := H22
        rcases H10 with H23 | H23
        · rcases H5 with H24 | H24
          · obtain ⟨X, H25⟩ := H23
            obtain ⟨H26, H27⟩ := H25
            obtain ⟨Y, H28⟩ := H24
            obtain ⟨H29, H30⟩ := H28
            have H31 := diff_sum_c b0 b1 b2 b0 X b7 H26
            have H32 := diff_sum_c b0 b1 b2 b0 Y b8 H29
            have H33 := sum_cong_c b0 X b7 H31 (Or.inr ((fun H33 => (by
  subst H33
  obtain ⟨H35, H36⟩ := H27
  obtain ⟨_, H37⟩ := H36
  rcases H37 with _ | _
  · have H38 := (let H38 := rfl; H35 H38)
    exact (H38).elim
  · have H38 := (let H38 := rfl; H35 H38)
    exact (H38).elim))))
            have H34 := sum_cong_c b0 Y b8 H32 (Or.inr ((fun H34 => (by
  subst H34
  obtain ⟨H36, H37⟩ := H30
  obtain ⟨_, H38⟩ := H37
  rcases H38 with _ | _
  · have H39 := (let H39 := rfl; H36 H39)
    exact (H39).elim
  · have H39 := (let H39 := rfl; H36 H39)
    exact (H39).elim))))
            obtain ⟨_, H35⟩ := H34
            obtain ⟨H36, H37⟩ := H35
            obtain ⟨H38, H39⟩ := H37
            obtain ⟨H40, H41⟩ := H39
            obtain ⟨_, H42⟩ := H33
            obtain ⟨H43, H44⟩ := H42
            obtain ⟨H45, H46⟩ := H44
            obtain ⟨H47, H48⟩ := H46
            have H49 := (by cong_r)
            have H50 := cong_identity b8 Y b0 H49
            subst H50
            have H53 := (by cong_r)
            have H54 := cong_identity b7 X b0 H53
            subst H54
            have H57 := l7_20_c b0 b7 M (((let H57 := l6_7_c b0 b7 b1 b8 H27 (l6_6 H30); (let H58 := out_col H57; (let H59 := bet_col_c b0 M b8 H15; (by colr)))))) H16
            rcases H57 with H58 | H58
            · subst H58
              exact H15
            · obtain ⟨H59, H60⟩ := H58
              have H61 := l6_7_c b0 b7 b1 b8 H27 (l6_6 H30)
              have H62 := outer_transitivity_between H59 H15 ((fun H62 => (by
  subst H62
  have H66 := cong_identity b7 b0 b0 H60
  subst H66
  rcases H48 with H68 | H68
  · rcases H41 with _ | _
    · have H69 := (let H69 := rfl; H68 H69)
      exact (H69).elim
    · have H69 := (let H69 := rfl; H68 H69)
      exact (H69).elim
  · rcases H41 with _ | _
    · have H69 := (let H69 := rfl; H68 H69)
      exact (H69).elim
    · have H69 := (let H69 := rfl; H68 H69)
      exact (H69).elim)))
              obtain ⟨H63, H64⟩ := H61
              obtain ⟨_, H65⟩ := H64
              rcases H65 with H66 | H66
              · have H67 := between_equality H62 H66
                subst H67
                exact H66
              · have H67 := between_exchange3 (between_symmetry H66) H62
                have H68 := (let H68 := between_equality (between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial b0 b8))))) H67; ((H12 H68)).elim)
                rcases H48 with _ | _
                · rcases H41 with H69 | H69
                  · have H70 := H12 H68
                    have H71 := H69 H68
                    exact (H70).elim
                  · have H70 := H12 H68
                    have H71 := H69 H68
                    exact (H70).elim
                · rcases H41 with H69 | H69
                  · have H70 := H12 H68
                    have H71 := H69 H68
                    exact (H70).elim
                  · have H70 := H12 H68
                    have H71 := H69 H68
                    exact (H70).elim
          · subst H24
            have H26 := (let H26 := rfl; H12 H26)
            exact (H26).elim
        · rcases H5 with _ | H24
          · subst H23
            exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b8))))
          · subst H24
            have H26 := (let H26 := rfl; H12 H26)
            exact (H26).elim
      · subst H18
        obtain ⟨_, _⟩ := H17
        have H20 := (let H20 := rfl; H12 H20)
        exact (H20).elim
    · rcases HH2 with _ | H18
      · subst H17
        exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b8))))
      · subst H18
        have H20 := (let H20 := rfl; H12 H20)
        exact (H20).elim))) H10 H5
theorem l15_3_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Cong O B A C := by
  intro b0 b1 b2 b3 b4 b5 b6
  have H0 := (by
  obtain ⟨H0, _⟩ := b6
  exact H0)
  obtain ⟨H1, H2⟩ := H0
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  have o := point_equality_decidability b3 b0
  rcases o with H7 | H7
  · subst H7
    have H9 := sum_uniqueness_c b0 b4 b4 b5 (sum_O_B_c b4 H5) b6
    subst H9
    exact (by cong_r)
  · have H8 := sum_cong_c b3 b4 b5 b6 (Or.inl H7)
    obtain ⟨_, H9⟩ := H8
    obtain ⟨_, H10⟩ := H9
    obtain ⟨_, H11⟩ := H10
    obtain ⟨H12, _⟩ := H11
    exact (by cong_r)
theorem length_uniqueness_c :
    ∀ (O E E' A B AB AB' : Tpoint), Length O E E' A B AB → Length O E E' A B AB' → AB = AB' := sorry

theorem length_cong_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → Cong A B O AB := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨_, H0⟩ := b6
  obtain ⟨_, H1⟩ := H0
  obtain ⟨_, H2⟩ := H1
  exact (by cong_r)
theorem length_Ps_c :
    ∀ (O E E' A B AB : Tpoint), AB ≠ O → Length O E E' A B AB → Ps O E AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  rcases H4 with H6 | H6
  · obtain ⟨X, H7⟩ := H6
    obtain ⟨H8, H9⟩ := H7
    have H10 := diff_sum_c b0 b1 b2 b0 X b5 H8
    have H11 := sum_cong_c b0 X b5 H10 (Or.inr ((fun H11 => (by
  subst H11
  obtain ⟨H13, H14⟩ := H9
  obtain ⟨_, H15⟩ := H14
  rcases H15 with _ | _
  · have H16 := (let H16 := rfl; H13 H16)
    exact (H16).elim
  · have H16 := (let H16 := rfl; H13 H16)
    exact (H16).elim))))
    obtain ⟨_, H12⟩ := H11
    obtain ⟨H13, H14⟩ := H12
    obtain ⟨H15, H16⟩ := H14
    obtain ⟨H17, H18⟩ := H16
    have H19 := (by cong_r)
    have H20 := cong_identity b5 X b0 H19
    subst H20
    exact H9
  · subst H6
    have H8 := (let H8 := rfl; b6 H8)
    exact (H8).elim
theorem length_not_col_null_c :
    ∀ (O E E' A B AB : Tpoint), Col O E E' → Length O E E' A B AB → AB=O := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨_, H1⟩ := b7
  obtain ⟨_, H2⟩ := H1
  obtain ⟨H3, _⟩ := H2
  rcases H3 with H4 | H4
  · obtain ⟨X, H5⟩ := H4
    obtain ⟨H6, _⟩ := H5
    have H7 := diff_sum_c b0 b1 b2 b0 X b5 H6
    obtain ⟨H8, _⟩ := H7
    obtain ⟨H9, H10⟩ := H8
    obtain ⟨_, H11⟩ := H10
    obtain ⟨_, _⟩ := H11
    exact ((H9 b6)).elim
  · exact Eq.symm H4
theorem triangular_equality_equiv_c :
    (∀ O E A , O ≠ E → (∀ (E' B C AB BC AC : Tpoint), Bet A B C → Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC → Sum O E E' AB BC AC)) ↔ (∀ (O E E' A B C AB BC AC : Tpoint), O ≠ E → Bet A B C → Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC → Sum O E E' AB BC AC) :=
  ⟨(fun H O E E' A B C AB BC AC H0 H1 H2 H3 H4 => (let HH := H O E A H0; HH E' B C AB BC AC H1 H2 H3 H4)), (fun H O E A H0 E' B C AB BC AC H1 H2 H3 H4 => (let HH := H O E E' A B C AB BC AC H0 H1 H2 H3 H4; HH))⟩
theorem not_triangular_equality1_c :
    ∀ (O E A : Tpoint), O ≠ E → ¬ (∀ (E' B C AB BC AC : Tpoint), Bet A B C → Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC → Sum O E E' AB BC AC) := by
  intro b0 b1 b2 b3
  intro H0
  have HH := H0 b1 b2 b2 b0 b0 b0
  have H1 := between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b2 b2))))
  have H2 := length_id_2_c b0 b1 b1 b2 b3
  have HHH := HH H1 H2 H2 H2
  obtain ⟨H3, H4⟩ := HHH
  obtain ⟨X, H5⟩ := H4
  obtain ⟨Y, H6⟩ := H5
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, _⟩ := H9
  obtain ⟨H10, H11⟩ := H3
  obtain ⟨_, H12⟩ := H11
  obtain ⟨_, _⟩ := H12
  exact H10 ((by colr))
theorem triangular_equality_c :
    ∀ (O E E' A B C AB BC AC : Tpoint), O ≠ E → Bet A B C → Is_length O E E' A B AB → Is_length O E E' B C BC → Is_length O E E' A C AC → Sumg O E E' AB BC AC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  rcases b11 with H1 | H1
  · rcases b12 with H2 | H2
    · rcases b13 with H3 | H3
      · obtain ⟨_, H4⟩ := H3
        obtain ⟨H5, H6⟩ := H4
        obtain ⟨H7, H8⟩ := H6
        obtain ⟨_, H9⟩ := H2
        obtain ⟨H10, H11⟩ := H9
        obtain ⟨H12, H13⟩ := H11
        obtain ⟨_, H14⟩ := H1
        obtain ⟨H15, H16⟩ := H14
        obtain ⟨H17, H18⟩ := H16
        rcases H17 with H19 | H19
        · rcases H12 with H20 | H20
          · rcases H7 with H21 | H21
            · obtain ⟨X, H22⟩ := H19
              obtain ⟨H23, H24⟩ := H22
              obtain ⟨Y, H25⟩ := H20
              obtain ⟨H26, H27⟩ := H25
              obtain ⟨Z, H28⟩ := H21
              obtain ⟨H29, H30⟩ := H28
              have H31 := diff_sum_c b0 b1 b2 b0 X b6 H23
              have H32 := diff_sum_c b0 b1 b2 b0 Y b7 H26
              have H33 := diff_sum_c b0 b1 b2 b0 Z b8 H29
              have H34 := sum_uniqueness_c b0 X b6 X H31 ((by
  obtain ⟨H34, _⟩ := H31
  exact sum_O_B_c X ((by
  obtain ⟨_, H35⟩ := H34
  obtain ⟨_, H36⟩ := H35
  obtain ⟨H37, _⟩ := H36
  exact H37))))
              subst H34
              have H37 := sum_uniqueness_c b0 Y b7 Y H32 ((by
  obtain ⟨H37, _⟩ := H32
  exact sum_O_B_c Y ((by
  obtain ⟨_, H38⟩ := H37
  obtain ⟨_, H39⟩ := H38
  obtain ⟨H40, _⟩ := H39
  exact H40))))
              subst H37
              have H39 := sum_uniqueness_c b0 Z b8 Z H33 ((by
  obtain ⟨H39, _⟩ := H33
  exact sum_O_B_c Z ((by
  obtain ⟨_, H40⟩ := H39
  obtain ⟨_, H41⟩ := H40
  obtain ⟨H42, _⟩ := H41
  exact H42))))
              subst H39
              have H41 := sum_exists_c b0 b1 b2 ((by
  obtain ⟨H41, _⟩ := H31
  intro H42
  obtain ⟨H43, H44⟩ := H41
  obtain ⟨_, H45⟩ := H44
  obtain ⟨_, _⟩ := H45
  have H46 := H43 H42
  exact (H46).elim))
              have HS := H41 b6 b7 H15 H10
              obtain ⟨AC', H42⟩ := HS
              have H43 := l14_36_a_c b0 b1 b2 b6 b7 AC' H42 (l6_7_c b0 b6 b1 b7 H24 (l6_6 H27))
              have HH := l15_3_c b0 b1 b2 b6 b7 AC' H42
              have H44 := l2_11 H43 b10 H18 ((by cong_r))
              have HP := sum_pos_pos_c b0 b1 b2 b6 b7 AC' H24 H27 H42
              have H45 := l6_11_uniqueness_c b0 b3 b5 b1 b8 AC' H30 H8 HP H44
              subst H45
              exact Or.inl H42
            · subst H21
              have H23 := (by cong_r)
              have H24 := cong_identity b3 b5 b0 H23
              subst H24
              have H27 := between_identity b3 b4 b10
              subst H27
              have H30 := cong_identity b0 b6 b3 H18
              subst H30
              have H31 := cong_identity b0 b7 b3 H13
              subst H31
              obtain ⟨X, H33⟩ := H20
              obtain ⟨H34, H35⟩ := H33
              have H36 := diff_sum_c b0 b1 b2 b0 X b0 H34
              have H37 := sum_uniqueness_c b0 X X b0 (sum_O_B_c X ((let H37 := out_col H35; (by colr)))) H36
              subst H37
              obtain ⟨H39, H40⟩ := H35
              obtain ⟨_, H41⟩ := H40
              rcases H41 with _ | _
              · have H42 := (let H42 := rfl; H39 H42)
                exact (H42).elim
              · have H42 := (let H42 := rfl; H39 H42)
                exact (H42).elim
          · rcases H7 with H21 | H21
            · subst H20
              have H23 := (by cong_r)
              have H24 := cong_identity b4 b5 b0 H23
              subst H24
              have H26 := (by cong_r)
              obtain ⟨X, H27⟩ := H19
              obtain ⟨H28, H29⟩ := H27
              have H30 := diff_sum_c b0 b1 b2 b0 X b6 H28
              have H31 := sum_uniqueness_c b0 X X b6 (sum_O_B_c X ((let H31 := out_col H29; (by colr)))) H30
              subst H31
              obtain ⟨Y, H34⟩ := H21
              obtain ⟨H35, H36⟩ := H34
              have H37 := diff_sum_c b0 b1 b2 b0 Y b8 H35
              have H38 := sum_uniqueness_c b0 Y Y b8 (sum_O_B_c Y ((let H38 := out_col H36; (by colr)))) H37
              subst H38
              have H40 := l6_11_uniqueness_c b0 b3 b4 b1 b6 b8 H29 H18 H36 H8
              subst H40
              exact Or.inl (sum_A_O_c b8 ((let H43 := out_col H29; H5)))
            · subst H21
              subst H20
              have H24 := (by cong_r)
              have H25 := cong_identity b3 b5 b0 H24
              subst H25
              have H28 := (by cong_r)
              have H29 := cong_identity b4 b3 b0 H28
              subst H29
              have H31 := cong_identity b0 b6 b3 H18
              subst H31
              exact Or.inl (sum_O_O_c)
        · rcases H12 with H20 | H20
          · rcases H7 with H21 | H21
            · subst H19
              have H23 := (by cong_r)
              have H24 := cong_identity b3 b4 b0 H23
              subst H24
              have H26 := l6_11_uniqueness_c b0 b3 b5 b1 b7 b8 ((by
  obtain ⟨X, H26⟩ := H20
  obtain ⟨H27, H28⟩ := H26
  have H29 := diff_sum_c b0 b1 b2 b0 X b7 H27
  have H30 := sum_uniqueness_c b0 X X b7 (sum_O_B_c X ((let H30 := out_col H28; (by colr)))) H29
  subst H30
  exact H28)) H13 ((by
  obtain ⟨X, H26⟩ := H21
  obtain ⟨H27, H28⟩ := H26
  have H29 := diff_sum_c b0 b1 b2 b0 X b8 H27
  have H30 := sum_uniqueness_c b0 X X b8 (sum_O_B_c X ((let H30 := out_col H28; (by colr)))) H29
  subst H30
  exact H28)) H8
              subst H26
              exact Or.inl (sum_O_B_c b7 H5)
            · subst H21
              subst H19
              have H24 := (by cong_r)
              have H25 := cong_identity b3 b4 b0 H24
              subst H25
              have H28 := (by cong_r)
              have H29 := cong_identity b3 b5 b0 H28
              subst H29
              have H31 := cong_identity b0 b7 b3 H13
              subst H31
              exact Or.inl (sum_O_O_c)
          · rcases H7 with H21 | H21
            · subst H19
              subst H20
              have H24 := (by cong_r)
              have H25 := cong_identity b4 b5 b0 H24
              subst H25
              have H28 := (by cong_r)
              have H29 := cong_identity b3 b4 b0 H28
              subst H29
              have H31 := cong_identity b0 b8 b3 H8
              subst H31
              exact Or.inl (sum_O_O_c)
            · subst H21
              subst H20
              subst H19
              have H25 := (by cong_r)
              have H26 := cong_identity b3 b5 b0 H25
              subst H26
              have H28 := (by cong_r)
              have H29 := cong_identity b3 b4 b0 H28
              subst H29
              have HH := col_dec_c b0 b1 b2
              rcases HH with H30 | H30
              · exact Or.inr (⟨((fun H31 => (by
  obtain ⟨H32, H33⟩ := H31
  obtain ⟨_, H34⟩ := H33
  obtain ⟨_, _⟩ := H34
  exact ((H32 H30)).elim))), rfl⟩)
              · exact Or.inl (sum_O_O_c)
      · obtain ⟨H4, _⟩ := H3
        exact ((b9 H4)).elim
    · rcases b13 with _ | H3
      · obtain ⟨H3, _⟩ := H2
        exact ((b9 H3)).elim
      · obtain ⟨H4, _⟩ := H3
        obtain ⟨_, _⟩ := H2
        exact ((b9 H4)).elim
  · rcases b12 with _ | H2
    · rcases b13 with _ | H3
      · obtain ⟨H2, _⟩ := H1
        exact ((b9 H2)).elim
      · obtain ⟨H4, _⟩ := H3
        obtain ⟨_, _⟩ := H1
        exact ((b9 H4)).elim
    · rcases b13 with _ | H3
      · obtain ⟨H3, _⟩ := H2
        obtain ⟨_, _⟩ := H1
        exact ((b9 H3)).elim
      · obtain ⟨H4, _⟩ := H3
        obtain ⟨_, _⟩ := H2
        obtain ⟨_, _⟩ := H1
        exact ((b9 H4)).elim
theorem length_O_c :
    ∀ (O E E' : Tpoint), O ≠ E → Length O E E' O O O :=
  fun b0 b1 b2 b3 =>
  ⟨b3, (⟨((by colr)), (⟨(Or.inr rfl), ((by cong_r))⟩)⟩)⟩
theorem triangular_equality_bis_c :
    ∀ (O E E' A B C AB BC AC : Tpoint), A ≠ B ∨ A ≠ C ∨ B ≠ C → O ≠ E → Bet A B C → Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC → Sum O E E' AB BC AC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  obtain ⟨_, H4⟩ := b14
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  obtain ⟨_, H9⟩ := b13
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨_, H14⟩ := b12
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  rcases H17 with H19 | H19
  · rcases H12 with H20 | H20
    · rcases H7 with H21 | H21
      · obtain ⟨X, H3⟩ := H19
        obtain ⟨H22, H23⟩ := H3
        obtain ⟨Y, H24⟩ := H20
        obtain ⟨H25, H26⟩ := H24
        obtain ⟨Z, H27⟩ := H21
        obtain ⟨H28, H29⟩ := H27
        have H30 := diff_sum_c b0 b1 b2 b0 X b6 H22
        have H31 := diff_sum_c b0 b1 b2 b0 Y b7 H25
        have H32 := diff_sum_c b0 b1 b2 b0 Z b8 H28
        have H33 := sum_uniqueness_c b0 X b6 X H30 ((by
  obtain ⟨H33, _⟩ := H30
  exact sum_O_B_c X ((by
  obtain ⟨_, H34⟩ := H33
  obtain ⟨_, H35⟩ := H34
  obtain ⟨H36, _⟩ := H35
  rcases b9 with _ | H37
  · exact H36
  · rcases H37 with _ | _
    · exact H36
    · exact H36))))
        subst H33
        have H36 := sum_uniqueness_c b0 Y b7 Y H31 ((by
  obtain ⟨H36, _⟩ := H31
  exact sum_O_B_c Y ((by
  obtain ⟨_, H37⟩ := H36
  obtain ⟨_, H38⟩ := H37
  obtain ⟨H39, _⟩ := H38
  rcases b9 with _ | H40
  · exact H39
  · rcases H40 with _ | _
    · exact H39
    · exact H39))))
        subst H36
        have H38 := sum_uniqueness_c b0 Z b8 Z H32 ((by
  obtain ⟨H38, _⟩ := H32
  exact sum_O_B_c Z ((by
  obtain ⟨_, H39⟩ := H38
  obtain ⟨_, H40⟩ := H39
  obtain ⟨H41, _⟩ := H40
  rcases b9 with _ | H42
  · exact H41
  · rcases H42 with _ | _
    · exact H41
    · exact H41))))
        subst H38
        have H40 := sum_exists_c b0 b1 b2 ((by
  obtain ⟨H40, _⟩ := H30
  intro H41
  obtain ⟨H42, H43⟩ := H40
  obtain ⟨_, H44⟩ := H43
  obtain ⟨_, _⟩ := H44
  rcases b9 with _ | H45
  · have H45 := H42 H41
    exact (H45).elim
  · rcases H45 with _ | _
    · have H46 := H42 H41
      exact (H46).elim
    · have H46 := H42 H41
      exact (H46).elim))
        have HS := H40 b6 b7 H15 H10
        obtain ⟨AC', H41⟩ := HS
        have H42 := l14_36_a_c b0 b1 b2 b6 b7 AC' H41 (l6_7_c b0 b6 b1 b7 H23 (l6_6 H26))
        have HH := l15_3_c b0 b1 b2 b6 b7 AC' H41
        have H43 := l2_11 H42 b11 H18 ((by cong_r))
        have HP := sum_pos_pos_c b0 b1 b2 b6 b7 AC' H23 H26 H41
        have H44 := l6_11_uniqueness_c b0 b3 b5 b1 b8 AC' H29 H8 HP H43
        subst H44
        exact H41
      · subst H21
        have H23 := (by cong_r)
        have H24 := cong_identity b3 b5 b0 H23
        subst H24
        have H26 := between_identity b3 b4 b11
        subst H26
        have H29 := cong_identity b0 b6 b3 H18
        subst H29
        have H30 := cong_identity b0 b7 b3 H13
        subst H30
        obtain ⟨X, H32⟩ := H20
        obtain ⟨H33, H34⟩ := H32
        have H35 := diff_sum_c b0 b1 b2 b0 X b0 H33
        have H36 := sum_uniqueness_c b0 X X b0 (sum_O_B_c X ((let H36 := out_col H34; (by colr)))) H35
        subst H36
        obtain ⟨H38, H39⟩ := H34
        obtain ⟨_, H40⟩ := H39
        rcases b9 with H41 | H41
        · rcases H40 with _ | _
          · have H42 := (let H42 := rfl; H38 H42)
            have H44 := (let H44 := rfl; H41 H44)
            exact (H42).elim
          · have H42 := (let H42 := rfl; H38 H42)
            have H44 := (let H44 := rfl; H41 H44)
            exact (H42).elim
        · rcases H40 with _ | _
          · rcases H41 with H42 | H42
            · have H43 := (let H43 := rfl; H38 H43)
              have H45 := (let H45 := rfl; H42 H45)
              exact (H43).elim
            · have H43 := (let H43 := rfl; H38 H43)
              have H45 := (let H45 := rfl; H42 H45)
              exact (H43).elim
          · rcases H41 with H42 | H42
            · have H43 := (let H43 := rfl; H38 H43)
              have H45 := (let H45 := rfl; H42 H45)
              exact (H43).elim
            · have H43 := (let H43 := rfl; H38 H43)
              have H45 := (let H45 := rfl; H42 H45)
              exact (H43).elim
    · rcases H7 with H21 | H21
      · subst H20
        have H23 := (by cong_r)
        have H24 := cong_identity b4 b5 b0 H23
        subst H24
        have H26 := (by cong_r)
        obtain ⟨X, H3⟩ := H19
        obtain ⟨H27, H28⟩ := H3
        have H29 := diff_sum_c b0 b1 b2 b0 X b6 H27
        have H30 := sum_uniqueness_c b0 X X b6 (sum_O_B_c X ((let H30 := out_col H28; (by colr)))) H29
        subst H30
        obtain ⟨Y, H33⟩ := H21
        obtain ⟨H34, H35⟩ := H33
        have H36 := diff_sum_c b0 b1 b2 b0 Y b8 H34
        have H37 := sum_uniqueness_c b0 Y Y b8 (sum_O_B_c Y ((let H37 := out_col H35; (by colr)))) H36
        subst H37
        have H39 := l6_11_uniqueness_c b0 b3 b4 b1 b6 b8 H28 H18 H35 H8
        subst H39
        exact sum_A_O_c b8 ((let H42 := out_col H28; H5))
      · subst H21
        subst H20
        have H24 := (by cong_r)
        have H25 := cong_identity b3 b5 b0 H24
        subst H25
        have H27 := (by cong_r)
        have H28 := cong_identity b4 b3 b0 H27
        subst H28
        have H30 := cong_identity b0 b6 b3 H18
        subst H30
        exact sum_O_O_c
  · rcases H12 with H20 | H20
    · rcases H7 with H21 | H21
      · subst H19
        have H23 := (by cong_r)
        have H24 := cong_identity b3 b4 b0 H23
        subst H24
        have H26 := l6_11_uniqueness_c b0 b3 b5 b1 b7 b8 ((by
  obtain ⟨X, H3⟩ := H20
  obtain ⟨H26, H27⟩ := H3
  have H28 := diff_sum_c b0 b1 b2 b0 X b7 H26
  have H29 := sum_uniqueness_c b0 X X b7 (sum_O_B_c X ((let H29 := out_col H27; (by colr)))) H28
  subst H29
  exact H27)) H13 ((by
  obtain ⟨X, H3⟩ := H21
  obtain ⟨H26, H27⟩ := H3
  have H28 := diff_sum_c b0 b1 b2 b0 X b8 H26
  have H29 := sum_uniqueness_c b0 X X b8 (sum_O_B_c X ((let H29 := out_col H27; (by colr)))) H28
  subst H29
  exact H27)) H8
        subst H26
        exact sum_O_B_c b7 H5
      · subst H21
        subst H19
        have H24 := (by cong_r)
        have H25 := cong_identity b3 b4 b0 H24
        subst H25
        have H27 := (by cong_r)
        have H28 := cong_identity b3 b5 b0 H27
        subst H28
        have H30 := cong_identity b0 b7 b3 H13
        subst H30
        exact sum_O_O_c
    · rcases H7 with H21 | H21
      · subst H19
        subst H20
        have H24 := (by cong_r)
        have H25 := cong_identity b4 b5 b0 H24
        subst H25
        have H27 := (by cong_r)
        have H28 := cong_identity b3 b4 b0 H27
        subst H28
        have H30 := cong_identity b0 b8 b3 H8
        subst H30
        exact sum_O_O_c
      · subst H19
        subst H21
        subst H20
        have H25 := (by cong_r)
        have H26 := cong_identity b3 b4 b0 H25
        subst H26
        have H28 := (by cong_r)
        have H29 := cong_identity b3 b5 b0 H28
        subst H29
        have H31 := cong_identity b0 b0 b3 H8
        rcases b9 with H32 | H32
        · have H33 := (let H33 := rfl; H32 H33)
          exact (H33).elim
        · rcases H32 with H33 | H33
          · have H34 := (let H34 := rfl; H33 H34)
            exact (H34).elim
          · have H34 := (let H34 := rfl; H33 H34)
            exact (H34).elim
theorem length_out_c :
    ∀ (O E E' A B C D AB CD : Tpoint), A ≠ B → C ≠ D → Length O E E' A B AB → Length O E E' C D CD → Out O AB CD := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  obtain ⟨_, H3⟩ := b12
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨_, H8⟩ := b11
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨H11, H12⟩ := H10
  rcases H11 with H13 | H13
  · rcases H6 with H14 | H14
    · obtain ⟨X, H15⟩ := H13
      obtain ⟨H16, H17⟩ := H15
      obtain ⟨Y, H18⟩ := H14
      obtain ⟨H19, H20⟩ := H18
      have H21 := diff_sum_c b0 b1 b2 b0 X b7 H16
      have H22 := diff_sum_c b0 b1 b2 b0 Y b8 H19
      have H23 := sum_uniqueness_c b0 X X b7 (sum_O_B_c X ((let H23 := out_col H17; (by colr)))) H21
      subst H23
      have H25 := sum_uniqueness_c b0 Y Y b8 (sum_O_B_c Y ((let H25 := out_col H20; (by colr)))) H22
      subst H25
      exact l6_7_c b0 b7 b1 b8 H17 (l6_6 H20)
    · subst H14
      have H16 := (by cong_r)
      have H17 := cong_identity b5 b6 b0 H16
      exact ((b10 H17)).elim
  · rcases H6 with _ | H14
    · subst H13
      have H15 := (by cong_r)
      have H16 := cong_identity b3 b4 b0 H15
      exact ((b9 H16)).elim
    · subst H14
      have H16 := (by cong_r)
      have H17 := cong_identity b5 b6 b0 H16
      exact ((b10 H17)).elim
theorem image_preserves_bet1_c :
    ∀ (X Y A B C A' B' C' : Tpoint), Bet A B C → Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Bet A' B' C' := sorry

theorem image_preserves_col_c :
    ∀ (X Y A B C A' B' C' : Tpoint), Col A B C → Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Col A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  rcases b8 with H3 | H3
  · exact Or.inl (image_preserves_bet1_c b0 b1 b2 b3 b4 b5 b6 b7 H3 b9 b10 b11)
  · rcases H3 with H4 | H4
    · exact Or.inr (Or.inl (image_preserves_bet1_c b0 b1 b3 b4 b2 b6 b7 b5 H4 b10 b11 b9))
    · exact Or.inr (Or.inr (image_preserves_bet1_c b0 b1 b4 b2 b3 b7 b5 b6 H4 b11 b9 b10))
theorem image_preserves_out_c :
    ∀ (X Y A B C A' B' C' : Tpoint), Out A B C → Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Out A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨H3, H4⟩ := b8
  obtain ⟨H5, H6⟩ := H4
  exact ⟨((fun H7 => (by
  subst H7
  have H9 := l10_2_uniqueness_c b0 b1 b5 b3 b2 b10 b9
  exact ((H3 H9)).elim))), (⟨((fun H7 => (by
  subst H7
  have H9 := l10_2_uniqueness_c b0 b1 b5 b4 b2 b11 b9
  exact ((H5 H9)).elim))), ((by
  rcases H6 with H7 | H7
  · exact Or.inl (image_preserves_bet1_c b0 b1 b2 b3 b4 b5 b6 b7 H7 b9 b10 b11)
  · exact Or.inr (image_preserves_bet1_c b0 b1 b2 b4 b3 b5 b7 b6 H7 b9 b11 b10)))⟩)⟩
theorem project_preserves_out_c :
    ∀ (A B C A' B' C' P Q X Y : Tpoint), Out A B C → ¬ Par A B X Y → Proj A A' P Q X Y → Proj B B' P Q X Y → Proj C C' P Q X Y → Out A' B' C' := sorry

theorem conga_bet_conga_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), CongA A B C D E F → A' ≠ B → C' ≠ B → D' ≠ E → F' ≠ E → Bet A B A' → Bet C B C' → Bet D E D' → Bet F E F' → CongA A' B C' D' E F' :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 =>
  (let HH := l11_13_c b5 b6 b8 b10 b15 b11 b17 b13; conga_comm_c b7 b1 b6 b9 b4 b8 (l11_13_c b8 b7 b9 (conga_comm_c b6 b1 b2 b8 b4 b5 HH) b16 b12 b18 b14))
theorem thales_c :
    ∀ (O E E' P A B C D A1 B1 C1 D1 AD : Tpoint), O ≠ E → Col P A B → Col P C D → ¬ Col P A C → Pj A C B D → Length O E E' P A A1 → Length O E E' P B B1 → Length O E E' P C C1 → Length O E E' P D D1 → Prodg O E E' A1 D1 AD → Prodg O E E' C1 B1 AD := sorry

theorem length_existence_c :
    ∀ (O E E' A B : Tpoint), ¬ Col O E E' → ∃ (AB : Tpoint), Length O E E' A B AB := by
  intro b0 b1 b2 b3 b4 b5
  have NEO := (fun H0 => (by
  subst H0
  exact b5 ((by colr))))
  have HH := segment_construction_2_c b1 b0 b3 b4 NEO
  obtain ⟨AB, H0⟩ := HH
  obtain ⟨H1, H2⟩ := H0
  exact ⟨AB, (((let H3 := (let o := point_equality_decidability AB b0; (by
  rcases o with H3 | H3
  · exact Or.inl H3
  · exact Or.inr (⟨NEO, (⟨H3, H1⟩)⟩))); (let H4 := (by
  rcases H3 with H4 | H4
  · subst H4
    exact (by colr)
  · exact out_col H4); ⟨(Ne.symm NEO), (⟨H4, (⟨((by
  rcases H3 with H5 | H5
  · exact Or.inr (Eq.symm H5)
  · exact Or.inl (⟨AB, (⟨(diff_A_O_c b0 b1 b2 AB b5 H4), (⟨((fun H6 => (by
  obtain ⟨_, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  rcases H1 with _ | _
  · rcases H9 with _ | _
    · have H10 := H8 H6
      exact (H10).elim
    · have H10 := H8 H6
      exact (H10).elim
  · rcases H9 with _ | _
    · have H10 := H8 H6
      exact (H10).elim
    · have H10 := H8 H6
      exact (H10).elim))), (⟨NEO, ((by
  rcases H1 with H6 | H6
  · exact Or.inr H6
  · exact Or.inl H6))⟩)⟩)⟩)⟩))), H2⟩)⟩)⟩))))⟩
theorem l15_7_c :
    ∀ (O E E' A B C H AB AC AH AC2 : Tpoint), O ≠ E → Per A C B → Perp_at H C H A B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' A H AH → (Prod O E E' AC AC AC2 ↔ Prod O E E' AB AH AC2) := sorry

theorem l15_7_1_c :
    ∀ (O E E' A B C H AB AC AH AC2 : Tpoint), O ≠ E → Per A C B → Perp_at H C H A B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' A H AH → Prod O E E' AC AC AC2 → Prod O E E' AB AH AC2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17
  have i := l15_7_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  obtain ⟨x, x0⟩ := i
  exact x b17
theorem l15_7_2_c :
    ∀ (O E E' A B C H AB AC AH AC2 : Tpoint), O ≠ E → Per A C B → Perp_at H C H A B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' A H AH → Prod O E E' AB AH AC2 → Prod O E E' AC AC AC2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17
  have i := l15_7_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  obtain ⟨x, x0⟩ := i
  exact x0 b17
theorem length_sym_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → Length O E E' B A AB := by
  intro b0 b1 b2 b3 b4 b5 b6
  obtain ⟨H0, H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  exact ⟨H0, (⟨H2, (⟨H4, ((by cong_r))⟩)⟩)⟩
theorem pythagoras_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 : Tpoint), O ≠ E → Per A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 AB2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
  have H7 := (by
  obtain ⟨H7, _⟩ := b19
  obtain ⟨H8, _⟩ := b18
  obtain ⟨H9, _⟩ := b17
  exact ⟨((fun H10 => (by
  obtain ⟨H11, H12⟩ := H9
  obtain ⟨H13, H14⟩ := H8
  obtain ⟨H15, H16⟩ := H7
  obtain ⟨_, H17⟩ := H12
  obtain ⟨_, H18⟩ := H14
  obtain ⟨_, H19⟩ := H16
  obtain ⟨_, _⟩ := H17
  obtain ⟨_, _⟩ := H18
  obtain ⟨_, _⟩ := H19
  have H20 := H11 H10
  have H21 := H13 H10
  have H22 := H15 H10
  exact (H20).elim))), (⟨((by
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H8
  obtain ⟨_, H13⟩ := H7
  obtain ⟨_, H14⟩ := H11
  obtain ⟨_, H15⟩ := H12
  obtain ⟨_, H16⟩ := H13
  obtain ⟨_, _⟩ := H14
  obtain ⟨_, _⟩ := H15
  obtain ⟨_, H19⟩ := H16
  exact H19)), (⟨((by
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H8
  obtain ⟨_, H13⟩ := H7
  obtain ⟨_, H14⟩ := H11
  obtain ⟨_, H15⟩ := H12
  obtain ⟨_, H16⟩ := H13
  obtain ⟨_, H17⟩ := H14
  obtain ⟨_, _⟩ := H15
  obtain ⟨_, _⟩ := H16
  exact H17)), ((by
  obtain ⟨_, H11⟩ := H9
  obtain ⟨_, H12⟩ := H8
  obtain ⟨_, H13⟩ := H7
  obtain ⟨_, H14⟩ := H11
  obtain ⟨_, H15⟩ := H12
  obtain ⟨_, H16⟩ := H13
  obtain ⟨_, _⟩ := H14
  obtain ⟨H17, _⟩ := H15
  obtain ⟨_, _⟩ := H16
  exact H17))⟩)⟩)⟩)
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨H12, H13⟩ := H11
  have o := col_dec_c b3 b5 b4
  rcases o with H14 | H14
  · have HH := l8_9_c b3 b5 b4 b13 H14
    rcases HH with H15 | H15
    · subst H15
      have H18 := length_uniqueness_c b0 b1 b2 b3 b4 b8 b7 b14 (length_sym_c b0 b1 b2 b4 b3 b7 b16)
      subst H18
      have H20 := prod_uniqueness_c b8 b8 b11 b10 b19 b18
      subst H20
      have H21 := length_uniqueness_c b0 b1 b2 b3 b3 b6 b0 b15 (length_id_2_c b0 b1 b2 b3 b12)
      subst H21
      have H23 := prod_uniqueness_c b0 b0 b9 b0 b17 (prod_0_l_c b0 b1 b2 b0 H8 ((by colr)))
      subst H23
      exact sum_O_B_c b11 H10
    · subst H15
      have H18 := length_uniqueness_c b0 b1 b2 b3 b4 b8 b6 b14 b15
      subst H18
      have H20 := prod_uniqueness_c b8 b8 b11 b9 b19 b17
      subst H20
      have H22 := length_uniqueness_c b0 b1 b2 b4 b4 b7 b0 b16 (length_id_2_c b0 b1 b2 b4 b12)
      subst H22
      have H25 := prod_uniqueness_c b0 b0 b10 b0 b18 (prod_0_l_c b0 b1 b2 b0 H8 H13)
      subst H25
      exact sum_A_O_c b11 H12
  · have H15 := l8_18_existence_c b3 b4 b5 (not_col_permutation_5_c b3 b5 b4 H14)
    obtain ⟨P, H16⟩ := H15
    obtain ⟨H17, H18⟩ := H16
    have H19 := l8_14_2_1b_bis_c b3 b4 b5 P P H18 ((by colr)) ((by colr))
    have H20 := l11_47_c b3 b4 b5 P b13 (perp_in_left_comm_c P b5 b3 b4 P (perp_in_left_comm_c b5 P b3 b4 P (perp_in_sym_c b3 b4 b5 P P H19)))
    obtain ⟨H21, H22⟩ := H20
    obtain ⟨_, H23⟩ := H22
    have HL1 := length_existence_c b0 b1 b2 b3 P H8
    have HL2 := length_existence_c b0 b1 b2 b4 P H8
    obtain ⟨AP, H24⟩ := HL1
    obtain ⟨BP, H25⟩ := HL2
    have H26 := triangular_equality_bis_c b0 b1 b2 b3 P b4 AP BP b8 (Or.inr (Or.inr (Ne.symm H23))) b12 H21 H24 (length_sym_c b0 b1 b2 b4 P BP H25) b14
    have H27 := l15_7_1_c b0 b1 b2 b3 b4 b5 P b8 b6 AP b9 b12 b13 (perp_in_left_comm_c P b5 b3 b4 P (perp_in_left_comm_c b5 P b3 b4 P (perp_in_sym_c b3 b4 b5 P P H19))) b14 b15 H24 b17
    have H28 := l15_7_1_c b0 b1 b2 b4 b3 b5 P b8 b7 BP b10 b12 (l8_2_c b3 b5 b4 b13) (perp_in_left_comm_c P b5 b4 b3 P (perp_in_left_comm_c b5 P b4 b3 P (perp_in_sym_c b4 b3 b5 P P (perp_in_left_comm_c b3 b4 b5 P P H19)))) (length_sym_c b0 b1 b2 b3 b4 b8 b14) b16 H25 b18
    have HD := distr_l_c b1 b2 b8 AP BP b8 b9 b10 b11 H26 H27 H28 b19
    exact HD
theorem is_length_exists_c :
    ∀ (O E E' X Y : Tpoint), ¬ Col O E E' → ∃ (XY : Tpoint), Is_length O E E' X Y XY := by
  intro b0 b1 b2 b3 b4 b5
  rcases (point_equality_decidability b3 b4) with HXY | _
  · subst HXY
    exact ⟨b0, (Or.inl (length_id_2_c b0 b1 b2 b3 ((let H := not_col_distincts_c b0 b1 b2 b5; (let H0 := H; (by
  obtain ⟨_, H1⟩ := H0
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨_, _⟩ := H3
  exact H2))))))⟩
  · have e := length_existence_c b0 b1 b2 b3 b4 b5
    obtain ⟨x, x0⟩ := e
    exact ⟨x, (Or.inl x0)⟩
theorem lt_to_ltp_c :
    ∀ (O E E' A B L C D M : Tpoint), Length O E E' A B L → Length O E E' C D M → Lt A B C D → LtP O E E' L M := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have o := point_equality_decidability b5 b8
  rcases o with H2 | H2
  · subst H2
    have H4 := length_cong_c b0 b1 b2 b6 b7 b5 b10
    have H5 := length_cong_c b0 b1 b2 b3 b4 b5 b9
    obtain ⟨_, H6⟩ := b11
    exact ((H6 ((let H7 := tarski_to_cong_theory.Tarski_is_a_Cong_theory; ((let H8 := (((b7 , BinNums.xO (BinNums.xI BinNums.xH)))) % list; (let H9 := CongR.interp H8 b7; fun H10 H11 => (let H12 := CongR.collect_congs b6 b7 b0 b5 H11 (BinNums.xI (BinNums.xO BinNums.xH)) (BinNums.xO (BinNums.xI BinNums.xH)) BinNums.xH (BinNums.xO (BinNums.xO BinNums.xH)) (sets.SSP.add (sets.SP.add (BinNums.xO BinNums.xH , BinNums.xI BinNums.xH) (sets.SP.add (BinNums.xH , BinNums.xO (BinNums.xO BinNums.xH)) sets.SP.empty)) sets.SSP.empty) H9 rfl rfl rfl rfl (CongR.collect_congs b3 b4 b0 b5 H10 (BinNums.xO BinNums.xH) (BinNums.xI BinNums.xH) BinNums.xH (BinNums.xO (BinNums.xO BinNums.xH)) sets.SSP.empty H9 rfl rfl rfl rfl (CongR.ss_ok_empty H9)); CongR.test_cong_ok (sets.SSP.add (sets.SP.add (BinNums.xI (BinNums.xO BinNums.xH) , BinNums.xO (BinNums.xI BinNums.xH)) (sets.SP.add (BinNums.xH , BinNums.xO (BinNums.xO BinNums.xH)) sets.SP.empty)) (sets.SSP.add (sets.SP.add (BinNums.xO BinNums.xH , BinNums.xI BinNums.xH) (sets.SP.add (BinNums.xH , BinNums.xO (BinNums.xO BinNums.xH)) sets.SP.empty)) sets.SSP.empty)) H9 (BinNums.xO BinNums.xH) (BinNums.xI BinNums.xH) (BinNums.xI (BinNums.xO BinNums.xH)) (BinNums.xO (BinNums.xI BinNums.xH)) H12 (rfl))))) H5 H4)))).elim
  · have H3 := lt__le_c b3 b4 b6 b7 b11
    have HH := length_leP_le_2_c b0 b1 b2 b3 b4 b6 b7 b5 b8 b9 b10 H3
    rcases HH with H4 | H4
    · exact H4
    · exact ((H2 H4)).elim
theorem ltp_to_lep_c :
    ∀ (O E E' L M : Tpoint), LtP O E E' L M → LeP O E E' L M :=
  fun b0 b1 b2 b3 b4 b5 =>
  Or.inl b5
theorem ltp_to_lt_c :
    ∀ (O E E' A B L C D M : Tpoint), Length O E E' A B L → Length O E E' C D M → LtP O E E' L M → Lt A B C D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have H2 := ltp_to_lep_c b0 b1 b2 b5 b8 b11
  exact ⟨(length_leP_le_1_c b0 b1 b2 b3 b4 b6 b7 b5 b8 b9 b10 H2), ((fun H3 => (let HH := length_eq_cong_2_c b0 b1 b2 b3 b4 b6 b7 b5 b9 H3; (let H4 := length_uniqueness_c b0 b1 b2 b6 b7 b5 b8 HH b10; (by
  subst H4
  obtain ⟨P, H6⟩ := b11
  obtain ⟨H7, H8⟩ := H6
  have H9 := (by
  obtain ⟨X, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H11, _⟩ := H10
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨_, _⟩ := H15
  exact ⟨((fun H16 => (let H17 := H12 H16; (H17).elim))), H14⟩)
  obtain ⟨H10, H11⟩ := H9
  have HP := diff_null_c b0 b1 b2 b5 H10 H11
  have H12 := diff_uniqueness_c b0 b1 b2 b5 b5 P b0 H7 HP
  subst H12
  obtain ⟨H14, H15⟩ := H8
  obtain ⟨_, H16⟩ := H15
  rcases H16 with _ | _
  · have H17 := (let H17 := rfl; H14 H17)
    exact (H17).elim
  · have H17 := (let H17 := rfl; H14 H17)
    exact (H17).elim)))))⟩
theorem prod_col_c :
    ∀ (O E E' A B AB : Tpoint), Ar2 O E E' A B A → Prod O E E' A B AB → Col O E AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H0, _⟩ := b7
  obtain ⟨_, H3⟩ := H0
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5
theorem square_increase_strict_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ar2 O E E' A B A → Ps O E A → Ps O E B → LtP O E E' A B → Prod O E E' A A A2 → Prod O E E' B B B2 → LtP O E E' A2 B2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  have HA2 := prod_col_c b0 b1 b2 b3 b3 b5 ((by
  obtain ⟨H5, H6⟩ := b7
  obtain ⟨_, H7⟩ := H6
  obtain ⟨_, H8⟩ := H7
  exact ⟨((fun H9 => (let H10 := H5 H9; (H10).elim))), (⟨H8, (⟨H8, H8⟩)⟩)⟩)) b11
  have HB2 := prod_col_c b0 b1 b2 b4 b4 b6 ((by
  obtain ⟨H5, H6⟩ := b7
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, _⟩ := H7
  exact ⟨((fun H9 => (let H10 := H5 H9; (H10).elim))), (⟨H8, (⟨H8, H8⟩)⟩)⟩)) b12
  obtain ⟨H5, H6⟩ := b7
  obtain ⟨_, H7⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  have HD := diff_exists_c b0 b1 b2 b4 b3 H5 H8 H9
  obtain ⟨BmA, H10⟩ := HD
  have HS := sum_exists_c b4 b3 H8 H9
  obtain ⟨BpA, H11⟩ := HS
  have HD0 := diff_exists_c b0 b1 b2 b6 b5 H5 HB2 HA2
  obtain ⟨B2mA2, H12⟩ := HD0
  have H13 := (let H13 := sum_ar2_c b0 b1 b2 b4 b3 BpA H11; (by
  obtain ⟨_, H14⟩ := H13
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  exact H16))
  have H14 := (let H14 := diff_ar2_c b0 b1 b2 b4 b3 BmA H10; (by
  obtain ⟨_, H15⟩ := H14
  obtain ⟨_, H16⟩ := H15
  obtain ⟨_, H17⟩ := H16
  exact H17))
  have H15 := (let H15 := diff_ar2_c b0 b1 b2 b6 b5 B2mA2 H12; (by
  obtain ⟨_, H16⟩ := H15
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, H18⟩ := H17
  exact H18))
  have HP := prod_exists_c BpA BmA H13 H14
  obtain ⟨F, H16⟩ := HP
  have HC := diff_of_squares_c b0 b1 b2 b4 b3 b6 b5 B2mA2 BpA BmA F b12 b11 H12 H11 H10 H16
  subst HC
  exact ⟨B2mA2, (⟨H12, (prod_pos_pos_c b0 b1 b2 BpA BmA B2mA2 (sum_pos_pos_c b0 b1 b2 b4 b3 BpA b9 b8 H11) (lt_diff_ps_c b0 b1 b2 b4 b3 BmA H8 H9 b10 H10) H16)⟩)⟩
theorem square_increase_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ar2 O E E' A B A → Ps O E A → Ps O E B → LeP O E E' A B → Prod O E E' A A A2 → Prod O E E' B B B2 → LeP O E E' A2 B2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  rcases b10 with H5 | H5
  · have H6 := square_increase_strict_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 H5 b11 b12
    have H7 := ltp_to_lep_c b0 b1 b2 b5 b6 H6
    exact H7
  · subst H5
    have H7 := prod_uniqueness_c b3 b3 b5 b6 b11 b12
    subst H7
    exact Or.inr rfl
theorem signeq__prod_pos_c :
    ∀ (O E E' A B C : Tpoint), SignEq O E A B → Prod O E E' A B C → Ps O E C := sorry

theorem pos_neg__prod_neg_c :
    ∀ (O E E' A B C : Tpoint), Ps O E A → Ng O E B → Prod O E E' A B C → Ng O E C := sorry

theorem sign_dec_c :
    ∀ (O E A : Tpoint), Col O E A → O ≠ E → A = O ∨ Ps O E A ∨ Ng O E A := by
  intro b0 b1 b2 b3 b4
  have o := point_equality_decidability b2 b0
  rcases o with H1 | H1
  · exact Or.inl H1
  · have HH := third_point_c b0 b1 b2 b3
    rcases HH with H2 | H2
    · exact Or.inr (Or.inr (⟨H1, (⟨(Ne.symm b4), H2⟩)⟩))
    · exact Or.inr (Or.inl ((⟨H1, (⟨(Ne.symm b4), H2⟩)⟩)))
theorem not_signEq_prod_neg_c :
    ∀ (O E E' A B C : Tpoint), A ≠ O → B ≠ O → ¬ SignEq O E A B → Prod O E E' A B C → Ng O E C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HP := b9
  obtain ⟨H3, _⟩ := HP
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  have H10 := (fun H10 => (by
  subst H10
  exact b8 (((H4 ((by colr)))).elim)))
  have HA := sign_dec_c b0 b1 b3 H6 H10
  have HB := sign_dec_c b0 b1 b4 H8 H10
  rcases HA with H11 | H11
  · rcases HB with H12 | _
    · exact ((b7 H12)).elim
    · exact ((b6 H11)).elim
  · rcases HB with H12 | H12
    · exact ((b7 H12)).elim
    · rcases H11 with H13 | H13
      · rcases H12 with H14 | H14
        · exact ((b8 (Or.inl (⟨H13, H14⟩)))).elim
        · exact pos_neg__prod_neg_c b0 b1 b2 b3 b4 b5 H13 H14 b9
      · rcases H12 with H14 | H14
        · have H15 := prod_comm_c b0 b1 b2 b3 b4 b5 b9
          exact pos_neg__prod_neg_c b0 b1 b2 b4 b3 b5 H14 H13 H15
        · exact ((b8 (Or.inr (⟨H13, H14⟩)))).elim
theorem prod_pos__signeq_c :
    ∀ (O E E' A B C : Tpoint), A ≠ O → B ≠ O → Prod O E E' A B C → Ps O E C → SignEq O E A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HP := b8
  obtain ⟨H3, _⟩ := HP
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  have HA := sign_dec_c b0 b1 b3 H6
  have HB := sign_dec_c b0 b1 b4 H8
  have H10 := (fun H10 => (by
  subst H10
  exact H4 ((by colr))))
  have o := HA H10
  rcases o with H11 | H11
  · exact ((b6 H11)).elim
  · have o0 := HB H10
    rcases o0 with H12 | H12
    · exact ((b7 H12)).elim
    · rcases H11 with H13 | H13
      · rcases H12 with H14 | H14
        · exact Or.inl (⟨H13, H14⟩)
        · have H15 := pos_neg__prod_neg_c b0 b1 b2 b3 b4 b5 H13 H14 b8
          have H16 := pos_not_neg_c b0 b1 b5 b9
          exact ((H16 H15)).elim
      · rcases H12 with H14 | H14
        · have H15 := prod_comm_c b0 b1 b2 b3 b4 b5 b8
          have H16 := pos_neg__prod_neg_c b0 b1 b2 b4 b3 b5 H14 H13 H15
          have H17 := pos_not_neg_c b0 b1 b5 b9
          exact ((H17 H16)).elim
        · exact Or.inr (⟨H13, H14⟩)
theorem prod_ng___not_signeq_c :
    ∀ (O E E' A B C : Tpoint), A ≠ O → B ≠ O → Prod O E E' A B C → Ng O E C → ¬ SignEq O E A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HP := b8
  obtain ⟨H3, _⟩ := HP
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  have HA := sign_dec_c b0 b1 b3 H6
  have HB := sign_dec_c b0 b1 b4 H8
  have H10 := (fun H10 => (by
  subst H10
  exact H4 ((by colr))))
  have o := HA H10
  rcases o with H11 | H11
  · intro _
    exact b6 H11
  · have o0 := HB H10
    rcases o0 with H12 | H12
    · intro _
      exact b7 H12
    · rcases H11 with H13 | H13
      · rcases H12 with H14 | H14
        · exact (((let H15 := signeq__prod_pos_c b0 b1 b2 b3 b4 b5 (Or.inl (⟨H13, H14⟩)) b8; (let H16 := pos_not_neg_c b0 b1 b5 H15; ((H16 b9)).elim)))).elim
        · intro H15
          rcases H15 with H16 | H16
          · obtain ⟨_, H17⟩ := H16
            have H18 := pos_not_neg_c b0 b1 b4 H17
            exact ((H18 H14)).elim
          · obtain ⟨H17, _⟩ := H16
            have H18 := pos_not_neg_c b0 b1 b3 H13
            exact ((H18 H17)).elim
      · rcases H12 with H14 | H14
        · intro H15
          rcases H15 with H16 | H16
          · obtain ⟨H17, _⟩ := H16
            have H18 := pos_not_neg_c b1 b3 H17 H13
            exact H18
          · obtain ⟨_, H17⟩ := H16
            have H18 := pos_not_neg_c b0 b1 b4 H14
            exact ((H18 H17)).elim
        · have H15 := signeq__prod_pos_c b0 b1 b2 b3 b4 b5 (Or.inr (⟨H13, H14⟩)) b8
          have H16 := pos_not_neg_c b0 b1 b5 H15
          intro _
          exact H16 b9
theorem ltp__diff_pos_c :
    ∀ (O E E' A B D : Tpoint), LtP O E E' A B → Diff O E E' B A D → Ps O E D := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨D', H1⟩ := b6
  obtain ⟨H2, H3⟩ := H1
  have H4 := diff_uniqueness_c b0 b1 b2 b4 b3 b5 D' b7 H2
  subst H4
  exact H3
theorem diff_pos__ltp_c :
    ∀ (O E E' A B D : Tpoint), Diff O E E' B A D → Ps O E D → LtP O E E' A B :=
  fun b0 b1 b2 b3 b4 b5 b6 b7 =>
  ⟨b5, (⟨b6, b7⟩)⟩
theorem square_increase_rev_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ps O E A → Ps O E B → LtP O E E' A2 B2 → Prod O E E' A A A2 → Prod O E E' B B B2 → LtP O E E' A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have HP2 := b10
  have HP3 := b11
  obtain ⟨H4, _⟩ := HP3
  obtain ⟨H6, _⟩ := HP2
  obtain ⟨_, H8⟩ := H4
  obtain ⟨H9, H10⟩ := H8
  obtain ⟨_, H11⟩ := H10
  obtain ⟨H7, H12⟩ := H6
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨_, H15⟩ := H14
  have HS := sum_exists_c b4 b3 H9 H13
  obtain ⟨SS, H5⟩ := HS
  have HD := diff_exists_c b0 b1 b2 b4 b3 H7 H9 H13
  obtain ⟨DD, H16⟩ := HD
  have H17 := prod_exists_c SS DD ((by
  obtain ⟨H17, _⟩ := H5
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, H19⟩ := H18
  obtain ⟨_, H20⟩ := H19
  exact H20)) ((by
  obtain ⟨X, H17⟩ := H16
  obtain ⟨_, H18⟩ := H17
  obtain ⟨H19, _⟩ := H18
  obtain ⟨_, H20⟩ := H19
  obtain ⟨_, H21⟩ := H20
  obtain ⟨_, H22⟩ := H21
  exact H22))
  obtain ⟨PSD, H18⟩ := H17
  have HH := diff_exists_c b0 b1 b2 b6 b5 H7 H11 H15
  obtain ⟨D2, H19⟩ := HH
  have HH0 := diff_of_squares_c b0 b1 b2 b4 b3 b6 b5 D2 SS DD PSD b11 b10 H19 H5 H16 H18
  subst HH0
  have HH1 := ltp__diff_pos_c b0 b1 b2 b5 b6 D2 b9 H19
  have H21 := prod_pos__signeq_c b0 b1 b2 SS DD D2 ((fun H21 => (by
  subst H21
  have H23 := sum_pos_pos_c b0 b1 b2 b4 b3 b0 b8 b7 H5
  obtain ⟨H24, H25⟩ := H23
  obtain ⟨_, H26⟩ := H25
  rcases H26 with _ | _
  · have H27 := (let H27 := rfl; H24 H27)
    exact (H27).elim
  · have H27 := (let H27 := rfl; H24 H27)
    exact (H27).elim))) ((fun H21 => (by
  subst H21
  have H24 := diff_null_eq_c b0 b1 b2 b4 b3 H16
  subst H24
  have H27 := prod_0_r_c b0 b1 b2 SS H7 ((by
  obtain ⟨H27, _⟩ := H5
  obtain ⟨_, H28⟩ := H27
  obtain ⟨_, H29⟩ := H28
  obtain ⟨_, H30⟩ := H29
  exact H30))
  have H28 := prod_uniqueness_c SS b0 D2 b0 H18 H27
  subst H28
  have H30 := diff_null_eq_c b0 b1 b2 b6 b5 H19
  subst H30
  obtain ⟨DF, H32⟩ := b9
  obtain ⟨H33, H34⟩ := H32
  have HD0 := diff_null_c b0 b1 b2 b5 H7 H15
  have H35 := diff_uniqueness_c b0 b1 b2 b5 b5 DF b0 H33 HD0
  subst H35
  obtain ⟨H37, H38⟩ := H34
  obtain ⟨_, H39⟩ := H38
  rcases H39 with _ | _
  · have H40 := (let H40 := rfl; H37 H40)
    exact (H40).elim
  · have H40 := (let H40 := rfl; H37 H40)
    exact (H40).elim))) H18 HH1
  rcases H21 with H22 | H22
  · obtain ⟨_, H23⟩ := H22
    have H24 := diff_pos__ltp_c b0 b1 b2 b3 b4 DD H16 H23
    exact H24
  · obtain ⟨H23, _⟩ := H22
    exact (((let HS0 := sum_pos_pos_c b0 b1 b2 b4 b3 SS b8 b7 H5; (let HS1 := pos_not_neg_c b0 b1 SS HS0; ((HS1 H23)).elim)))).elim
theorem ltp__ltps_c :
    ∀ (O E E' A B : Tpoint), LtP O E E' A B → LtPs O E E' A B := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨D, H0⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  exact ⟨D, (⟨H2, (diff_sum_c b0 b1 b2 b3 D b4 H1)⟩)⟩
theorem ltps__ltp_c :
    ∀ (O E E' A B : Tpoint), LtPs O E E' A B → LtP O E E' A B := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨D, H0⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  exact ⟨D, (⟨(sum_diff_c b0 b1 b2 b3 D b4 H2), H1⟩)⟩
theorem ltp__lep_neq_c :
    ∀ (O E E' A B : Tpoint), LtP O E E' A B → LeP O E E' A B ∧ A ≠ B := by
  intro b0 b1 b2 b3 b4 b5
  exact ⟨(Or.inl b5), ((by
  obtain ⟨D, H0⟩ := b5
  obtain ⟨H1, H2⟩ := H0
  intro H3
  subst H3
  have HD := H1
  obtain ⟨B', H5⟩ := HD
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, _⟩ := H6
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨H10, H11⟩ := H9
  obtain ⟨_, H12⟩ := H11
  have H13 := diff_null_c b0 b1 b2 b3 H8 H10
  have H14 := diff_uniqueness_c b0 b1 b2 b3 b3 D b0 H1 H13
  subst H14
  obtain ⟨H16, H17⟩ := H2
  obtain ⟨_, H18⟩ := H17
  rcases H18 with _ | _
  · have H19 := (let H19 := rfl; H16 H19)
    exact (H19).elim
  · have H19 := (let H19 := rfl; H16 H19)
    exact (H19).elim))⟩
theorem lep_neq__ltp_c :
    ∀ (O E E' A B : Tpoint), LeP O E E' A B ∧ A ≠ B → LtP O E E' A B := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H0, H1⟩ := b5
  rcases H0 with H2 | H2
  · exact H2
  · exact ((H1 H2)).elim
theorem sum_preserves_ltp_c :
    ∀ (O E E' A B C AC BC : Tpoint), LtP O E E' A B → Sum O E E' A C AC → Sum O E E' B C BC → LtP O E E' AC BC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have H2 := ltp__lep_neq_c b0 b1 b2 b3 b4 b8
  obtain ⟨H3, H4⟩ := H2
  exact lep_neq__ltp_c b0 b1 b2 b6 b7 (⟨(compatibility_of_sum_with_order_c b0 b1 b2 b3 b4 b5 b6 b7 H3 b9 b10), ((fun H5 => (by
  subst H5
  have HS := b9
  obtain ⟨H7, _⟩ := HS
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨_, _⟩ := H10
  have H11 := sum_uniquenessA_c b5 b3 b4 b6 b9 b10
  exact ((H4 H11)).elim)))⟩)
theorem sum_preserves_lep_c :
    ∀ (O E E' A B C AC BC : Tpoint), LeP O E E' A B → Sum O E E' A C AC → Sum O E E' B C BC → LeP O E E' AC BC := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have o := point_equality_decidability b3 b4
  rcases o with H2 | H2
  · subst H2
    have HH := sum_uniqueness_c b3 b5 b6 b7 b9 b10
    subst HH
    exact leP_refl_c b0 b1 b2 b6
  · have H3 := lep_neq__ltp_c b0 b1 b2 b3 b4 (⟨b8, H2⟩)
    exact ltp_to_lep_c b0 b1 b2 b6 b7 (sum_preserves_ltp_c b0 b1 b2 b3 b4 b5 b6 b7 H3 b9 b10)
theorem sum_preserves_ltp_rev_c :
    ∀ (O E E' A B C AC BC : Tpoint), Sum O E E' A C AC → Sum O E E' B C BC → LtP O E E' AC BC → LtP O E E' A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have HS1 := b8
  have HS2 := b9
  obtain ⟨H2, _⟩ := HS2
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, _⟩ := HS1
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H11, H12⟩ := H10
  have HH := opp_exists_c b5 H11
  obtain ⟨C', H13⟩ := HH
  have OP := H13
  obtain ⟨H14, _⟩ := OP
  obtain ⟨H15, H16⟩ := H14
  obtain ⟨H17, H18⟩ := H16
  obtain ⟨_, _⟩ := H18
  have H19 := sum_comm_c C' b5 b0 H13
  have HH0 := sum_exists_c b6 C' H12 H17
  obtain ⟨D, H20⟩ := HH0
  have HH1 := sum_assoc_c b0 b1 b2 b3 b5 C' b6 b0 D b8 H19
  obtain ⟨x, x0⟩ := HH1
  have H23 := x0 H20
  have HS := sum_A_O_eq_c b3 D H23
  subst HS
  have HH2 := sum_exists_c b7 C' H6 H17
  obtain ⟨D0, H25⟩ := HH2
  have HH3 := sum_assoc_c b0 b1 b2 b4 b5 C' b7 b0 D0 b9 H19
  obtain ⟨x1, x2⟩ := HH3
  have H28 := x2 H25
  have HS0 := sum_A_O_eq_c b4 D0 H28
  subst HS0
  exact sum_preserves_ltp_c b0 b1 b2 b6 b7 C' b3 b4 b10 H20 H25
theorem sum_preserves_lep_rev_c :
    ∀ (O E E' A B C AC BC : Tpoint), Sum O E E' A C AC → Sum O E E' B C BC → LeP O E E' AC BC → LeP O E E' A B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
  have HS1 := b8
  have HS2 := b9
  obtain ⟨H2, _⟩ := HS2
  obtain ⟨_, H4⟩ := H2
  obtain ⟨_, H5⟩ := H4
  obtain ⟨_, H6⟩ := H5
  obtain ⟨H7, _⟩ := HS1
  obtain ⟨H8, H9⟩ := H7
  obtain ⟨_, H10⟩ := H9
  obtain ⟨_, _⟩ := H10
  rcases b10 with H3 | H3
  · exact Or.inl (sum_preserves_ltp_rev_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 H3)
  · subst H3
    exact Or.inr (sum_uniquenessA_c b5 b3 b4 b6 b8 b9)
theorem cong2_lea__le_c :
    ∀ (A B C D E F : Tpoint), Cong A B D E → Cong A C D F → LeA F D E C A B → Le E F B C := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have H2 := ((let o := conga_dec_c b5 b3 b4 b2 b0 b1; (by
  rcases o with H2 | H2
  · exact Or.inr H2
  · exact Or.inl (⟨b8, H2⟩))))
  rcases H2 with H3 | H3
  · have H4 := t18_18_c b0 b1 b2 b3 b4 b5 b6 b7 H3
    exact lt__le_c b4 b5 b1 b2 H4
  · have H4 := l11_49_c b5 b3 b4 b2 b0 b1 H3 ((by cong_r)) ((by cong_r))
    obtain ⟨H5, _⟩ := H4
    exact ⟨b2, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial b1 b2))))), ((by cong_r))⟩)⟩
theorem lea_out_lea_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), Out B A A' → Out B C C' → Out E D D' → Out E F F' → LeA A B C D E F → LeA A' B C' D' E F' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  obtain ⟨P, H4⟩ := b14
  obtain ⟨H5, H6⟩ := H4
  exact ⟨P, (⟨(l11_25_c P b3 b4 b5 b8 b9 P H5 (l6_6 b12) (l6_6 b13) (l6_6 (out_trivial ((fun H7 => (by
  obtain ⟨_, H8⟩ := H6
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H11, _⟩ := H10
  have H12 := H11 H7
  exact (H12).elim)))))), (l11_10_c b0 b1 b2 b3 b4 P b6 b7 b8 P H6 (l6_6 b10) (l6_6 b11) (l6_6 b12) (l6_6 (out_trivial ((fun H7 => (by
  obtain ⟨_, H8⟩ := H6
  obtain ⟨_, H9⟩ := H8
  obtain ⟨_, H10⟩ := H9
  obtain ⟨H11, _⟩ := H10
  have H12 := H11 H7
  exact (H12).elim))))))⟩)⟩
theorem lta_out_lta_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), Out B A A' → Out B C C' → Out E D D' → Out E F F' → LtA A B C D E F → LtA A' B C' D' E F' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
  obtain ⟨H4, H5⟩ := b14
  exact ⟨(lea_out_lea_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 H4), ((fun H6 => H5 (l11_10_c b6 b1 b7 b8 b4 b9 b0 b2 b3 b5 H6 b10 b11 b12 b13)))⟩
theorem pythagoras_obtuse_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Obtuse A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LtP O E E' S2 AB2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
  obtain ⟨A', H8⟩ := b14
  obtain ⟨B', H9⟩ := H8
  obtain ⟨C', H10⟩ := H9
  obtain ⟨H11, H12⟩ := H10
  have H13 := (by
  obtain ⟨H13, _⟩ := H12
  obtain ⟨P, H14⟩ := H13
  obtain ⟨H15, H16⟩ := H14
  exact ⟨((fun H17 => (by
  obtain ⟨_, H18⟩ := H15
  obtain ⟨H19, H20⟩ := H16
  obtain ⟨_, H21⟩ := H18
  obtain ⟨_, H22⟩ := H20
  obtain ⟨_, _⟩ := H21
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  have H24 := H19 H17
  exact (H24).elim))), (⟨((fun H17 => (by
  obtain ⟨_, H18⟩ := H15
  obtain ⟨_, H19⟩ := H16
  obtain ⟨_, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H19
  obtain ⟨_, _⟩ := H20
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  have H24 := H21 H17
  exact (H24).elim))), (⟨((by
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, H18⟩ := H17
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨_, _⟩ := H20
  obtain ⟨_, H21⟩ := H15
  obtain ⟨_, H22⟩ := H21
  obtain ⟨_, _⟩ := H22
  exact Ne.symm H19)), (⟨((fun H17 => (by
  obtain ⟨_, H18⟩ := H15
  obtain ⟨_, H19⟩ := H16
  obtain ⟨_, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H19
  obtain ⟨_, _⟩ := H20
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  have H24 := H21 H17
  exact (H24).elim))), ((by
  obtain ⟨_, H17⟩ := H16
  obtain ⟨_, H18⟩ := H17
  obtain ⟨_, H19⟩ := H18
  obtain ⟨_, _⟩ := H19
  obtain ⟨_, H20⟩ := H15
  obtain ⟨H21, H22⟩ := H20
  obtain ⟨_, _⟩ := H22
  exact Ne.symm H21))⟩)⟩)⟩)⟩)
  obtain ⟨H14, H15⟩ := H13
  obtain ⟨H16, H17⟩ := H15
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨H20, H21⟩ := H19
  have HH := l6_11_existence_c B' b5 b3 A' H14 H18
  obtain ⟨AA, H22⟩ := HH
  obtain ⟨H23, H24⟩ := H22
  have HH0 := l6_11_existence_c B' b5 b4 C' H20 H21
  obtain ⟨CC, H25⟩ := HH0
  obtain ⟨H26, H27⟩ := H25
  have H28 := t18_18_c b5 b3 b4 B' AA CC ((by cong_r)) ((by cong_r)) (lta_comm_c AA B' CC b3 b5 b4 (lta_out_lta_c A' B' C' b3 b5 b4 AA CC b3 b4 (l6_6 H23) (l6_6 H26) (l6_6 (out_trivial (Ne.symm H18))) (l6_6 (out_trivial (Ne.symm H21))) H12))
  have H29 := (fun H29 => (by
  obtain ⟨H30, _⟩ := b19
  obtain ⟨H31, H32⟩ := H30
  obtain ⟨_, H33⟩ := H32
  obtain ⟨_, _⟩ := H33
  have H34 := H31 H29
  exact (H34).elim))
  have H30 := length_existence_c b0 b1 b2 AA CC H29
  obtain ⟨x, x0⟩ := H30
  have H32 := prod_exists_c x x ((by
  obtain ⟨_, H32⟩ := x0
  obtain ⟨H33, H34⟩ := H32
  obtain ⟨_, _⟩ := H34
  exact H33)) ((by
  obtain ⟨_, H32⟩ := x0
  obtain ⟨H33, H34⟩ := H32
  obtain ⟨_, _⟩ := H34
  exact H33))
  obtain ⟨SS, H33⟩ := H32
  have H34 := per_col_c A' B' C' CC (Ne.symm H20) H11 ((let H34 := out_col H26; (by colr)))
  have H35 := l8_2_c A' B' CC H34
  have H36 := per_col_c CC B' A' AA (Ne.symm H14) H35 ((let H36 := out_col H23; (by colr)))
  have H37 := pythagoras_c b0 b1 b2 AA CC B' b6 b7 x b9 b10 SS b13 (l8_2_c CC B' AA H36) x0 (length_eq_cong_2_c b0 b1 b2 b3 b5 AA B' b6 b16 ((by cong_r))) (length_eq_cong_2_c b0 b1 b2 b4 b5 CC B' b7 b17 ((by cong_r))) b18 b19 H33
  have H38 := sum_uniqueness_c b9 b10 b12 SS b21 H37
  subst H38
  have HH1 := lt_to_ltp_c b0 b1 b2 AA CC x b3 b4 b8 x0 b15 H28
  have H40 := (let H40 := (fun H40 => (by
  subst H40
  have H43 := (by cong_r)
  have H44 := cong_identity b5 b3 AA H43
  subst H44
  exact ((H18 rfl)).elim)); (let H41 := (fun H41 => (by
  subst H41
  have H44 := (by cong_r)
  have H45 := cong_identity b5 b4 CC H44
  subst H45
  exact ((H21 rfl)).elim)); (let H42 := (fun H42 => (by
  subst H42
  have H47 := l8_8_c AA B' H36
  subst H47
  have H52 := (by cong_r)
  have H53 := cong_identity b5 b4 AA H52
  subst H53
  have H57 := (by cong_r)
  have H58 := cong_identity b5 b3 AA H57
  subst H58
  have H60 := (let H60 := rfl; H18 H60)
  have H62 := (let H62 := rfl; H40 H62)
  exact (H60).elim)); (let H43 := length_Ps_c b0 b1 b2 AA CC x ((fun H43 => (let H44 := Eq.symm H43; (by
  subst H44
  have H46 := length_cong_c b0 b1 b2 AA CC b0 x0
  have H47 := cong_identity AA CC b0 H46
  subst H47
  have H49 := (let H49 := rfl; H42 H49)
  exact (H49).elim)))) x0; H43))))
  exact square_increase_strict_c b0 b1 b2 x b8 b12 b11 ((by
  obtain ⟨_, H41⟩ := x0
  obtain ⟨H42, H43⟩ := H41
  obtain ⟨_, _⟩ := H43
  obtain ⟨_, H44⟩ := b15
  obtain ⟨H45, H46⟩ := H44
  obtain ⟨_, _⟩ := H46
  exact ⟨H29, (⟨H42, (⟨H45, H42⟩)⟩)⟩)) H40 (length_Ps_c b0 b1 b2 b3 b4 b8 ((fun H41 => (let H42 := Eq.symm H41; (by
  subst H42
  have HH3 := ltP_neg_c b0 b1 b2 x HH1
  have H43 := pos_not_neg_c b0 b1 x H40
  exact ((H43 HH3)).elim)))) b15) HH1 H33 b20
theorem pythagoras_obtuse_or_per_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Obtuse A C B ∨ Per A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LeP O E E' S2 AB2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
  rcases b14 with H8 | H8
  · exact ltp_to_lep_c b0 b1 b2 b12 b11 (pythagoras_obtuse_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 H8 b15 b16 b17 b18 b19 b20 b21)
  · have HH := pythagoras_c b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b13 H8 b15 b16 b17 b18 b19 b20
    have H9 := sum_uniqueness_c b9 b10 b12 b11 b21 HH
    subst H9
    exact leP_refl_c b0 b1 b2 b11
theorem pythagoras_acute_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Acute A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LtP O E E' AB2 S2 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
  obtain ⟨A', H8⟩ := b14
  obtain ⟨B', H9⟩ := H8
  obtain ⟨C', H10⟩ := H9
  obtain ⟨H11, H12⟩ := H10
  have H13 := ⟨((fun H13 => (by
  subst H13
  obtain ⟨H15, H16⟩ := H12
  obtain ⟨P, H17⟩ := H15
  obtain ⟨_, H18⟩ := H17
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨_, H21⟩ := H20
  obtain ⟨_, H22⟩ := H21
  obtain ⟨_, _⟩ := H22
  have H23 := (let H23 := rfl; H19 H23)
  have H25 := fun H25 H26 => H16 (⟨H25, H26⟩)
  exact (H23).elim))), ((fun H13 => (by
  subst H13
  obtain ⟨H15, H16⟩ := H12
  obtain ⟨P, H17⟩ := H15
  obtain ⟨_, H18⟩ := H17
  obtain ⟨H19, H20⟩ := H18
  obtain ⟨H21, H22⟩ := H20
  obtain ⟨_, H23⟩ := H22
  obtain ⟨_, _⟩ := H23
  have H24 := (let H24 := rfl; H21 H24)
  have H26 := fun H26 H27 => H16 (⟨H26, H27⟩)
  have H27 := H26 H19
  have H28 := fun H28 H29 => H27 (⟨H28, H29⟩)
  exact (H24).elim)))⟩
  obtain ⟨H14, H15⟩ := H13
  have H16 := (fun H16 => (by
  obtain ⟨H17, _⟩ := b19
  obtain ⟨H18, H19⟩ := H17
  obtain ⟨_, H20⟩ := H19
  obtain ⟨_, _⟩ := H20
  have H21 := H18 H16
  exact (H21).elim))
  have o := point_equality_decidability b3 b4
  rcases o with H17 | H17
  · subst H17
    have H21 := length_id_2_c b0 b1 b2 b3 b13
    have H22 := length_uniqueness_c b0 b1 b2 b3 b3 b8 b0 b15 H21
    have H23 := Eq.symm H22
    subst H23
    have H25 := prod_O_l_eq_c b0 b1 b2 b0 b11 b20
    subst H25
    have H26 := length_Ps_c b0 b1 b2 b3 b5 b6 ((fun H26 => (by
  subst H26
  have H28 := length_cong_c b0 b1 b2 b3 b5 b0 b16
  have H29 := cong_identity b3 b5 b0 H28
  subst H29
  have H31 := (let H31 := rfl; H14 H31)
  exact (H31).elim))) b16
    have H27 := length_Ps_c b0 b1 b2 b3 b5 b7 ((fun H27 => (by
  subst H27
  have H29 := length_cong_c b0 b1 b2 b3 b5 b0 b17
  have H30 := cong_identity b3 b5 b0 H29
  subst H30
  have H32 := (let H32 := rfl; H14 H32)
  exact (H32).elim))) b17
    have H28 := signeq__prod_pos_c b0 b1 b2 b6 b6 b9 (Or.inl (⟨H26, H26⟩)) b18
    have H29 := signeq__prod_pos_c b0 b1 b2 b7 b7 b10 (Or.inl (⟨H27, H27⟩)) b19
    have H30 := sum_pos_pos_c b0 b1 b2 b9 b10 b12 H28 H29 b21
    exact ⟨b12, (⟨(diff_A_O_c b0 b1 b2 b12 H16 ((let H31 := out_col H26; (by colr)))), H30⟩)⟩
  · have H18 := (by
  obtain ⟨H18, _⟩ := H12
  obtain ⟨P, H19⟩ := H18
  obtain ⟨H20, _⟩ := H19
  exact ⟨((fun H21 => (by
  obtain ⟨H22, H23⟩ := H20
  obtain ⟨_, H24⟩ := H23
  obtain ⟨_, _⟩ := H24
  have H25 := H22 H21
  exact (H25).elim))), (⟨((fun H21 => (by
  obtain ⟨_, H22⟩ := H20
  obtain ⟨H23, H24⟩ := H22
  obtain ⟨_, _⟩ := H24
  have H25 := H23 H21
  exact (H25).elim))), ((fun H21 => (by
  obtain ⟨_, H22⟩ := H20
  obtain ⟨H23, H24⟩ := H22
  obtain ⟨_, _⟩ := H24
  have H25 := H23 H21
  exact (H25).elim)))⟩)⟩)
    obtain ⟨H19, H20⟩ := H18
    obtain ⟨H21, H22⟩ := H20
    have H23 := l6_11_existence_c B' b5 b3 A' H19 (Ne.symm H14)
    obtain ⟨AA, H24⟩ := H23
    obtain ⟨H25, H26⟩ := H24
    have H27 := l6_11_existence_c B' b5 b4 C' H22 (Ne.symm H15)
    obtain ⟨CC, H28⟩ := H27
    obtain ⟨H29, H30⟩ := H28
    have H31 := t18_18_c B' AA CC b5 b3 b4 H26 H30 (lta_comm_c b3 b5 b4 AA B' CC (lta_out_lta_c b3 b5 b4 A' B' C' b3 b4 AA CC (l6_6 (out_trivial H14)) (l6_6 (out_trivial H15)) (l6_6 H25) (l6_6 H29) H12))
    have H32 := length_existence_c b0 b1 b2 AA CC H16
    obtain ⟨x, x0⟩ := H32
    have H34 := prod_exists_c x x ((by
  obtain ⟨_, H34⟩ := x0
  obtain ⟨H35, H36⟩ := H34
  obtain ⟨_, _⟩ := H36
  exact H35)) ((by
  obtain ⟨_, H34⟩ := x0
  obtain ⟨H35, H36⟩ := H34
  obtain ⟨_, _⟩ := H36
  exact H35))
    obtain ⟨SS, H35⟩ := H34
    have H36 := per_col_c A' B' C' CC (Ne.symm H22) H11 ((let H36 := out_col H29; (by colr)))
    have H37 := l8_2_c A' B' CC H36
    have H38 := per_col_c CC B' A' AA (Ne.symm H19) H37 ((let H38 := out_col H25; (by colr)))
    have H39 := pythagoras_c b0 b1 b2 AA CC B' b6 b7 x b9 b10 SS b13 (l8_2_c CC B' AA H38) x0 (length_eq_cong_2_c b0 b1 b2 b3 b5 AA B' b6 b16 ((by cong_r))) (length_eq_cong_2_c b0 b1 b2 b4 b5 CC B' b7 b17 ((by cong_r))) b18 b19 H35
    have H40 := sum_uniqueness_c b9 b10 b12 SS b21 H39
    subst H40
    have HH := lt_to_ltp_c b0 b1 b2 b3 b4 b8 AA CC x b15 x0 H31
    exact square_increase_strict_c b0 b1 b2 b8 x b11 b12 ((by
  obtain ⟨_, H42⟩ := x0
  obtain ⟨H43, H44⟩ := H42
  obtain ⟨_, _⟩ := H44
  obtain ⟨_, H45⟩ := b15
  obtain ⟨H46, H47⟩ := H45
  obtain ⟨_, _⟩ := H47
  exact ⟨H16, (⟨H46, (⟨H43, H46⟩)⟩)⟩)) ((let H42 := length_Ps_c b0 b1 b2 b3 b4 b8 ((fun H42 => (let H43 := Eq.symm H42; (by
  subst H43
  have H45 := length_cong_c b0 b1 b2 b3 b4 b0 b15
  have H46 := cong_identity b3 b4 b0 H45
  subst H46
  have H48 := (let H48 := rfl; H17 H48)
  exact (H48).elim)))) b15; H42)) ((let H42 := (fun H42 => (by
  subst H42
  have H45 := (by cong_r)
  have H46 := cong_identity b5 b3 AA H45
  subst H46
  exact ((H14 rfl)).elim)); (let H43 := (fun H43 => (by
  subst H43
  have H46 := (by cong_r)
  have H47 := cong_identity b5 b4 CC H46
  subst H47
  exact ((H15 rfl)).elim)); (let H44 := (fun H44 => (by
  subst H44
  have H49 := l8_8_c AA B' H38
  subst H49
  have H54 := (by cong_r)
  have H55 := cong_identity b5 b4 AA H54
  subst H55
  have H59 := (by cong_r)
  have H60 := cong_identity b5 b3 AA H59
  subst H60
  have H62 := (let H62 := rfl; H14 H62)
  have H64 := (let H64 := rfl; H42 H64)
  exact (H62).elim)); (let H45 := length_Ps_c b0 b1 b2 AA CC x ((fun H45 => (let H46 := Eq.symm H45; (by
  subst H46
  have H48 := length_cong_c b0 b1 b2 AA CC b0 x0
  have H49 := cong_identity AA CC b0 H48
  subst H49
  have H51 := (let H51 := rfl; H44 H51)
  exact (H51).elim)))) x0; H45))))) HH b20 H35
theorem pyth_context_c :
    ∀ (O E E' A B C : Tpoint), ¬ Col O E E' → ∃ (AB BC AC AB2 BC2 AC2 SS : Tpoint), Col O E AB ∧ Col O E BC ∧ Col O E AC ∧ Col O E AB2 ∧ Col O E BC2 ∧ Col O E AC2 ∧ Length O E E' A B AB ∧ Length O E E' B C BC ∧ Length O E E' A C AC ∧ Prod O E E' AB AB AB2 ∧ Prod O E E' BC BC BC2 ∧ Prod O E E' AC AC AC2 ∧ Sum O E E' AB2 BC2 SS := by
  intro b0 b1 b2 b3 b4 b5 b6
  have Lab := length_existence_c b0 b1 b2 b3 b4 b6
  obtain ⟨AB, H0⟩ := Lab
  have Lbc := length_existence_c b0 b1 b2 b4 b5 b6
  obtain ⟨BC, H1⟩ := Lbc
  have Lac := length_existence_c b0 b1 b2 b3 b5 b6
  obtain ⟨AC, H2⟩ := Lac
  have H3 := (by
  obtain ⟨_, H4⟩ := H0
  obtain ⟨_, H5⟩ := H1
  obtain ⟨_, H6⟩ := H2
  obtain ⟨H3, H7⟩ := H4
  obtain ⟨H8, H9⟩ := H5
  obtain ⟨H10, H11⟩ := H6
  obtain ⟨_, _⟩ := H7
  obtain ⟨_, _⟩ := H9
  obtain ⟨_, _⟩ := H11
  exact ⟨H3, (⟨H8, H10⟩)⟩)
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  have Pab := prod_exists_c AB AB H4 H4
  obtain ⟨AB2, H8⟩ := Pab
  have Pbc := prod_exists_c BC BC H6 H6
  obtain ⟨BC2, H9⟩ := Pbc
  have Pac := prod_exists_c AC AC H7 H7
  obtain ⟨AC2, H10⟩ := Pac
  have H11 := ((by
  obtain ⟨H11, _⟩ := H8
  obtain ⟨H12, _⟩ := H9
  obtain ⟨H13, _⟩ := H10
  obtain ⟨_, H14⟩ := H11
  obtain ⟨_, H15⟩ := H12
  obtain ⟨_, H16⟩ := H13
  obtain ⟨_, H17⟩ := H14
  obtain ⟨_, H18⟩ := H15
  obtain ⟨_, H19⟩ := H16
  obtain ⟨_, H20⟩ := H17
  obtain ⟨_, H21⟩ := H18
  obtain ⟨_, H22⟩ := H19
  exact ⟨H20, (⟨H21, H22⟩)⟩))
  obtain ⟨H12, H13⟩ := H11
  obtain ⟨H14, H15⟩ := H13
  have HS := sum_exists_c AB2 BC2 H12 H14
  obtain ⟨SS, H16⟩ := HS
  exact ⟨AB, (⟨BC, (⟨AC, (⟨AB2, (⟨BC2, (⟨AC2, (⟨SS, (⟨H4, (⟨H6, (⟨H7, (⟨H12, (⟨H14, (⟨H15, (⟨H0, (⟨H1, (⟨H2, (⟨H8, (⟨H9, (⟨H10, H16⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩
theorem length_pos_or_null_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → Ps O E AB ∨ A = B := by
  intro b0 b1 b2 b3 b4 b5 b6
  have o := point_equality_decidability b3 b4
  rcases o with H0 | H0
  · exact Or.inr H0
  · have H1 := length_Ps_c b0 b1 b2 b3 b4 b5 ((fun H1 => (by
  subst H1
  obtain ⟨_, H3⟩ := b6
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  have H6 := (by cong_r)
  have H7 := cong_identity b3 b4 b0 H6
  subst H7
  have H9 := (let H9 := rfl; H0 H9)
  exact (H9).elim))) b6
    exact Or.inl H1
theorem not_neg_pos_c :
    ∀ (O E A : Tpoint), E ≠ O → Col O E A → ¬ Ng O E A → Ps O E A ∨ A = O := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b2 b0
  rcases o with H2 | H2
  · exact Or.inr H2
  · exact Or.inl (l6_4_2_c b2 b1 b0 (⟨((by colr)), ((fun H3 => b5 (⟨H2, (⟨b3, H3⟩)⟩)))⟩))
theorem sum_pos_null_c :
    ∀ (O E E' A B : Tpoint), ¬ Ng O E A → ¬ Ng O E B → Sum O E E' A B O → A = O ∧ B = O := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  have H2 := (by
  obtain ⟨H2, H3⟩ := b7
  obtain ⟨H4, H5⟩ := H2
  obtain ⟨H6, H7⟩ := H5
  obtain ⟨H8, H9⟩ := H7
  exact ⟨H6, (⟨H8, (⟨((fun H10 => (by
  subst H10
  exact H4 ((by colr))))), H4⟩)⟩)⟩)
  obtain ⟨H3, H4⟩ := H2
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  have H9 := (let o := point_equality_decidability b3 b0; (by
  rcases o with H9 | H9
  · exact Or.inr H9
  · exact Or.inl ((let H10 := not_neg_pos_c b0 b1 b3 (Ne.symm H7) H3 b5; (by
  rcases H10 with H11 | H11
  · exact H11
  · exact ((H9 H11)).elim)))))
  have H10 := (let o := point_equality_decidability b4 b0; (by
  rcases o with H10 | H10
  · exact Or.inr H10
  · exact Or.inl ((let H11 := not_neg_pos_c b0 b1 b4 (Ne.symm H7) H5 b6; (by
  rcases H11 with H12 | H12
  · exact H12
  · exact ((H10 H12)).elim)))))
  rcases H9 with H11 | H11
  · rcases H10 with H12 | H12
    · have HH := sum_pos_pos_c b0 b1 b2 b3 b4 b0 H11 H12 b7
      obtain ⟨H13, H14⟩ := HH
      obtain ⟨_, H15⟩ := H14
      rcases H15 with _ | _
      · have H16 := (let H16 := rfl; H13 H16)
        exact ⟨((H16).elim), ((H16).elim)⟩
      · have H16 := (let H16 := rfl; H13 H16)
        exact ⟨((H16).elim), ((H16).elim)⟩
    · subst H12
      have HH := sum_A_O_c b3 H3
      exact ⟨(sum_uniqueness_c b3 b0 b3 b0 HH b7), rfl⟩
  · rcases H10 with _ | H12
    · subst H11
      have HH := sum_O_B_c b4 H5
      exact ⟨rfl, (sum_uniqueness_c b0 b4 b4 b0 HH b7)⟩
    · exact ⟨H11, H12⟩
theorem length_not_neg_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → ¬ Ng O E AB := by
  intro b0 b1 b2 b3 b4 b5 b6
  intro H0
  have HH := length_cong_c b0 b1 b2 b3 b4 b5 b6
  have H1 := length_pos_or_null_c b0 b1 b2 b3 b4 b5 b6
  rcases H1 with H2 | H2
  · have H3 := pos_not_neg_c b0 b1 b5 H2
    exact ((H3 H0)).elim
  · obtain ⟨H3, H4⟩ := H0
    obtain ⟨_, H5⟩ := H4
    subst H2
    have HH1 := (by cong_r)
    have HH2 := cong_identity b0 b5 b3 HH1
    subst HH2
    have H7 := (let H7 := rfl; H3 H7)
    exact (H7).elim
theorem signEq_refl_c :
    ∀ (O E A : Tpoint), O ≠ E → Col O E A → A = O ∨ SignEq O E A A := by
  intro b0 b1 b2 b3 b4
  have HH := sign_dec_c b0 b1 b2 b4 b3
  rcases HH with H1 | H1
  · exact Or.inl H1
  · rcases H1 with H2 | H2
    · exact Or.inr (Or.inl (⟨H2, H2⟩))
    · exact Or.inr (Or.inr (⟨H2, H2⟩))
theorem square_not_neg_c :
    ∀ (O E E' A A2 : Tpoint), Prod O E E' A A A2 → ¬ Ng O E A2 := by
  intro b0 b1 b2 b3 b4 b5
  intro H0
  have H1 := (by
  obtain ⟨H1, H2⟩ := b5
  obtain ⟨H3, H4⟩ := H1
  obtain ⟨H5, H6⟩ := H4
  obtain ⟨H7, H8⟩ := H6
  exact ⟨((fun H9 => (by
  subst H9
  exact H3 ((by colr))))), H7⟩)
  obtain ⟨H2, H3⟩ := H1
  have HP := signEq_refl_c b0 b1 b3 H2 H3
  rcases HP with H4 | H4
  · subst H4
    have HH := prod_O_l_eq_c b0 b1 b2 b0 b4 b5
    obtain ⟨H6, H7⟩ := H0
    obtain ⟨_, _⟩ := H7
    exact ((H6 HH)).elim
  · have HH := signeq__prod_pos_c b0 b1 b2 b3 b3 b4 H4 b5
    have HH0 := pos_not_neg_c b0 b1 b4 HH
    exact ((HH0 H0)).elim
theorem root_uniqueness_c :
    ∀ (O E E' A B C : Tpoint), ¬ Ng O E A → ¬ Ng O E B → Prod O E E' A A C → Prod O E E' B B C → A = B := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have H1 := ((by
  obtain ⟨H1, _⟩ := b8
  obtain ⟨H2, _⟩ := b9
  obtain ⟨H3, H4⟩ := H1
  obtain ⟨H5, H6⟩ := H2
  obtain ⟨_, H7⟩ := H4
  obtain ⟨_, H8⟩ := H6
  obtain ⟨H9, _⟩ := H7
  obtain ⟨H10, H11⟩ := H8
  exact ⟨((fun H12 => (let H13 := H3 H12; (let H14 := H5 H12; (H13).elim)))), (⟨H9, (⟨H10, H11⟩)⟩)⟩))
  obtain ⟨H2, H3⟩ := H1
  obtain ⟨H4, H5⟩ := H3
  obtain ⟨H6, H7⟩ := H5
  have HS := sum_exists_c b3 b4 H4 H6
  obtain ⟨ApB, H8⟩ := HS
  have HD := diff_exists_c b0 b1 b2 b3 b4 H2 H4 H6
  obtain ⟨AmB, H9⟩ := HD
  have H10 := (by
  obtain ⟨X, H10⟩ := H9
  obtain ⟨_, H11⟩ := H10
  obtain ⟨H12, _⟩ := H8
  obtain ⟨_, H13⟩ := H12
  obtain ⟨H14, _⟩ := H11
  obtain ⟨_, H15⟩ := H13
  obtain ⟨_, H16⟩ := H14
  obtain ⟨_, H17⟩ := H15
  obtain ⟨_, H18⟩ := H16
  obtain ⟨_, H19⟩ := H18
  exact ⟨H17, H19⟩)
  obtain ⟨H11, H12⟩ := H10
  have HP := prod_exists_c ApB AmB H11 H12
  obtain ⟨PP, H13⟩ := HP
  have H14 := diff_null_c b0 b1 b2 b5 H2 H7
  have HH := diff_of_squares_c b0 b1 b2 b3 b4 b5 b5 b0 ApB AmB PP b8 b9 H14 H8 H9 H13
  subst HH
  have HH0 := prod_null_c b0 b1 b2 ApB AmB H13
  have o := point_equality_decidability b3 b0
  rcases o with H16 | H16
  · subst H16
    have H20 := prod_O_l_eq_c b0 b1 b2 b0 b5 b8
    subst H20
    have H22 := prod_null_c b0 b1 b2 b4 b4 b9
    rcases H22 with H23 | H23
    · subst H23
      exact rfl
    · subst H23
      exact rfl
  · have H17 := (fun H17 => (by
  subst H17
  exact H2 ((by colr))))
    have o0 := point_equality_decidability b4 b0
    rcases o0 with H18 | H18
    · subst H18
      have H22 := prod_O_l_eq_c b0 b1 b2 b0 b5 b9
      subst H22
      have H24 := prod_null_c b0 b1 b2 b3 b3 b8
      rcases H24 with H25 | H25
      · subst H25
        exact rfl
      · subst H25
        exact rfl
    · rcases HH0 with H19 | H19
      · have H20 := not_neg_pos_c b0 b1 b3 H17 H4 b6
        have H21 := not_neg_pos_c b0 b1 b4 H17 H6 b7
        rcases H20 with H22 | H22
        · rcases H21 with H23 | H23
          · have HP0 := sum_pos_pos_c b0 b1 b2 b3 b4 ApB H22 H23 H8
            subst H19
            obtain ⟨H24, H25⟩ := HP0
            obtain ⟨_, H26⟩ := H25
            rcases H26 with _ | _
            · have H27 := (let H27 := rfl; H24 H27)
              exact (H27).elim
            · have H27 := (let H27 := rfl; H24 H27)
              exact (H27).elim
          · exact ((H18 H23)).elim
        · rcases H21 with _ | H23
          · exact ((H16 H22)).elim
          · exact ((H18 H23)).elim
      · subst H19
        have H21 := diff_null_eq_c b0 b1 b2 b3 b4 H9
        exact H21
theorem inter_tangent_circle_c :
    ∀ (P Q O M : Tpoint), P ≠ Q → Cong P O Q O → Col P O Q → Le P M P O → Le Q M Q O → M = O := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have H4 := l7_20_c b2 b0 b1 b6 ((by cong_r))
  rcases H4 with H5 | H5
  · exact ((b4 H5)).elim
  · obtain ⟨H6, _⟩ := H5
    have H7 := l5_6_c b1 b3 b1 b2 b1 b3 b0 b2 b8 ((by cong_r)) ((by cong_r))
    have H8 := l5_6_c b0 b3 b0 b2 b0 b3 b2 b0 b7 ((by cong_r)) ((by cong_r))
    have H9 := l5_6_c b1 b3 b1 b2 b1 b3 b2 b1 b8 ((by cong_r)) ((by cong_r))
    obtain ⟨A, H10⟩ := H8
    obtain ⟨H11, H12⟩ := H10
    obtain ⟨B, H13⟩ := H9
    obtain ⟨H14, H15⟩ := H13
    have H16 := between_symmetry (between_inner_transitivity (between_symmetry (between_inner_transitivity H6 H14)) H11)
    have H17 := triangle_inequality_2_c b0 b3 b1 A b2 B H16 ((by cong_r)) ((by cong_r))
    have H18 := bet2_le2__le_c b2 b2 b0 b1 A B H16 H6 (⟨A, (⟨H11, ((by cong_r))⟩)⟩) (⟨B, (⟨H14, ((by cong_r))⟩)⟩)
    have H19 := le_anti_symmetry_c A B b0 b1 H18 H17
    have H20 := bet_cong_eq_c b0 A B b1 (between_symmetry (between_exchange2 (between_symmetry (between_inner_transitivity H6 H14)) H11)) (between_symmetry (between_symmetry (between_exchange2 H6 H14))) H19
    obtain ⟨H21, H22⟩ := H20
    subst H22
    subst H21
    exact Eq.symm (l4_18_c b0 b1 b2 b3 b4 ((by colr)) ((by cong_r)) ((by cong_r)))
theorem inter_circle_per_c :
    ∀ (P Q A T M : Tpoint), Cong P A Q A → Le P M P A → Le Q M Q A → Projp A T P Q → Per P T M → Le T M T A := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HH := lower_dim
  have O := PA
  have E := PB
  have E' := PC
  have HD := (fun H4 => HH ((by
  rcases H4 with H5 | H5
  · have H6 := fun H6 => HH (Or.inl H6)
    have H7 := fun H7 => HH (Or.inr H7)
    have H8 := H6 H5
    have H9 := fun H9 => H7 (Or.inl H9)
    have H10 := fun H10 => H7 (Or.inr H10)
    exact (H8).elim
  · rcases H5 with H6 | H6
    · have H7 := fun H7 => HH (Or.inl H7)
      have H8 := fun H8 => HH (Or.inr H8)
      have H9 := fun H9 => H8 (Or.inl H9)
      have H10 := fun H10 => H8 (Or.inr H10)
      have H11 := H9 H6
      exact (H11).elim
    · have H7 := fun H7 => HH (Or.inl H7)
      have H8 := fun H8 => HH (Or.inr H8)
      have H9 := fun H9 => H8 (Or.inl H9)
      have H10 := fun H10 => H8 (Or.inr H10)
      have H11 := H10 H6
      exact (H11).elim)))
  have o := point_equality_decidability b0 b3
  rcases o with H4 | H4
  · subst H4
    exact b6
  · obtain ⟨H5, H6⟩ := b8
    rcases H6 with H7 | H7
    · obtain ⟨H8, H9⟩ := H7
      have HX := (let H10 := not_col_distincts_c O E E' HD; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨_, _⟩ := H14
  have H15 := per_distinct_c b0 b3 b4 b9 H4
  have H16 := le_diff_c b0 b4 b0 b2 H15 b6
  have H17 := cong_diff H16 b5
  have H18 := perp_distinct_c b0 b1 b2 b3 H9
  have H19 := H18
  obtain ⟨_, _⟩ := H19
  exact H13)))
      have H10 := (let H10 := perp_col_c b0 b1 b2 b3 b3 H4 H9 H8; (let H11 := perp_left_comm_c b0 b3 b2 b3 H10; (let H12 := perp_perp_in_c b3 b0 b2 H11; (let H13 := perp_in_comm_c b3 b0 b2 b3 b3 H12; (let H14 := perp_in_per_c b0 b3 b2 H13; H14)))))
      have Py := pyth_context_c O E E' b0 b3 b2 HD
      obtain ⟨PT, H11⟩ := Py
      obtain ⟨TA, H12⟩ := H11
      obtain ⟨AP, H13⟩ := H12
      obtain ⟨PT2, H14⟩ := H13
      obtain ⟨TA2, H15⟩ := H14
      obtain ⟨AP2, H16⟩ := H15
      obtain ⟨SS, H17⟩ := H16
      obtain ⟨H18, H19⟩ := H17
      obtain ⟨H20, H21⟩ := H19
      obtain ⟨H22, H23⟩ := H21
      obtain ⟨H24, H25⟩ := H23
      obtain ⟨_, H26⟩ := H25
      obtain ⟨_, H27⟩ := H26
      obtain ⟨H28, H29⟩ := H27
      obtain ⟨H30, H31⟩ := H29
      obtain ⟨H32, H33⟩ := H31
      obtain ⟨H34, H35⟩ := H33
      obtain ⟨H36, H37⟩ := H35
      obtain ⟨H38, H39⟩ := H37
      have Pyth := pythagoras_c O E E' b0 b2 b3 PT TA AP PT2 TA2 AP2 HX H10 H32 H28 (length_sym_c O E E' b3 b2 TA H30) H34 H36 H38
      have HE := sum_uniqueness_c PT2 TA2 SS AP2 H39 Pyth
      subst HE
      have Pyth0 := sum_comm_c PT2 TA2 AP2 Pyth
      have Pyth1 := sum_diff_c O E E' TA2 PT2 AP2 Pyth0
      have Py0 := pyth_context_c O E E' b0 b3 b4 HD
      obtain ⟨PT', H41⟩ := Py0
      obtain ⟨TM, H42⟩ := H41
      obtain ⟨PM, H43⟩ := H42
      obtain ⟨PT2', H44⟩ := H43
      obtain ⟨TM2, H45⟩ := H44
      obtain ⟨PM2, H46⟩ := H45
      obtain ⟨SS', H47⟩ := H46
      obtain ⟨H48, H49⟩ := H47
      obtain ⟨H50, H51⟩ := H49
      obtain ⟨H52, H53⟩ := H51
      obtain ⟨H54, H55⟩ := H53
      obtain ⟨H56, H57⟩ := H55
      obtain ⟨H58, H59⟩ := H57
      obtain ⟨H60, H61⟩ := H59
      obtain ⟨H62, H63⟩ := H61
      obtain ⟨H64, H65⟩ := H63
      obtain ⟨H66, H67⟩ := H65
      obtain ⟨H68, H69⟩ := H67
      obtain ⟨H70, H71⟩ := H69
      have H72 := length_uniqueness_c O E E' b0 b3 PT PT' H28 H60
      subst H72
      have H74 := prod_uniqueness_c PT PT PT2 PT2' H34 H66
      subst H74
      have PythM := pythagoras_c O E E' b0 b4 b3 PT TM PM PT2 TM2 PM2 HX b9 H64 H28 (length_sym_c O E E' b3 b4 TM H62) H34 H68 H70
      have H76 := sum_uniqueness_c PT2 TM2 SS' PM2 H71 PythM
      subst H76
      have o0 := point_equality_decidability b3 b4
      rcases o0 with H78 | H78
      · subst H78
        exact le_trivial_c b4 b4 b2
      · have o1 := point_equality_decidability b0 b4
        rcases o1 with H79 | H79
        · subst H79
          have HH0 := length_id_2_c O E E' b0 HX
          have H83 := length_uniqueness_c O E E' b0 b0 PM O H64 HH0
          subst H83
          have H85 := prod_O_l_eq_c O E E' O PM2 H70
          subst H85
          have H87 := sum_pos_null_c O E E' PT2 TM2 (square_not_neg_c O E E' PT PT2 H34) (square_not_neg_c O E E' TM TM2 H68) H71
          obtain ⟨H88, _⟩ := H87
          subst H88
          have H90 := prod_null_c O E E' PT PT H34
          rcases H90 with H91 | H91
          · subst H91
            have H93 := length_cong_c O E E' b0 b3 O H28
            have H94 := cong_identity b0 b3 PA H93
            subst H94
            have H96 := (let H96 := rfl; H4 H96)
            exact (H96).elim
          · subst H91
            have H93 := length_cong_c O E E' b0 b3 O H28
            have H94 := cong_identity b0 b3 PA H93
            subst H94
            have H96 := (let H96 := rfl; H4 H96)
            exact (H96).elim
        · have H80 := length_leP_le_2_c O E E' b0 b4 b0 b2 PM AP H64 H32 b6
          have H81 := square_increase_c O E E' PM AP PM2 AP2 (⟨HD, (⟨H52, (⟨H22, H52⟩)⟩)⟩) (length_Ps_c O E E' b0 b4 PM ((fun H81 => (let O0 := PA; (by
  subst H81
  have H84 := prod_O_l_eq_c O0 E E' O0 PM2 H70
  subst H84
  have H85 := length_id_1_c O0 E E' b0 b4 H64
  exact ((H79 H85)).elim)))) H64) ((let H81 := length_pos_or_null_c O E E' b0 b2 AP H32; (by
  rcases H81 with H82 | H82
  · exact H82
  · subst H82
    have H89 := (by cong_r)
    have H90 := cong_identity b1 b0 b0 H89
    subst H90
    have H96 := le_zero_c b1 b4 b1 b6
    subst H96
    have HH0 := length_id_2_c O E E' b1 HX
    have HP := length_uniqueness_c O E E' b1 b1 O PM HH0 H64
    subst HP
    have H99 := prod_O_l_eq_c O E E' O PM2 H70
    subst H99
    have H101 := sum_pos_null_c O E E' PT2 TM2 (square_not_neg_c O E E' PT PT2 H34) (square_not_neg_c O E E' TM TM2 H68) H71
    obtain ⟨_, _⟩ := H101
    have H102 := (let H102 := rfl; H5 H102)
    exact (H102).elim))) H80 H70 H38
          have H82 := sum_comm_c PT2 TM2 PM2 H71
          have H83 := sum_comm_c PT2 TA2 AP2 H39
          have HH0 := sum_preserves_lep_rev_c O E E' TM2 TA2 PT2 PM2 AP2 H82 H83 H81
          have o2 := point_equality_decidability TA TM
          rcases o2 with H84 | H84
          · subst H84
            have H86 := length_eq_cong_1_c O E E' b3 b4 b3 b2 TA H62 H30
            exact cong__le_c b3 b4 b3 b2 H86
          · have H85 := lep_neq__ltp_c O E E' TM2 TA2 (⟨HH0, ((fun H85 => H84 ((by
  subst H85
  exact root_uniqueness_c O E E' TA TM TA2 (length_not_neg_c O E E' b3 b2 TA H30) (length_not_neg_c O E E' b3 b4 TM H62) H36 H68))))⟩)
            have H86 := square_increase_rev_c O E E' TM TA TM2 TA2 ((let H86 := length_Ps_c O E E' b3 b4 TM ((fun H86 => (by
  subst H86
  have H88 := length_id_1_c O E E' b3 b4 H62
  have H89 := H78 H88
  exact (H89).elim))) H62; H86)) ((let H86 := length_Ps_c O E E' b3 b2 TA ((fun H86 => (by
  subst H86
  have H88 := length_id_1_c O E E' b3 b2 H30
  subst H88
  have H90 := perp_distinct_c b0 b1 b2 b2 H9
  obtain ⟨_, H91⟩ := H90
  have H92 := (let H92 := rfl; H91 H92)
  exact (H92).elim))) H30; H86)) H85 H68 H36
            exact lt__le_c b3 b4 b3 b2 (ltp_to_lt_c O E E' b3 b4 TM b3 b2 TA H62 H30 H86)
    · obtain ⟨H8, _⟩ := H7
      have HH0 := inter_tangent_circle_c b0 b1 b2 b4 H5 b5
      have H9 := HH0 ((by colr)) b6 b7
      subst H9
      exact le_reflexivity_c b3 b2
theorem inter_circle_obtuse_c :
    ∀ (P Q A T M : Tpoint), Cong P A Q A → Le P M P A → Le Q M Q A → Projp A T P Q → Obtuse P T M ∨ Per P T M → Le T M T A := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  have HH := lower_dim
  have O := PA
  have E := PB
  have E' := PC
  have HD := (fun H4 => HH ((by
  rcases b9 with _ | _
  · rcases H4 with H5 | H5
    · have H6 := fun H6 => HH (Or.inl H6)
      have H7 := fun H7 => HH (Or.inr H7)
      have H8 := H6 H5
      have H9 := fun H9 => H7 (Or.inl H9)
      have H10 := fun H10 => H7 (Or.inr H10)
      exact (H8).elim
    · rcases H5 with H6 | H6
      · have H7 := fun H7 => HH (Or.inl H7)
        have H8 := fun H8 => HH (Or.inr H8)
        have H9 := fun H9 => H8 (Or.inl H9)
        have H10 := fun H10 => H8 (Or.inr H10)
        have H11 := H9 H6
        exact (H11).elim
      · have H7 := fun H7 => HH (Or.inl H7)
        have H8 := fun H8 => HH (Or.inr H8)
        have H9 := fun H9 => H8 (Or.inl H9)
        have H10 := fun H10 => H8 (Or.inr H10)
        have H11 := H10 H6
        exact (H11).elim
  · rcases H4 with H5 | H5
    · have H6 := fun H6 => HH (Or.inl H6)
      have H7 := fun H7 => HH (Or.inr H7)
      have H8 := H6 H5
      have H9 := fun H9 => H7 (Or.inl H9)
      have H10 := fun H10 => H7 (Or.inr H10)
      exact (H8).elim
    · rcases H5 with H6 | H6
      · have H7 := fun H7 => HH (Or.inl H7)
        have H8 := fun H8 => HH (Or.inr H8)
        have H9 := fun H9 => H8 (Or.inl H9)
        have H10 := fun H10 => H8 (Or.inr H10)
        have H11 := H9 H6
        exact (H11).elim
      · have H7 := fun H7 => HH (Or.inl H7)
        have H8 := fun H8 => HH (Or.inr H8)
        have H9 := fun H9 => H8 (Or.inl H9)
        have H10 := fun H10 => H8 (Or.inr H10)
        have H11 := H10 H6
        exact (H11).elim)))
  have o := point_equality_decidability b0 b3
  rcases o with H4 | H4
  · subst H4
    exact b6
  · obtain ⟨H5, H6⟩ := b8
    rcases H6 with H7 | H7
    · obtain ⟨H8, H9⟩ := H7
      have HX := (let H10 := not_col_distincts_c O E E' HD; (let H11 := H10; (by
  obtain ⟨_, H12⟩ := H11
  obtain ⟨H13, H14⟩ := H12
  obtain ⟨_, _⟩ := H14
  have H15 := perp_distinct_c b0 b1 b2 b3 H9
  have H16 := H15
  obtain ⟨_, _⟩ := H16
  exact H13)))
      have H10 := (let H10 := perp_col_c b0 b1 b2 b3 b3 H4 H9 H8; (let H11 := perp_left_comm_c b0 b3 b2 b3 H10; (let H12 := perp_perp_in_c b3 b0 b2 H11; (let H13 := perp_in_comm_c b3 b0 b2 b3 b3 H12; (let H14 := perp_in_per_c b0 b3 b2 H13; H14)))))
      have Py := pyth_context_c O E E' b0 b3 b2 HD
      obtain ⟨PT, H11⟩ := Py
      obtain ⟨TA, H12⟩ := H11
      obtain ⟨AP, H13⟩ := H12
      obtain ⟨PT2, H14⟩ := H13
      obtain ⟨TA2, H15⟩ := H14
      obtain ⟨AP2, H16⟩ := H15
      obtain ⟨SS, H17⟩ := H16
      obtain ⟨H18, H19⟩ := H17
      obtain ⟨_, H20⟩ := H19
      obtain ⟨H21, H22⟩ := H20
      obtain ⟨_, H23⟩ := H22
      obtain ⟨_, H24⟩ := H23
      obtain ⟨_, H25⟩ := H24
      obtain ⟨H26, H27⟩ := H25
      obtain ⟨H28, H29⟩ := H27
      obtain ⟨H30, H31⟩ := H29
      obtain ⟨H32, H33⟩ := H31
      obtain ⟨H34, H35⟩ := H33
      obtain ⟨H36, H37⟩ := H35
      have Py0 := pyth_context_c O E E' b0 b3 b4 HD
      obtain ⟨PT', H38⟩ := Py0
      obtain ⟨TM, H39⟩ := H38
      obtain ⟨PM, H40⟩ := H39
      obtain ⟨PT2', H41⟩ := H40
      obtain ⟨TM2, H42⟩ := H41
      obtain ⟨PM2, H43⟩ := H42
      obtain ⟨SS', H44⟩ := H43
      obtain ⟨H45, H46⟩ := H44
      obtain ⟨H47, H48⟩ := H46
      obtain ⟨H49, H50⟩ := H48
      obtain ⟨H51, H52⟩ := H50
      obtain ⟨H53, H54⟩ := H52
      obtain ⟨H55, H56⟩ := H54
      obtain ⟨H57, H58⟩ := H56
      obtain ⟨H59, H60⟩ := H58
      obtain ⟨H61, H62⟩ := H60
      obtain ⟨H63, H64⟩ := H62
      obtain ⟨H65, H66⟩ := H64
      obtain ⟨H67, H68⟩ := H66
      have H69 := length_uniqueness_c O E E' b0 b3 PT PT' H26 H57
      subst H69
      have H71 := prod_uniqueness_c PT PT PT2 PT2' H32 H63
      subst H71
      have Pyth := pythagoras_c O E E' b0 b2 b3 PT TA AP PT2 TA2 AP2 HX H10 H30 H26 (length_sym_c O E E' b3 b2 TA H28) H32 H34 H36
      have HE := sum_uniqueness_c PT2 TA2 SS AP2 H37 Pyth
      subst HE
      have Pyth1 := pythagoras_obtuse_or_per_c O E E' b0 b4 b3 PT TM PM PT2 TM2 PM2 SS' HX b9 H61 H26 (length_sym_c O E E' b3 b4 TM H59) H32 H65 H67 H68
      have o0 := point_equality_decidability b3 b4
      rcases o0 with H73 | H73
      · subst H73
        exact le_trivial_c b3 b3 b2
      · have o1 := point_equality_decidability b0 b4
        rcases o1 with H74 | H74
        · subst H74
          have HH0 := length_id_2_c O E E' b0 HX
          have H79 := length_uniqueness_c O E E' b0 b0 PM O H61 HH0
          subst H79
          have H81 := prod_O_l_eq_c O E E' O PM2 H67
          subst H81
          have H82 := sum_pos_pos_c O E E' PT2 TM2 SS' (square_pos_c O E E' PT PT2 ((fun H82 => (by
  subst H82
  have H84 := length_cong_c O E E' b0 b3 O H26
  have H85 := cong_identity b0 b3 O H84
  exact ((H4 H85)).elim))) H32) (square_pos_c O E E' TM TM2 ((fun H82 => (by
  subst H82
  have H84 := length_cong_c O E E' b3 b0 O H59
  have H85 := cong_identity b3 b0 O H84
  exact ((H73 H85)).elim))) H65) H68
          rcases Pyth1 with H83 | H83
          · have H84 := ltP_neg_c O E E' SS' H83
            have H85 := pos_not_neg_c O E SS' H82
            exact ((H85 H84)).elim
          · subst H83
            obtain ⟨H85, H86⟩ := H82
            obtain ⟨_, H87⟩ := H86
            rcases b9 with _ | _
            · rcases H87 with _ | _
              · have H88 := (let H88 := rfl; H85 H88)
                exact (H88).elim
              · have H88 := (let H88 := rfl; H85 H88)
                exact (H88).elim
            · rcases H87 with _ | _
              · have H88 := (let H88 := rfl; H85 H88)
                exact (H88).elim
              · have H88 := (let H88 := rfl; H85 H88)
                exact (H88).elim
        · have H75 := length_leP_le_2_c O E E' b0 b4 b0 b2 PM AP H61 H30 b6
          have H76 := square_increase_c O E E' PM AP PM2 AP2 (⟨HD, (⟨H49, (⟨H21, H49⟩)⟩)⟩) ((let H76 := length_pos_or_null_c O E E' b0 b4 PM H61; (by
  rcases H76 with H77 | H77
  · exact H77
  · subst H77
    rcases b9 with _ | _
    · have H80 := (let H80 := rfl; H74 H80)
      exact (H80).elim
    · have H80 := (let H80 := rfl; H74 H80)
      exact (H80).elim))) ((let H76 := length_pos_or_null_c O E E' b0 b2 AP H30; (by
  rcases H76 with H77 | H77
  · exact H77
  · subst H77
    have H84 := (by cong_r)
    have H85 := cong_identity b1 b0 b0 H84
    subst H85
    have H91 := le_zero_c b1 b4 b1 b6
    subst H91
    rcases b9 with _ | _
    · have H93 := (let H93 := rfl; H5 H93)
      exact (H93).elim
    · have H93 := (let H93 := rfl; H5 H93)
      exact (H93).elim))) H75 H67 H36
          have H77 := leP_trans_c O E E' SS' PM2 AP2 Pyth1 H76
          have H78 := sum_preserves_lep_rev_c O E E' TM2 TA2 PT2 SS' AP2 (sum_comm_c PT2 TM2 SS' H68) (sum_comm_c PT2 TA2 AP2 Pyth) H77
          have H79 := (let H79 := length_pos_or_null_c O E E' b3 b4 TM H59; (by
  rcases H79 with H80 | H80
  · exact H80
  · subst H80
    rcases b9 with _ | _
    · have H83 := (let H83 := rfl; H73 H83)
      exact (H83).elim
    · have H83 := (let H83 := rfl; H73 H83)
      exact (H83).elim))
          have H80 := (let H80 := length_pos_or_null_c O E E' b3 b2 TA H28; (by
  rcases H80 with H81 | H81
  · exact H81
  · subst H81
    have H84 := perp_distinct_c b0 b1 b2 b2 H9
    obtain ⟨_, H85⟩ := H84
    rcases b9 with _ | _
    · have H86 := (let H86 := rfl; H85 H86)
      exact (H86).elim
    · have H86 := (let H86 := rfl; H85 H86)
      exact (H86).elim))
          have H81 := (let o2 := point_equality_decidability TM TA; (by
  rcases o2 with H81 | H81
  · subst H81
    exact leP_refl_c O E E' TA
  · exact ltp_to_lep_c O E E' TM TA (square_increase_rev_c O E E' TM TA TM2 TA2 H79 H80 (lep_neq__ltp_c O E E' TM2 TA2 (⟨H78, ((fun H82 => H81 ((by
  subst H82
  exact root_uniqueness_c O E E' TM TA TA2 ((fun H84 => (let H85 := pos_not_neg_c O E TM H79; ((H85 H84)).elim))) ((fun H84 => (let H85 := pos_not_neg_c O E TA H80; ((H85 H84)).elim))) H65 H34))))⟩)) H65 H34)))
          exact length_leP_le_1_c O E E' b3 b4 b3 b2 TM TA H59 H28 H81
    · obtain ⟨H8, _⟩ := H7
      have HH0 := inter_tangent_circle_c b0 b1 b2 b4 H5 b5
      have H9 := HH0 ((by colr)) b6 b7
      subst H9
      exact le_reflexivity_c b3 b2
theorem circle_projp_between_c :
    ∀ (P Q A T : Tpoint), Cong P A Q A → Projp A T P Q → Bet P T Q := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b0 b3
  rcases o with H1 | H1
  · subst H1
    exact between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial2 b0 b1))))
  · obtain ⟨H2, H3⟩ := b5
    rcases H3 with H4 | H4
    · obtain ⟨H5, H6⟩ := H4
      have H7 := (let H7 := perp_col_c b0 b1 b2 b3 b3 H1 H6 H5; (let H8 := perp_left_comm_c b0 b3 b2 b3 H7; (let H9 := perp_perp_in_c b3 b0 b2 H8; (let H10 := perp_in_comm_c b3 b0 b2 b3 b3 H9; (let H11 := perp_in_per_c b0 b3 b2 H10; l8_2_c b0 b3 b2 H11)))))
      have HM := midpoint_existence_c b0 b1
      obtain ⟨T', H8⟩ := HM
      have H9 := ⟨b1, (⟨H8, ((by cong_r))⟩)⟩
      have H10 := col_per2_cases_c b2 T' b0 b1 b3 ((fun H10 => (by
  subst H10
  have H18 := is_midpoint_id_c T' b1 H8
  subst H18
  have H21 := perp_distinct_c b1 b1 b2 b3 H6
  obtain ⟨H22, _⟩ := H21
  have H23 := (let H23 := rfl; H2 H23)
  have H25 := (let H25 := rfl; H22 H25)
  exact (H23).elim))) (Ne.symm H1) H2 (midpoint_col_c b0 T' b1 H8) H9 H7
      rcases H10 with H11 | H11
      · subst H11
        exact midpoint_bet_c b0 b3 b1 H8
      · have H12 := col_perp2_ncol__col_c b2 b3 b2 T' b0 b1 (perp_comm_c b3 b2 b1 b0 (perp_comm_c b2 b3 b0 b1 (perp_sym_c b0 b1 b2 b3 H6))) ((let H12 := per_perp_in_c b2 T' b0 ((fun H12 => (by
  subst H12
  obtain ⟨H14, _⟩ := H8
  exact H11 ((let H15 := bet_col_c b0 b2 b1 H14; (by colr)))))) ((fun H12 => (by
  subst H12
  have H14 := is_midpoint_id_c b0 b1 H8
  exact ((H2 H14)).elim))) H9; (let H13 := perp_in_comm_c b2 T' T' b0 T' H12; (let H14 := perp_in_perp_c T' b2 b0 T' T' H13; (let H15 := perp_sym_c T' b2 b0 T' H14; perp_sym_c b0 b1 b2 T' (perp_col_c b0 T' b2 T' b1 H2 (perp_comm_c T' b0 T' b2 (perp_comm_c b0 T' b2 T' (perp_comm_c T' b0 T' b2 (perp_left_comm_c b0 T' T' b2 H15)))) ((by colr)))))))) ((by colr)) ((fun _ => H11 ((let H12 := midpoint_col_c b0 T' b1 H8; (by colr)))))
        have H13 := per2_col_eq_c ((fun H13 => (by
  subst H13
  obtain ⟨H15, _⟩ := H8
  exact H11 ((let H16 := bet_col_c b0 b2 b1 H15; (by colr)))))) H7 H9 H12
        subst H13
        exact midpoint_bet_c b0 b3 b1 H8
    · obtain ⟨H5, H6⟩ := H4
      subst H6
      have H7 := l7_20_c b2 b0 b1 ((by colr)) ((by cong_r))
      rcases H7 with H8 | H8
      · exact ((H2 H8)).elim
      · exact midpoint_bet_c b0 b2 b1 H8
theorem inter_circle_c :
    ∀ (P Q A T M : Tpoint), Cong P A Q A → Le P M P A → Le Q M Q A → Projp A T P Q → Le T M T A := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8
  have HH := circle_projp_between_c b0 b1 b2 b3 b5 b8
  have o := point_equality_decidability b3 b4
  rcases o with H3 | H3
  · subst H3
    exact le_trivial_c b3 b3 b2
  · have o0 := point_equality_decidability b0 b3
    rcases o0 with H4 | H4
    · subst H4
      exact b6
    · have HA := angle_partition_c b0 b3 b4 H4 H3
      have o1 := point_equality_decidability b1 b3
      rcases o1 with H5 | H5
      · subst H5
        exact b7
      · rcases HA with H6 | H6
        · have HB := acute_bet__obtuse_c b0 b3 b4 b1 HH H5 H6
          exact inter_circle_obtuse_c b1 b0 b2 b3 b4 ((by cong_r)) b7 b6 ((by
  obtain ⟨H7, H8⟩ := b8
  exact ⟨(Ne.symm H7), ((by
  rcases H8 with H9 | H9
  · exact Or.inl ((by
  obtain ⟨H10, H11⟩ := H9
  exact ⟨((by colr)), (perp_comm_c b0 b1 b3 b2 (perp_comm_c b1 b0 b2 b3 (perp_comm_c b0 b1 b3 b2 (perp_right_comm_c b0 b1 b2 b3 H11))))⟩))
  · exact Or.inr ((by
  obtain ⟨H10, H11⟩ := H9
  exact ⟨((by colr)), H11⟩))))⟩)) (Or.inl HB)
        · exact inter_circle_obtuse_c b0 b1 b2 b3 b4 b5 b6 b7 b8 ((by
  rcases H6 with H7 | H7
  · exact Or.inr H7
  · exact Or.inl H7))
theorem projp_lt_c :
    ∀ (P Q A T : Tpoint), Cong P A Q A → Projp A T P Q → Lt T A P A := by
  intro b0 b1 b2 b3 b4 b5
  obtain ⟨H1, H2⟩ := b5
  rcases H2 with H3 | H3
  · obtain ⟨H4, H5⟩ := H3
    have o := point_equality_decidability b0 b3
    rcases o with H6 | H6
    · subst H6
      have H8 := per_lt_c b1 b0 b2 (Ne.symm H1) ((let H8 := perp_distinct_c b0 b1 b2 b0 H5; (fun H9 => (by
  obtain ⟨_, H10⟩ := H8
  have H11 := H10 H9
  exact (H11).elim)))) (perp_in_per_c b1 b0 b2 (perp_in_left_comm_c b0 b1 b0 b2 b0 (perp_in_right_comm_c b0 b1 b2 b0 b0 (perp_perp_in_c b0 b1 b2 H5))))
      obtain ⟨_, H9⟩ := H8
      obtain ⟨_, H10⟩ := H9
      exact ((H10 ((by cong_r)))).elim
    · have H7 := per_lt_c b0 b3 b2 H6 ((let H7 := perp_distinct_c b0 b1 b2 b3 H5; (fun H8 => (by
  obtain ⟨_, H9⟩ := H7
  have H10 := H9 H8
  exact (H10).elim)))) ((let H7 := perp_col_c b0 b1 b2 b3 b3 H6 H5 H4; perp_in_per_c b0 b3 b2 (perp_in_comm_c b3 b0 b2 b3 b3 (perp_perp_in_c b3 b0 b2 (perp_left_comm_c b0 b3 b2 b3 H7)))))
      obtain ⟨_, H8⟩ := H7
      exact lt_left_comm_c b2 b3 b0 b2 H8
  · obtain ⟨H4, H5⟩ := H3
    subst H5
    have o := point_equality_decidability b0 b2
    rcases o with H6 | H6
    · subst H6
      have H10 := (by cong_r)
      have H11 := cong_identity b1 b2 b2 H10
      subst H11
      have H13 := (let H13 := rfl; H1 H13)
      exact (H13).elim
    · exact lt1123_c b2 b0 b2 H6

#print axioms GeocoqTranslate.Tarski.Base.length_pos_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_2_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_c
#print axioms GeocoqTranslate.Tarski.Base.length_eq_cong_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_eq_cong_2_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_pos_c
#print axioms GeocoqTranslate.Tarski.Base.bet_leP_c
#print axioms GeocoqTranslate.Tarski.Base.leP_bet_c
#print axioms GeocoqTranslate.Tarski.Base.length_Ar2_c
#print axioms GeocoqTranslate.Tarski.Base.length_leP_le_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_leP_le_2_c
#print axioms GeocoqTranslate.Tarski.Base.l15_3_c
#print axioms GeocoqTranslate.Tarski.Base.length_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.length_cong_c
#print axioms GeocoqTranslate.Tarski.Base.length_Ps_c
#print axioms GeocoqTranslate.Tarski.Base.length_not_col_null_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.not_triangular_equality1_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_c
#print axioms GeocoqTranslate.Tarski.Base.length_O_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_bis_c
#print axioms GeocoqTranslate.Tarski.Base.length_out_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_bet1_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.project_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.conga_bet_conga_c
#print axioms GeocoqTranslate.Tarski.Base.thales_c
#print axioms GeocoqTranslate.Tarski.Base.length_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_1_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_2_c
#print axioms GeocoqTranslate.Tarski.Base.length_sym_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_c
#print axioms GeocoqTranslate.Tarski.Base.is_length_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lt_to_ltp_c
#print axioms GeocoqTranslate.Tarski.Base.ltp_to_lep_c
#print axioms GeocoqTranslate.Tarski.Base.ltp_to_lt_c
#print axioms GeocoqTranslate.Tarski.Base.prod_col_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_strict_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_c
#print axioms GeocoqTranslate.Tarski.Base.signeq__prod_pos_c
#print axioms GeocoqTranslate.Tarski.Base.pos_neg__prod_neg_c
#print axioms GeocoqTranslate.Tarski.Base.sign_dec_c
#print axioms GeocoqTranslate.Tarski.Base.not_signEq_prod_neg_c
#print axioms GeocoqTranslate.Tarski.Base.prod_pos__signeq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_ng___not_signeq_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__diff_pos_c
#print axioms GeocoqTranslate.Tarski.Base.diff_pos__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_rev_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__ltps_c
#print axioms GeocoqTranslate.Tarski.Base.ltps__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__lep_neq_c
#print axioms GeocoqTranslate.Tarski.Base.lep_neq__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_rev_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_rev_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_lea__le_c
#print axioms GeocoqTranslate.Tarski.Base.lea_out_lea_c
#print axioms GeocoqTranslate.Tarski.Base.lta_out_lta_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_obtuse_or_per_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_acute_c
#print axioms GeocoqTranslate.Tarski.Base.pyth_context_c
#print axioms GeocoqTranslate.Tarski.Base.length_pos_or_null_c
#print axioms GeocoqTranslate.Tarski.Base.not_neg_pos_c
#print axioms GeocoqTranslate.Tarski.Base.sum_pos_null_c
#print axioms GeocoqTranslate.Tarski.Base.length_not_neg_c
#print axioms GeocoqTranslate.Tarski.Base.signEq_refl_c
#print axioms GeocoqTranslate.Tarski.Base.square_not_neg_c
#print axioms GeocoqTranslate.Tarski.Base.root_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.inter_tangent_circle_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_per_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.circle_projp_between_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_c
#print axioms GeocoqTranslate.Tarski.Base.projp_lt_c
end GeocoqTranslate.Tarski.Base
#print axioms GeocoqTranslate.Tarski.Base.length_pos_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_2_c
#print axioms GeocoqTranslate.Tarski.Base.length_id_c
#print axioms GeocoqTranslate.Tarski.Base.length_eq_cong_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_eq_cong_2_c
#print axioms GeocoqTranslate.Tarski.Base.ltP_pos_c
#print axioms GeocoqTranslate.Tarski.Base.bet_leP_c
#print axioms GeocoqTranslate.Tarski.Base.leP_bet_c
#print axioms GeocoqTranslate.Tarski.Base.length_Ar2_c
#print axioms GeocoqTranslate.Tarski.Base.length_leP_le_1_c
#print axioms GeocoqTranslate.Tarski.Base.length_leP_le_2_c
#print axioms GeocoqTranslate.Tarski.Base.l15_3_c
#print axioms GeocoqTranslate.Tarski.Base.length_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.length_cong_c
#print axioms GeocoqTranslate.Tarski.Base.length_Ps_c
#print axioms GeocoqTranslate.Tarski.Base.length_not_col_null_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_equiv_c
#print axioms GeocoqTranslate.Tarski.Base.not_triangular_equality1_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_c
#print axioms GeocoqTranslate.Tarski.Base.length_O_c
#print axioms GeocoqTranslate.Tarski.Base.triangular_equality_bis_c
#print axioms GeocoqTranslate.Tarski.Base.length_out_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_bet1_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_col_c
#print axioms GeocoqTranslate.Tarski.Base.image_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.project_preserves_out_c
#print axioms GeocoqTranslate.Tarski.Base.conga_bet_conga_c
#print axioms GeocoqTranslate.Tarski.Base.thales_c
#print axioms GeocoqTranslate.Tarski.Base.length_existence_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_1_c
#print axioms GeocoqTranslate.Tarski.Base.l15_7_2_c
#print axioms GeocoqTranslate.Tarski.Base.length_sym_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_c
#print axioms GeocoqTranslate.Tarski.Base.is_length_exists_c
#print axioms GeocoqTranslate.Tarski.Base.lt_to_ltp_c
#print axioms GeocoqTranslate.Tarski.Base.ltp_to_lep_c
#print axioms GeocoqTranslate.Tarski.Base.ltp_to_lt_c
#print axioms GeocoqTranslate.Tarski.Base.prod_col_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_strict_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_c
#print axioms GeocoqTranslate.Tarski.Base.signeq__prod_pos_c
#print axioms GeocoqTranslate.Tarski.Base.pos_neg__prod_neg_c
#print axioms GeocoqTranslate.Tarski.Base.sign_dec_c
#print axioms GeocoqTranslate.Tarski.Base.not_signEq_prod_neg_c
#print axioms GeocoqTranslate.Tarski.Base.prod_pos__signeq_c
#print axioms GeocoqTranslate.Tarski.Base.prod_ng___not_signeq_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__diff_pos_c
#print axioms GeocoqTranslate.Tarski.Base.diff_pos__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_rev_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__ltps_c
#print axioms GeocoqTranslate.Tarski.Base.ltps__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.ltp__lep_neq_c
#print axioms GeocoqTranslate.Tarski.Base.lep_neq__ltp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_rev_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_rev_c
#print axioms GeocoqTranslate.Tarski.Base.cong2_lea__le_c
#print axioms GeocoqTranslate.Tarski.Base.lea_out_lea_c
#print axioms GeocoqTranslate.Tarski.Base.lta_out_lta_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_obtuse_or_per_c
#print axioms GeocoqTranslate.Tarski.Base.pythagoras_acute_c
#print axioms GeocoqTranslate.Tarski.Base.pyth_context_c
#print axioms GeocoqTranslate.Tarski.Base.length_pos_or_null_c
#print axioms GeocoqTranslate.Tarski.Base.not_neg_pos_c
#print axioms GeocoqTranslate.Tarski.Base.sum_pos_null_c
#print axioms GeocoqTranslate.Tarski.Base.length_not_neg_c
#print axioms GeocoqTranslate.Tarski.Base.signEq_refl_c
#print axioms GeocoqTranslate.Tarski.Base.square_not_neg_c
#print axioms GeocoqTranslate.Tarski.Base.root_uniqueness_c
#print axioms GeocoqTranslate.Tarski.Base.inter_tangent_circle_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_per_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_obtuse_c
#print axioms GeocoqTranslate.Tarski.Base.circle_projp_between_c
#print axioms GeocoqTranslate.Tarski.Base.inter_circle_c
#print axioms GeocoqTranslate.Tarski.Base.projp_lt_c
end GeocoqTranslate.Tarski.Base