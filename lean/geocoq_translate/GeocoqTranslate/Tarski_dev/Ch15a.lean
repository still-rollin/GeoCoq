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
  have H3 : Cong b3 b4 b0 b0 := (by cong_r)
  have H4 := cong_identity b3 b4 b0 H3
  rw [H4] at *
  exact rfl
theorem length_id_2_c :
    ∀ (O E E' A : Tpoint), O ≠ E → Length O E E' A A O :=
  fun b0 b1 b2 b3 b4 =>
  ⟨b4, (⟨(col_trivial_3_c b0 b1), (⟨(Or.inr rfl), (cong_trivial_identity b0 b3)⟩)⟩)⟩
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
  rw [H0] at *
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
    ∀ (O E E' A : Tpoint), LtP O E E' O A → Ps O E A := sorry

theorem bet_leP_c :
    ∀ (O E E' AB CD : Tpoint), Bet O AB CD → LeP O E E' O AB → LeP O E E' O CD → LeP O E E' AB CD := sorry

theorem leP_bet_c :
    ∀ (O E E' AB CD : Tpoint), LeP O E E' AB CD → LeP O E E' O AB → LeP O E E' O CD → Bet O AB CD := sorry

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
  have H15 : Cong b3 b4 b5 M := (by cong_r)
  exact le_transitivity_c b3 b4 b5 M b5 b6 (⟨M, (⟨(between_symmetry (between_symmetry (between_symmetry (between_symmetry (between_trivial b5 M))))), H15⟩)⟩) ((let H16 : Le b0 b7 b0 b8 := ⟨b7, (⟨H10, ((by cong_r))⟩)⟩; l5_6_c b0 b7 b0 b8 b5 M b5 b6 H16 ((by cong_r)) H5))
theorem length_leP_le_2_c :
    ∀ (O E E' A B C D AB CD : Tpoint), Length O E E' A B AB → Length O E E' C D CD → Le A B C D → LeP O E E' AB CD := sorry

theorem l15_3_c :
    ∀ (O E E' A B C : Tpoint), Sum O E E' A B C → Cong O B A C := sorry

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
    ∀ (O E E' A B AB : Tpoint), AB ≠ O → Length O E E' A B AB → Ps O E AB := sorry

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
    ∀ (O E E' A B C AB BC AC : Tpoint), O ≠ E → Bet A B C → Is_length O E E' A B AB → Is_length O E E' B C BC → Is_length O E E' A C AC → Sumg O E E' AB BC AC := sorry

theorem length_O_c :
    ∀ (O E E' : Tpoint), O ≠ E → Length O E E' O O O :=
  fun b0 b1 b2 b3 =>
  ⟨b3, (⟨(col_trivial_3_c b0 b1), (⟨(Or.inr rfl), ((by cong_r))⟩)⟩)⟩
theorem triangular_equality_bis_c :
    ∀ (O E E' A B C AB BC AC : Tpoint), A ≠ B ∨ A ≠ C ∨ B ≠ C → O ≠ E → Bet A B C → Length O E E' A B AB → Length O E E' B C BC → Length O E E' A C AC → Sum O E E' AB BC AC := sorry

theorem length_out_c :
    ∀ (O E E' A B C D AB CD : Tpoint), A ≠ B → C ≠ D → Length O E E' A B AB → Length O E E' C D CD → Out O AB CD := sorry

theorem image_preserves_bet1_c :
    ∀ (X Y A B C A' B' C' : Tpoint), Bet A B C → Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Bet A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  have o := point_equality_decidability b0 b1
  rcases o with H3 | H3
  · rw [H3] at *
    rcases b9 with H7 | H7
    · obtain ⟨H8, _⟩ := H7
      rcases b11 with H9 | H9
      · obtain ⟨H10, _⟩ := H9
        rcases b10 with H11 | H11
        · obtain ⟨H12, _⟩ := H11
          have H13 := (let H13 := rfl; H8 H13)
          have H15 := (let H15 := rfl; H10 H15)
          have H16 := (let H16 := rfl; H12 H16)
          exact (H13).elim
        · obtain ⟨H12, _⟩ := H11
          have H13 := H8 H12
          have H14 := H10 H12
          exact (H13).elim
      · obtain ⟨H10, _⟩ := H9
        rcases b10 with H11 | H11
        · obtain ⟨H12, _⟩ := H11
          have H13 := H8 H10
          have H14 := H12 H10
          exact (H13).elim
        · obtain ⟨_, _⟩ := H11
          have H12 := H8 H10
          exact (H12).elim
    · rcases b10 with H8 | H8
      · obtain ⟨H9, _⟩ := H8
        obtain ⟨H10, _⟩ := H7
        rcases b11 with H11 | H11
        · obtain ⟨H12, _⟩ := H11
          have H13 := H9 H10
          have H14 := H12 H10
          exact (H13).elim
        · obtain ⟨_, _⟩ := H11
          have H12 := H9 H10
          exact (H12).elim
      · rcases b11 with H9 | H9
        · obtain ⟨H10, _⟩ := H9
          obtain ⟨H11, _⟩ := H8
          obtain ⟨_, _⟩ := H7
          have H12 := H10 H11
          exact (H12).elim
        · obtain ⟨_, H10⟩ := H7
          obtain ⟨_, H11⟩ := H8
          obtain ⟨_, H12⟩ := H9
          exact l7_15_c b2 b3 b4 b5 b6 b7 b0 (l7_2_c b0 b5 b2 H10) (l7_2_c b0 b6 b3 H11) (l7_2_c b0 b7 b4 H12) b8
  · exact image_preserves_bet_c b2 b3 b4 b5 b6 b7 b0 b1 ((by
  rcases b9 with H4 | H4
  · obtain ⟨_, H5⟩ := H4
    exact H5
  · obtain ⟨H5, _⟩ := H4
    exact ((H3 H5)).elim)) ((by
  rcases b9 with H4 | H4
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨_, H7⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact H7
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨H7, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim)) ((by
  rcases b9 with H4 | H4
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, H7⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact H7
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨H7, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim)) ((by
  rcases b9 with H4 | H4
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact b8
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
  · rcases b10 with H5 | H5
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨H7, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
    · rcases b11 with H6 | H6
      · obtain ⟨_, _⟩ := H6
        obtain ⟨H7, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim
      · obtain ⟨H7, _⟩ := H6
        obtain ⟨_, _⟩ := H5
        obtain ⟨_, _⟩ := H4
        exact ((H3 H7)).elim))
theorem image_preserves_out_c :
    ∀ (X Y A B C A' B' C' : Tpoint), Out A B C → Reflect A A' X Y → Reflect B B' X Y → Reflect C C' X Y → Out A' B' C' := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  obtain ⟨H3, H4⟩ := b8
  obtain ⟨H5, H6⟩ := H4
  exact ⟨((fun H7 => (by
  rw [H7] at *
  have H9 := l10_2_uniqueness_c b0 b1 b5 b3 b2 b10 b9
  exact ((H3 H9)).elim))), (⟨((fun H7 => (by
  rw [H7] at *
  have H9 := l10_2_uniqueness_c b0 b1 b5 b4 b2 b11 b9
  exact ((H5 H9)).elim))), ((by
  rcases H6 with H7 | H7
  · exact Or.inl (image_preserves_bet1_c b0 b1 b2 b3 b4 b5 b6 b7 H7 b9 b10 b11)
  · exact Or.inr (image_preserves_bet1_c b0 b1 b2 b4 b3 b5 b7 b6 H7 b9 b11 b10)))⟩)⟩
theorem project_preserves_out_c :
    ∀ (A B C A' B' C' P Q X Y : Tpoint), Out A B C → ¬ Par A B X Y → Proj A A' P Q X Y → Proj B B' P Q X Y → Proj C C' P Q X Y → Out A' B' C' := sorry

theorem conga_bet_conga_c :
    ∀ (A B C D E F A' C' D' F' : Tpoint), CongA A B C D E F → A' ≠ B → C' ≠ B → D' ≠ E → F' ≠ E → Bet A B A' → Bet C B C' → Bet D E D' → Bet F E F' → CongA A' B C' D' E F' := sorry

theorem thales_c :
    ∀ (O E E' P A B C D A1 B1 C1 D1 AD : Tpoint), O ≠ E → Col P A B → Col P C D → ¬ Col P A C → Pj A C B D → Length O E E' P A A1 → Length O E E' P B B1 → Length O E E' P C C1 → Length O E E' P D D1 → Prodg O E E' A1 D1 AD → Prodg O E E' C1 B1 AD := sorry

theorem length_existence_c :
    ∀ (O E E' A B : Tpoint), ¬ Col O E E' → ∃ (AB : Tpoint), Length O E E' A B AB := sorry

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
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 : Tpoint), O ≠ E → Per A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 AB2 := sorry

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
    ∀ (O E E' A B L C D M : Tpoint), Length O E E' A B L → Length O E E' C D M → Lt A B C D → LtP O E E' L M := sorry

theorem ltp_to_lep_c :
    ∀ (O E E' L M : Tpoint), LtP O E E' L M → LeP O E E' L M :=
  fun b0 b1 b2 b3 b4 b5 =>
  Or.inl b5
theorem ltp_to_lt_c :
    ∀ (O E E' A B L C D M : Tpoint), Length O E E' A B L → Length O E E' C D M → LtP O E E' L M → Lt A B C D := sorry

theorem prod_col_c :
    ∀ (O E E' A B AB : Tpoint), Ar2 O E E' A B A → Prod O E E' A B AB → Col O E AB := by
  intro b0 b1 b2 b3 b4 b5 b6 b7
  obtain ⟨H0, _⟩ := b7
  obtain ⟨_, H3⟩ := H0
  obtain ⟨_, H4⟩ := H3
  obtain ⟨_, H5⟩ := H4
  exact H5
theorem square_increase_strict_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ar2 O E E' A B A → Ps O E A → Ps O E B → LtP O E E' A B → Prod O E E' A A A2 → Prod O E E' B B B2 → LtP O E E' A2 B2 := sorry

theorem square_increase_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ar2 O E E' A B A → Ps O E A → Ps O E B → LeP O E E' A B → Prod O E E' A A A2 → Prod O E E' B B B2 → LeP O E E' A2 B2 := sorry

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
    ∀ (O E E' A B C : Tpoint), A ≠ O → B ≠ O → ¬ SignEq O E A B → Prod O E E' A B C → Ng O E C := sorry

theorem square_increase_rev_c :
    ∀ (O E E' A B A2 B2 : Tpoint), Ps O E A → Ps O E B → LtP O E E' A2 B2 → Prod O E E' A A A2 → Prod O E E' B B B2 → LtP O E E' A B := sorry

theorem sum_preserves_ltp_c :
    ∀ (O E E' A B C AC BC : Tpoint), LtP O E E' A B → Sum O E E' A C AC → Sum O E E' B C BC → LtP O E E' AC BC := sorry

theorem sum_preserves_lep_c :
    ∀ (O E E' A B C AC BC : Tpoint), LeP O E E' A B → Sum O E E' A C AC → Sum O E E' B C BC → LeP O E E' AC BC := sorry

theorem sum_preserves_ltp_rev_c :
    ∀ (O E E' A B C AC BC : Tpoint), Sum O E E' A C AC → Sum O E E' B C BC → LtP O E E' AC BC → LtP O E E' A B := sorry

theorem sum_preserves_lep_rev_c :
    ∀ (O E E' A B C AC BC : Tpoint), Sum O E E' A C AC → Sum O E E' B C BC → LeP O E E' AC BC → LeP O E E' A B := sorry

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
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Obtuse A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LtP O E E' S2 AB2 := sorry

theorem pythagoras_obtuse_or_per_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Obtuse A C B ∨ Per A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LeP O E E' S2 AB2 := sorry

theorem pythagoras_acute_c :
    ∀ (O E E' A B C AC BC AB AC2 BC2 AB2 S2 : Tpoint), O ≠ E → Acute A C B → Length O E E' A B AB → Length O E E' A C AC → Length O E E' B C BC → Prod O E E' AC AC AC2 → Prod O E E' BC BC BC2 → Prod O E E' AB AB AB2 → Sum O E E' AC2 BC2 S2 → LtP O E E' AB2 S2 := sorry

theorem pyth_context_c :
    ∀ (O E E' A B C : Tpoint), ¬ Col O E E' → ∃ (AB BC AC AB2 BC2 AC2 SS : Tpoint), Col O E AB ∧ Col O E BC ∧ Col O E AC ∧ Col O E AB2 ∧ Col O E BC2 ∧ Col O E AC2 ∧ Length O E E' A B AB ∧ Length O E E' B C BC ∧ Length O E E' A C AC ∧ Prod O E E' AB AB AB2 ∧ Prod O E E' BC BC BC2 ∧ Prod O E E' AC AC AC2 ∧ Sum O E E' AB2 BC2 SS := sorry

theorem length_pos_or_null_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → Ps O E AB ∨ A = B := sorry

theorem not_neg_pos_c :
    ∀ (O E A : Tpoint), E ≠ O → Col O E A → ¬ Ng O E A → Ps O E A ∨ A = O := by
  intro b0 b1 b2 b3 b4 b5
  have o := point_equality_decidability b2 b0
  rcases o with H2 | H2
  · exact Or.inr H2
  · exact Or.inl (l6_4_2_c b2 b1 b0 (⟨((by colr)), ((fun H3 => b5 (⟨H2, (⟨b3, H3⟩)⟩)))⟩))
theorem sum_pos_null_c :
    ∀ (O E E' A B : Tpoint), ¬ Ng O E A → ¬ Ng O E B → Sum O E E' A B O → A = O ∧ B = O := sorry

theorem length_not_neg_c :
    ∀ (O E E' A B AB : Tpoint), Length O E E' A B AB → ¬ Ng O E AB := sorry

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
    ∀ (O E E' A A2 : Tpoint), Prod O E E' A A A2 → ¬ Ng O E A2 := sorry

theorem root_uniqueness_c :
    ∀ (O E E' A B C : Tpoint), ¬ Ng O E A → ¬ Ng O E B → Prod O E E' A A C → Prod O E E' B B C → A = B := sorry

theorem inter_tangent_circle_c :
    ∀ (P Q O M : Tpoint), P ≠ Q → Cong P O Q O → Col P O Q → Le P M P O → Le Q M Q O → M = O := sorry

theorem inter_circle_per_c :
    ∀ (P Q A T M : Tpoint), Cong P A Q A → Le P M P A → Le Q M Q A → Projp A T P Q → Per P T M → Le T M T A := sorry

theorem inter_circle_obtuse_c :
    ∀ (P Q A T M : Tpoint), Cong P A Q A → Le P M P A → Le Q M Q A → Projp A T P Q → Obtuse P T M ∨ Per P T M → Le T M T A := sorry

theorem circle_projp_between_c :
    ∀ (P Q A T : Tpoint), Cong P A Q A → Projp A T P Q → Bet P T Q := sorry

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
        · have HB := acute_bet_obtuse_c b0 b3 b4 b1 HH H5 H6
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
    ∀ (P Q A T : Tpoint), Cong P A Q A → Projp A T P Q → Lt T A P A := sorry

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
#print axioms GeocoqTranslate.Tarski.Base.sign_dec_c
#print axioms GeocoqTranslate.Tarski.Base.not_signEq_prod_neg_c
#print axioms GeocoqTranslate.Tarski.Base.square_increase_rev_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_ltp_rev_c
#print axioms GeocoqTranslate.Tarski.Base.sum_preserves_lep_rev_c
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