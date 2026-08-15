/-
Angle-congruence (`CongA`) automation, mirroring `Tcol`/`Tcong`/`Tbet` in
`AesopRuleSets.lean` + `tarski_tactics.lean`.

Not folded into `TarskiFinish.lean` (kept self-contained by design, no Ch11
dependency) or `tarski_tactics.lean` (pulls in the legacy `Ch03_bet.lean`,
which shadows real `Ch03.lean` names like `bet_col`/`bet_col_c` -- a trap
already hit twice this session). This file imports `Ch11` directly instead,
declares its own `Tconga` rule-set, and defines `TfinishA` ("Tfinish +
Angle") as the combined closer for goals involving `CongA`.
-/
import GeocoqTranslate.Tarski_dev.Ch11
import GeocoqTranslate.Tarski_dev.TarskiFinish
import GeocoqTranslate.Tarski_dev.ConARuleSet

namespace GeocoqTranslate.Tarski.Base

attribute [aesop unsafe 50% forward (rule_sets := [Tconga])]
  conga_sym_c conga_comm_c conga_left_comm_c conga_right_comm_c conga_trans_c

-- Widened 2026-07-14 for the upper-chapter (Ch12+) sorry-backlog sweep: the
-- original 5-lemma set only covered CongA's own algebraic closure
-- (sym/comm/trans), so `aesop (rule_sets := [Tconga])` never fired on goals
-- that BRIDGE CongA to LeA/LtA/InAngle, which is most of what later chapters
-- actually need. All of these are independently kernel-clean in Ch11.lean.
attribute [aesop unsafe 50% forward (rule_sets := [Tconga])]
  conga_refl_c conga_pseudo_refl_c conga_trivial_1_c out2_conga_c
  conga_lea_c conga_lea456123_c
  lea_refl_c lea_comm_c lea_left_comm_c lea_right_comm_c lea_trans_c
  lta_comm_c lta_left_comm_c lta_right_comm_c lta_trans_c
  inangle_lea_c inangle_lea_1_c inangle2_lea_c
  lea_nlta_c lta_nlea_c lta_lea_c
  lea_out4_lea_c lea121345_c lea123456_lta_lta_c lea456789_lta_lta_c
  l11_10_c

end GeocoqTranslate.Tarski.Base

namespace GeocoqTranslate.Tarski

/-- `Tfinish` extended with angle-congruence closure (`Tconga`). Adds
`subst_vars`/`tauto` as generic degenerate-case fallbacks (equality
case-splits collapsing via substitution, or a purely propositional
finish) -- cheap, no legacy-chain dependency, catches the
`point_equality_decidability`-then-trivial shape seen repeatedly in
Ch11's own det_attempt output (e.g. `l11_60_c`, `triangle_inequality_c`). -/
macro "TfinishA" : tactic =>
  `(tactic|
    first
      | assumption
      | colr
      | cong_r
      | assert_diffs
      | aesop (rule_sets := [Tconga])
      | (subst_vars; first | assumption | colr | cong_r | tauto)
      | tauto)

end GeocoqTranslate.Tarski
