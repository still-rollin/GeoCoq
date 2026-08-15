/-
Aesop rule-set declaration for angle-congruence (`CongA`) automation.
Mirrors `AesopRuleSets.lean`'s `[Tcol, Tcong, Tbet]` -- kept in its own file
for the same reason: a `declare_aesop_rule_sets` rule set only becomes
visible to `attribute […]`/`aesop (rule_sets := …)` in files that import
this one, never in the file that declares it.
-/
import Aesop

declare_aesop_rule_sets [Tconga]
