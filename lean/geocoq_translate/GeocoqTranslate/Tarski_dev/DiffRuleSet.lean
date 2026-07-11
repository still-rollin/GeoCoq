/-
Aesop rule-set declaration for the `assert_diffs` distinctness rules.

Must live in its own file: a declared aesop rule set only becomes visible to
`attribute [...]` registration and `aesop (rule_sets := …)` *after* the declaring
file is imported. `TarskiDiffs.lean` imports this and populates the set.
-/
import Aesop

declare_aesop_rule_sets [TarskiDiffs]
