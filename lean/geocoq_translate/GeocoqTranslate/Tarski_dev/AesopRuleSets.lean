/-
Aesop rule-set declarations for the Tarski automation tactics.

These MUST live in their own file: Aesop rule sets only become visible to
`attribute […]` registration and `aesop (rule_sets := …)` *after* the
declaring file is imported. `tarski_tactics.lean` imports this and populates
the sets.
-/
import Aesop

declare_aesop_rule_sets [Tcol, Tcong, Tbet]
