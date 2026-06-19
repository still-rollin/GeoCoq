/-
Lean port of `theories/Elements/OriginalProofs/euclidean_tactics.v` together with
the `general_tactics.v` helpers it builds on.

Purpose: let translated Elements proofs mirror their GeoCoq originals
line-for-line, e.g.

  Coq : assert (OutCirc D K) by (conclude_def OutCirc).
  Lean: have : OutCirc D K := by conclude_def OutCirc

The heavy lifting (existential introduction with unification-determined
witnesses, conjunction splitting, backtracking lemma application) is delegated
to `aesop` / `solve_by_elim`, which were verified to discharge the GeoCoq
`remove_exists; eauto` goals.
-/
import Mathlib.Tactic
import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs

namespace GeocoqTranslate.Elements

open Classical euclidean_neutral_basis euclidean_neutral

/- Let `aesop` see through the derived geometry predicates, so that
   `conclude_def` / `close` can build or destruct them even when one predicate
   is defined via another (e.g. `Triangle := nCol`). Mirrors GeoCoq's
   transparent `unfold` of these definitions. -/
attribute [aesop norm unfold]
  euclidean_neutral_basis.nCol euclidean_neutral_basis.Col
  euclidean_neutral_basis.Triangle euclidean_neutral_basis.OnCirc
  euclidean_neutral_basis.InCirc euclidean_neutral_basis.OutCirc
  euclidean_neutral_basis.Cong_3 euclidean_neutral_basis.TS
  equilateral Lt Out TG Midpoint Per Supp CongA Perp_at Perp InAngle OS
  isosceles Cut Meet CR LtA TT RT TP Par SumA PG SQ RE

/-! ## Compatibility shims

GeoCoq common notions that Lean folds into built-ins. Provided as named lemmas
so the translation can reference them 1:1 (`conclude cn_equalityreflexive`). -/

/-- GeoCoq `cn_equalityreflexive : eq A A`. In Lean, `=` reflexivity. -/
theorem cn_equalityreflexive {Point : Type} (A : Point) : A = A := rfl

/-- GeoCoq `cn_equalitytransitive`. In Lean, `=` transitivity. -/
theorem cn_equalitytransitive {Point : Type} (A B C : Point) :
    A = B → B = C → A = C := fun h g => h.trans g

/-- GeoCoq `cn_equalitysub` — substitution of equals (Leibniz). Lets `conclude`
    resolve the name; the concrete goal is closed by `subst`/`aesop`. -/
theorem cn_equalitysub {Point : Type} {p : Point → Prop} {A B : Point} :
    A = B → p A → p B := fun h pa => h ▸ pa

/-! ## General tactics (`general_tactics.v`) -/

/-- GeoCoq `spliter`: destruct every conjunction in the context. -/
macro "spliter" : tactic => `(tactic| casesm* _ ∧ _)

/-- GeoCoq `remove_double_neg`: rewrite `¬¬X` to `X` in all hypotheses
    (classical `not_not`). Wrapped in `try` so it is a no-op when absent. -/
macro "remove_double_neg" : tactic => `(tactic| try simp only [not_not] at *)

/-! ## Euclidean tactics (`euclidean_tactics.v`) -/

/-- GeoCoq `conclude t`: normalise the context, then close the goal using the
    lemma/axiom `t` — by direct application, backtracking elimination, or search. -/
macro "conclude " t:term : tactic =>
  `(tactic|
    ((try spliter); (try remove_double_neg);
     first
       | done
       | assumption
       | exact $t
       | (apply $t <;> assumption)
       | solve_by_elim [$t:term]
       | (apply $t <;> (first | assumption | aesop))
       | aesop))

/-- GeoCoq `conclude_def t`: unfold the definition `t` and either build it
    (forward: existentials + splits, witnesses by unification) or extract it
    from a hypothesis (backward). -/
macro "conclude_def " t:ident : tactic =>
  `(tactic|
    first
      -- fast path: the fact is already a hypothesis — extract it by unfolding
      -- everywhere + assumption. Avoids aesop reconstructing huge defs (e.g. Par).
      | (unfold $t at *; (try spliter); first | done | assumption)
      -- forward: construct the unfolded goal
      | (unfold $t; (try remove_double_neg);
         first | done | assumption | (repeat' apply And.intro) <;> assumption | aesop)
      -- backward: search after unfolding into the context
      | (unfold $t at *; (try spliter); (try remove_double_neg);
         first | done | assumption | tauto | aesop))

/-- GeoCoq `forward_using thm`: forward-apply `thm` to a hypothesis and use the
    result (possibly a conjunction) to close the goal. -/
macro "forward_using " t:term : tactic =>
  `(tactic|
    ((try spliter);
     first
       | done
       | assumption
       | solve_by_elim [$t:term]
       | aesop (add unsafe 90% forward ($t))
       | aesop))

/-- GeoCoq `contradict`: derive `False` from a collinearity/non-collinearity
    clash or any direct contradiction in the context. -/
macro "contradict" : tactic =>
  `(tactic| first | contradiction | (exfalso; aesop) | tauto)

/-- GeoCoq `close`: finish by assumption, search, splitting conjunctions, or
    providing existential witnesses + deeper search. -/
macro "close" : tactic =>
  `(tactic|
    first
      | assumption
      | (by_contra h; contradiction)      -- classical ¬¬-elim BEFORE aesop, which
                                          -- would normalise away the `¬¬` hypothesis
      | solve_by_elim
      | ((repeat' apply And.intro) <;> (first | assumption | aesop))
      | tauto
      | aesop)

/-! ## Basic Col/nCol lemmas (`euclidean_tactics.v` `basic_lemmas`).
    `nCol` is definitionally `¬ Col` up to reordering, so all three are `tauto`.
    Stated at `euclidean_neutral` (not the basis) to match downstream proof
    contexts and avoid deep-`extends` instance-synthesis failures. -/

variable {Point : Type} [euclidean_neutral Point]

theorem not_nCol_Col (A B C : Point) (h : ¬ nCol A B C) : Col A B C := by
  unfold nCol Col at *; tauto

theorem nCol_notCol (A B C : Point) (h : ¬ Col A B C) : nCol A B C := by
  unfold nCol Col at *; tauto

theorem Col_nCol_False (A B C : Point) (h1 : nCol A B C) (h2 : Col A B C) : False := by
  unfold nCol Col at *; tauto

end GeocoqTranslate.Elements
