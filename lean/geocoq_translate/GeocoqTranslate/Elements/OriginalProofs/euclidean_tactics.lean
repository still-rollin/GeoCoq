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
import GeocoqTranslate.Elements.OriginalProofs.conclude_bounded

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

/-- Coq `splits` (`repeat split`): split the GOAL's nested conjunctions into one
    subgoal per atom. The dual of `spliter` (which splits conjunction HYPOTHESES).
    Splits ONLY goals whose head is a SYNTACTIC `And` (checked without `whnf`), so a
    `nCol A B C` conjunct — which is a `def` that WOULD unfold to a 6-way conjunction
    under a plain `apply And.intro` — is left ATOMIC (and then discharged by `auto`'s
    `nCol_notCol` bridge), instead of being shredded into `A ≠ B`, `¬BetS A B C`, … . -/
elab "splits" : tactic => do
  let mut work ← Lean.Elab.Tactic.getGoals
  let mut done : Array Lean.MVarId := #[]
  while !work.isEmpty do
    let g := work.head!
    work := work.tail!
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    match ty.getAppFnArgs with
    | (``And, #[_, _]) =>
      let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``And.intro)
      work := gs ++ work
    | _ => done := done.push g
  Lean.Elab.Tactic.setGoals done.toList

/-- GeoCoq `remove_double_neg`: expose the positive content of every classically
    double-negated hypothesis (`¬¬X`, including `¬ (a ≠ b)`) as a fresh `X` fact.

    This is the NON-DESTRUCTIVE replacement for the old `simp only [not_not] at *`.
    That `simp … at *` was destructive — it rewrote `a = a` hypotheses to `True`
    and used variable equalities to substitute, silently corrupting the facts a
    proof depends on (the unbounded `aesop` fallback then masked the damage by
    re-proving the mangled goal). This version is purely ADDITIVE: for each `¬¬X`
    hypothesis it `note`s a new proof of `X`, touching nothing else. Only genuine
    double negations match (`mkAppM not_not.mp` fails on anything else and is
    skipped), so it can never alter a non-`¬¬` hypothesis. -/
elab "remove_double_neg" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let hyps ← g.withContext do
    -- Existing hypothesis types, so we never re-add a positive fact already present.
    -- Without this guard, running in EVERY `conclude` preamble accumulates duplicate
    -- `this : P` hyps across a long proof — bloating the context and compounding the
    -- per-call cost (the `9_5a` quadratic).
    let existing ← (← Lean.getLCtx).foldlM (init := #[]) (fun acc d => do
      if d.isImplementationDetail then return acc
      return acc.push (← Lean.instantiateMVars d.type))
    let mut acc : Array Lean.Meta.Hypothesis := #[]
    for d in (← Lean.getLCtx) do
      if d.isImplementationDetail then continue
      -- Structurally recognise a classically double-negated hypothesis and read
      -- off the positive proposition `P` it hides. We match SYNTACTICALLY (rather
      -- than unifying `¬¬?a` bottom-up, which fails to resolve `?a` through `Ne`):
      --   `¬ ¬ P`      ⇒ P
      --   `¬ (a ≠ b)`  ⇒ a = b      (`Ne` unfolds to `¬ (a = b)`)
      let ty ← Lean.instantiateMVars d.type
      let some p ← (do
        match ty.getAppFnArgs with
        | (``Not, #[inner]) =>
          match inner.getAppFnArgs with
          | (``Not, #[p])      => return some p
          | (``Ne,  #[_, a, b]) => return some (← Lean.Meta.mkEq a b)
          | _ => return none
        | _ => return none) | continue
      -- skip if this positive fact (or its pending addition) is already present
      if ← existing.anyM (fun e => Lean.Meta.isDefEq e p) then continue
      if ← acc.anyM (fun h => Lean.Meta.isDefEq h.type p) then continue
      -- `of_not_not : ¬¬a → a`, with `a := P` given explicitly so the proof term
      -- elaborates top-down (the hypothesis is `¬¬P` up to defeq).
      try
        let pf ← Lean.Meta.mkAppOptM ``of_not_not #[some p, some d.toExpr]
        acc := acc.push { userName := `this, type := p, value := pf }
      catch _ => pure ()
    pure acc
  if hyps.isEmpty then return
  let (_, g') ← g.assertHypotheses hyps
  Lean.Elab.Tactic.replaceMainGoal [g']


/-! ## Basic Col/nCol lemmas (`euclidean_tactics.v` `basic_lemmas`).
    `nCol` is definitionally `¬ Col` up to reordering, so all three are `tauto`.
    Stated at `euclidean_neutral` (not the basis) to match downstream proof
    contexts and avoid deep-`extends` instance-synthesis failures.

    DEFINED BEFORE THE MACROS that reference them (`forward_using` via `expose_col`):
    a macro's RHS forward-reference to a later same-file declaration silently fails
    to resolve at expansion (it became a no-op preamble that the old `aesop` fallback
    masked). Section-scoped `variable` so the `euclidean_neutral` instance does not
    leak into the `cn_*` shims above. -/
section
variable {Point : Type} [euclidean_neutral Point]

theorem not_nCol_Col (A B C : Point) (h : ¬ nCol A B C) : Col A B C := by
  unfold nCol Col at *; tauto

theorem nCol_notCol (A B C : Point) (h : ¬ Col A B C) : nCol A B C := by
  unfold nCol Col at *; tauto

theorem Col_nCol_False (A B C : Point) (h1 : nCol A B C) (h2 : Col A B C) : False := by
  unfold nCol Col at *; tauto

/-- `nCol` is `¬ Col`, so `¬ nCol` is classically `Col`. -/
theorem not_nCol_iff_Col (A B C : Point) : ¬ nCol A B C ↔ Col A B C :=
  ⟨not_nCol_Col A B C, fun h hn => Col_nCol_False A B C hn h⟩

/-- Collinearity excluded middle: three points are either a proper triangle
    (`nCol`) or collinear (`Col`). This is the disjunction GeoCoq's `by cases on
    (Col …)` splits on; it is genuinely true (classically `Col ∨ ¬Col`, and
    `¬Col ↔ nCol`), so routing the transpiler's case-split through it is honest. -/
theorem nCol_or_Col (A B C : Point) : nCol A B C ∨ Col A B C :=
  (Classical.em (Col A B C)).symm.imp (nCol_notCol A B C) id

/-- Coq `auto` as it appears in GeoCoq's transliterated manual builds
    (`unfold OS; exists …; splits; auto`): close EVERY remaining goal from the local
    context. Geometry atoms go by `assumption`/`rfl`; an `nCol A B C` goal whose
    context only carries `¬ Col A B C` is bridged by `nCol_notCol` (the classical
    `¬Col → nCol`, exactly the hint Coq's `auto` database supplies). `all_goals`
    because Coq's `t; auto` runs `auto` on ALL of `t`'s subgoals (e.g. the six atoms
    `splits` leaves), whereas Lean's `;` is sequential. (Defined here, AFTER
    `nCol_notCol`, so the macro's reference to it resolves at definition time.)
    IMPORTANT: this is the `auto` mapping ONLY. Coq `eauto` (genuine backtracking
    search with metavariables) must be routed to the bounded engine
    (`conclude`/`prove_struct`/`solve_by_elim`), NEVER to this assumption-closer. -/
macro "auto" : tactic => `(tactic|
  all_goals (first
    | assumption
    | rfl
    | exact nCol_notCol _ _ _ (by assumption)))

theorem Col_or_nCol (A B C : Point) : Col A B C ∨ nCol A B C :=
  (nCol_or_Col A B C).symm

/-- Meta helper used by `forward_using`: additively expose the positive `Col A B C`
    from every `¬ nCol A B C` hypothesis (GeoCoq's implicit `¬nCol ⟹ Col` collapse).
    A robust replacement for the macro `have := not_nCol_Col _ _ _ (by assumption)`,
    which was silently a no-op (macro forward-reference + hygiene). Purely additive,
    so it cannot corrupt the context; a no-op when no `¬ nCol` hypothesis exists. -/
elab "expose_col" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let hyps ← g.withContext do
    let mut acc : Array Lean.Meta.Hypothesis := #[]
    for d in (← Lean.getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← Lean.instantiateMVars d.type
      match ty.getAppFnArgs with
      | (``Not, #[inner]) =>
        match inner.getAppFnArgs with
        | (``euclidean_neutral_basis.nCol, args) =>
          if args.size ≥ 3 then
            let a := args[args.size - 3]!
            let b := args[args.size - 2]!
            let c := args[args.size - 1]!
            try
              let pf ← Lean.Meta.mkAppM ``not_nCol_Col #[a, b, c, d.toExpr]
              acc := acc.push { userName := `this, type := ← Lean.Meta.inferType pf, value := pf }
            catch _ => pure ()
        | _ => pure ()
      | _ => pure ()
    pure acc
  if hyps.isEmpty then return
  let (_, g') ← g.assertHypotheses hyps
  Lean.Elab.Tactic.replaceMainGoal [g']

/-- Meta helper: additively materialise the positive `nCol A B C` from every
    `¬ Col A B C` hypothesis (via `nCol_notCol`). This is the bridge GeoCoq's
    `conclude` makes implicitly: a lemma/axiom premise stated with `nCol` (e.g.
    `postulate_Pasch_inner`'s `nCol A C B`) must be discharged from a context that
    only carries the fact as `¬ Col A C B`. Because `nCol` (a positive def) and
    `¬ Col` have DIFFERENT head symbols, the head-indexed `conclude_bounded` search
    never bridges them on its own — so without this the Pasch steps fail to
    discharge and fall through to the `aesop` blow-up. Purely additive + DEDUP'd
    (skips an `nCol` already present), so it cannot corrupt or bloat the context;
    a no-op when no `¬ Col` hypothesis exists. -/
elab "expose_ncol" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let hyps ← g.withContext do
    -- existing nCol facts, so we never re-add one already in context
    let mut existing : Array Lean.Expr := #[]
    for d in (← Lean.getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← Lean.instantiateMVars d.type
      if ty.getAppFn.constName? == some ``euclidean_neutral_basis.nCol then
        existing := existing.push ty
    let mut acc : Array Lean.Meta.Hypothesis := #[]
    for d in (← Lean.getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← Lean.instantiateMVars d.type
      match ty.getAppFnArgs with
      | (``Not, #[inner]) =>
        match inner.getAppFnArgs with
        | (``euclidean_neutral_basis.Col, args) =>
          if args.size ≥ 3 then
            let a := args[args.size - 3]!
            let b := args[args.size - 2]!
            let c := args[args.size - 1]!
            try
              let pf ← Lean.Meta.mkAppM ``nCol_notCol #[a, b, c, d.toExpr]
              let pty ← Lean.Meta.inferType pf
              -- skip if this nCol fact is already present (or queued)
              if ← existing.anyM (fun e => Lean.Meta.isDefEq e pty) then pure ()
              else if ← acc.anyM (fun h => Lean.Meta.isDefEq h.type pty) then pure ()
              else acc := acc.push { userName := `this, type := pty, value := pf }
            catch _ => pure ()
        | _ => pure ()
      | _ => pure ()
    pure acc
  if hyps.isEmpty then return
  let (_, g') ← g.assertHypotheses hyps
  Lean.Elab.Tactic.replaceMainGoal [g']

end

/-! ## Euclidean tactics (`euclidean_tactics.v`) -/

/-- Close a goal that may be a (right-nested, up to 3-way) DISJUNCTION by trying
    `assumption`/`rfl` at each branch. The area axioms (`axiom_paste3/4/5`) carry
    premises like `BetS A M B ∨ A = M ∨ M = B`; after `apply`, the determining
    midpoint metavar is pinned by an earlier ground `BetS` premise, leaving the
    correct branch closable by `assumption` (the established betweenness) or `rfl`
    (a degenerate `x = x`). This stays cheap — no search, just branch injection. -/
macro "assum_inj" : tactic => `(tactic|
  first
    | assumption | rfl
    | (left;  (first | assumption | rfl))
    | (right; (first | assumption | rfl
                     | (left;  (first | assumption | rfl))
                     | (right; (first | assumption | rfl)))))

/-- GeoCoq `conclude t`: normalise the context, then close the goal using the
    lemma/axiom `t` — by direct application, backtracking elimination, or search. -/
macro "conclude " t:term : tactic =>
  `(tactic|
    -- Preamble: `spliter` (split conjunctions in context) + the now NON-DESTRUCTIVE
    -- `remove_double_neg` (additively exposes `a = b` from a `¬ a ≠ b` hypothesis so
    -- the `subst_vars` path below can fire — this is what `conclude cn_equalitysub`
    -- needs). The old preamble's `simp only [not_not] at *` corrupted the context;
    -- the additive version cannot, so it is safe even now that the ladder is bounded.
    ((try spliter); (try remove_double_neg); (try expose_ncol);
     first
       | done
       | assumption
       -- First-order substitution path. Closes `conclude cn_equalitysub` /
       -- `cn_equalitytransitive` / `cn_equalityreflexive` (GeoCoq's equality
       -- idioms) by a cheap syntactic `subst` — BEFORE `apply $t`, where matching
       -- those lemmas' conclusions forces a higher-order motive search that
       -- explodes on `Col`'s 6-way disjunction. `subst_vars` is name-free (a no-op
       -- when no variable-equality exists); `rfl` mops up a residual `x = x`.
       | (subst_vars; (first | assumption | rfl))
       | exact $t
       | (apply $t <;> assumption)
       -- area axioms (`axiom_paste3/4/5`) leave DISJUNCTION premises (`BetS … ∨
       -- eq … ∨ eq …`) after `apply`; the determining midpoint is pinned by an
       -- earlier ground `BetS` premise (the preamble `spliter` having exposed it
       -- from its bundling conjunction), so the right branch closes by
       -- `assumption`/`rfl`. Cheap branch injection, before the bounded search.
       | (apply $t <;> assum_inj)
       -- HEAD-INDEXED BOUNDED path (the faithful `eauto` port). Apply `t`, then
       -- discharge its premises by head-indexed, most-ground-first backtracking
       -- over the local context (BetS-premise ⇒ only BetS hyps, with backtracking
       -- across premises). This handles the unpinned-argument lemmas
       -- (`outerconnectivity`, `connectivity`, `axiom_5_line`, …) cheaply, where
       -- `apply <;> assumption` can't backtrack and the unbounded `aesop` blew the
       -- heartbeat budget. Bounded: a failure is cheap (no heartbeat blow-up).
       | conclude_bounded $t
       -- BOUNDED conjunct-projection: when `t` concludes a CONJUNCTION and the goal is
       -- one conjunct (Coq's `apply (L …)` projects implicitly), `forward_bounded`
       -- picks the matching conjunct of `t`'s conclusion and discharges its premises
       -- head-indexed — e.g. `conclude lemma_together` (`… → Lt … ∧ A ≠ a ∧ …`) for a
       -- `Lt …` goal.
       | forward_bounded $t
       -- LAST-RESORT fallbacks. The bounded tactics above are the primary path and
       -- handle the collinear4-class lemmas, so those never reach here (this is what
       -- avoids the old `solve_by_elim`-over-huge-context heartbeat sink). `aesop` is
       -- bounded by its own `maxRuleApplications` (200) and fails gracefully; it only
       -- runs on the easy long tail the bounded tactics don't yet cover.
       -- `And.left/And.right` let `solve_by_elim` PROJECT a conjunction-concluding
       -- lemma to the goal — Coq's `apply (L …)` does this implicitly (proving `A`
       -- from `L : … → A ∧ B`), e.g. `conclude lemma_together` (concludes `Lt … ∧
       -- A ≠ a ∧ …`) against a bare `Lt …` goal.
       | solve_by_elim [$t:term, And.left, And.right]
       | (apply $t <;> (first | assumption | aesop))
       | aesop))

/-- Cheap, TARGETED extract: unfold the definition `t` only in the hypotheses
    that actually have head `t` (then destructure the exposed ∧/∃), instead of the
    context-wide `unfold t at *; casesm* …` blast. The `at *` form re-scans (and
    `casesm` re-destructures) ALL ~60 hypotheses of a deep proof on EVERY call —
    that is the quadratic per-call cost behind the `crossbar`/`prop_04` cumulative
    timeouts. Here we touch only the 1–3 relevant hypotheses: a failed `unfold at h`
    (the def does not occur in `h`) is caught and skipped, so non-matching
    hypotheses cost only a cheap occurrence scan, never a rewrite/`casesm`. -/
elab "extract_def " t:ident : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let targets ← g.withContext do
    let mut hs : Array Lean.Name := #[]
    for d in (← Lean.getLCtx) do
      if d.isImplementationDetail then continue
      hs := hs.push d.userName
    return hs
  let mut unfolded := false
  for h in targets do
    let hid := Lean.mkIdent h
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $t at $hid:ident))
      unfolded := true
    catch _ => pure ()
  if !unfolded then
    throwError "extract_def: no hypothesis with head {t}"
  Lean.Elab.Tactic.evalTactic (← `(tactic| (try (casesm* _ ∧ _, Exists _))))

/-- Count a goal's leading existentials `k` and the number of conjunct leaves `n`
    in the trailing conjunction (`∃ x₁ … x_k, C₁ ∧ … ∧ C_n`). Structural, under
    binders (loose bvars are fine — we only count shape). -/
private partial def countExistsAnd : Lean.Expr → Nat × Nat
  | e =>
    -- the goal coming out of `unfold` is wrapped in `mdata noImplicitLambda`; strip it
    match e.consumeMData.getAppFnArgs with
    | (``Exists, #[_, lam]) =>
      let (k, n) := countExistsAnd lam.consumeMData.bindingBody!
      (k + 1, n)
    | (``And, #[a, b]) =>
      let (_, na) := countExistsAnd a
      let (_, nb) := countExistsAnd b
      (0, na + nb)
    | _ => (0, 1)

/-- DEFERRED-UNIFICATION existential build (the `eauto`-style fix for `conclude_def
    CongA`/`OS`-type goals that the eager `prove_struct` search can't close). The
    eager search fails because no SINGLE conjunct pins a witness in isolation
    (`Out B A ?U` does not determine `?U`); it is a LATER conjunct that pins all
    witnesses at once (`Cong U V u v` unifies with `Cong A C a c`, fixing
    `U,V,u,v` together). So instead of searching, we hand the witnesses to the
    elaborator as DEFERRED holes inside a single `exact ⟨_, …, _, by …, …⟩`: the
    `exact` carries the full expected type, the `_` witnesses stay metavariables,
    and each conjunct's proof (`assumption` / `prove_struct` / the `nCol` bridge)
    pins them by unification — left-to-right, with the elaborator backtracking. The
    crucial detail is `exact` (term-mode, expected type known), NOT `refine`: under
    `refine` the `_` witnesses become Point GOALS that `assumption` wrongly closes
    with the first Point in scope. -/
elab "build_struct" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  -- Count the leading `∃`s / conjuncts on the WHNF-reduced type, so a goal still in
  -- DEFINITION form (`InCirc N K`, head not yet `∃`) is counted through its `def`
  -- without a prior `unfold`. This is the heartbeat-critical path: building straight
  -- from the def goal lets the `exact ⟨…⟩` anonymous constructor discharge all the
  -- existentials + the top `∧` in ONE deferred-unification pass, whereas building
  -- from the `unfold`ed goal forces `prove_struct`'s per-witness `apply Exists.intro`
  -- descent, which does ~85k heartbeats of `whnf` on a `Circle`-typed body. The
  -- `exact`/`apply Exists.intro` below still elaborate against the ORIGINAL goal `g`
  -- (the anonymous constructor / `apply` see through the `def` themselves). -/
  let tyR ← Lean.Meta.whnf ty
  let (k, n) := countExistsAnd tyR
  if k == 0 then
    throwError "build_struct: goal has no leading existential to build"
  let hole ← `(term| _)
  -- CHEAP prover: pure `assumption`. When every conjunct is already a context fact
  -- (CongA-, LtA-style builds) the elaborator pins the witnesses by backtracking
  -- over `assumption` alone — which is fast. Crucially this AVOIDS invoking
  -- `prove_struct` during backtracking: for a goal like `LtA = ∃ U X V, BetS U X V
  -- ∧ … ∧ CongA A B C D E X`, a wrong early `BetS` pick mispins `X`, and a
  -- `prove_struct` prover would then try to *build* the inner `CongA` from scratch
  -- on every backtrack — the heartbeat sink. Pure `assumption` fails that branch
  -- cheaply and backtracks to the next `BetS`.
  let proverCheap ← `(term| by assumption)
  -- FULL prover: also handles conjuncts that are disjunctions / need the `nCol`
  -- bridge (e.g. `OS`/`Col`-style builds where a conjunct is a 6-way `∨`).
  let proverFull ← `(term|
    by (first | assumption | prove_struct
              | exact nCol_or_Col _ _ _ | exact Col_or_nCol _ _ _))
  let elemsCheap : Array (Lean.TSyntax `term) :=
    (Array.replicate k hole) ++ (Array.replicate n proverCheap)
  let elemsFull : Array (Lean.TSyntax `term) :=
    (Array.replicate k hole) ++ (Array.replicate n proverFull)
  let stxCheap ← `(term| ⟨$elemsCheap,*⟩)
  let stxFull  ← `(term| ⟨$elemsFull,*⟩)
  -- PHASE C — joint BACKTRACKING search (for AMBIGUOUS-witness builds like
  -- `LtA = ∃ U X V, BetS U X V ∧ Out C B U ∧ Out C G V ∧ CongA A B C B C X`, where
  -- no single conjunct pins a witness uniquely — `Out C B U` matches both `Out C B B`
  -- and `Out C B e`, and `BetS U X V` matches ~20 facts — so the commit-without-
  -- backtrack `exact ⟨…⟩` of Phases A/B mispicks and fails). `apply Exists.intro`
  -- introduces each witness as a DEFERRED metavariable (NOT a goal — so
  -- `solve_by_elim` never wastes time plugging `Point`s into it), `refine ⟨?_,…⟩`
  -- exposes the conjuncts as goals, and `solve_by_elim*` solves them JOINTLY with
  -- backtracking: matching the joint constraint (`BetS U X V` ↔ `BetS e h G`) pins
  -- all witnesses at once, and a wrong pick is undone. `maxDepth` is small (these are
  -- leaf assumptions) to keep the search bounded. -/
  let kLit := Lean.Syntax.mkNumLit (toString k)
  let goalHole ← `(term| ?_)
  let goalHoles : Array (Lean.TSyntax `term) := Array.replicate n goalHole
  -- All `k` witnesses + `n` conjuncts as holes, for the disjunction-aware build below.
  let allHoles : Array (Lean.TSyntax `term) := Array.replicate (k + n) goalHole
  -- Is the ORIGINAL goal already in structural form (`∃`/`∧`/`∨` head), or still a
  -- folded `def` (`InCirc …`) that only WHNF exposed? Phase A (`exact ⟨_…, by
  -- assumption…⟩`) is the cheap fast-path for an already-unfolded all-atoms build
  -- (`LtA`/`CongA`), but on a folded def whose body hides a DISJUNCTION conjunct it
  -- does not merely fail — its anonymous-constructor unification spins ~200k
  -- heartbeats of `isDefEq` on the `Circle`-typed body before giving up, and a
  -- heartbeat timeout is NOT catchable, so `first` never reaches Phase B. So for a
  -- folded-def goal we SKIP Phase A and go straight to the full prover. -/
  let headIsStruct :=
    match ty.consumeMData.getAppFnArgs with
    | (``Exists, _) | (``And, _) | (``Or, _) => true
    | _ => false
  if headIsStruct then
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      first
        | exact $stxCheap
        | exact $stxFull
        | (iterate $kLit (apply Exists.intro);
           refine ⟨$goalHoles,*⟩;
           solve_by_elim* (config := { maxDepth := 8 }))))
  else
    -- FOLDED-DEF build (`InCirc N K`, head a `def` over a `Circle`-typed body). Phase C's
    -- `iterate (apply Exists.intro)` would whnf the `Circle` body once per witness and blow
    -- the heartbeat budget, so we use the OR-COMMIT build instead (J. Narboux's structure):
    --   1. `refine ⟨_…⟩` — ONE anonymous-constructor pass introduces all `k` witnesses AND
    --      the `n` conjuncts as goals (no per-witness `Exists.intro` descent, no `Circle` whnf
    --      blow-up);
    --   2. `rotate_left k` — bring the `n` CONJUNCT goals in front of the witness goals, so
    --      they are solved FIRST and pin the witnesses by unification;
    --   3. per conjunct: `assumption`/`prove_struct` for an atom, or — for a DISJUNCTION
    --      conjunct — COMMIT the side first (`left`/`right`) and then assemble that side's
    --      conjunction LEFT-TO-RIGHT (`repeat' apply And.intro; all_goals assumption`), so a
    --      joint-constraint conjunct (`BetS U Y X`) pins an otherwise-ambiguous witness before
    --      a looser one (`Cong U X V W`) can mis-pin it;
    --   4. a final `all_goals assumption` fills any witness left dangling by an `Or.inl` side
    --      that doesn't mention it (the `fillWitnesses` role, but as a cheap single step).
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      first
        | exact $stxFull
        | (refine ⟨$allHoles,*⟩;
           rotate_left $kLit;
           all_goals (first
             | assumption
             | prove_struct
             | (left; (repeat' apply And.intro); all_goals assumption)
             | (right; (repeat' apply And.intro); all_goals assumption)
             | exact nCol_or_Col _ _ _ | exact Col_or_nCol _ _ _);
           all_goals assumption)))

/-- GeoCoq `conclude_def t`: unfold the definition `t` and either build it
    (forward: existentials + splits, witnesses by unification) or extract it
    from a hypothesis (backward). -/
macro "conclude_def " t:ident : tactic =>
  `(tactic|
    first
      -- CHEAP paths first. `unfold $t at *` (the context-wide blast) is QUADRATIC in a
      -- proof with many `Col`/`Bet…` hypotheses — it rewrites the definition in every
      -- one, on every call — so it is demoted to the last resort. The common case is a
      -- BUILD (`have : Col … := by conclude_def Col`), handled goal-only below.
      | done
      | assumption
      -- forward BUILD (bounded, type-directed, GOAL-ONLY unfold). The unfolded goal is
      -- an existential over point witnesses whose body is a ∨/∧-combination of atoms
      -- (e.g. `Col`'s 6-way disjunction, `InCirc`'s `∃ … CI … ∧ (P = U ∨ …)`).
      -- `prove_struct` selects the right disjunct, splits conjunctions, supplies
      -- witnesses by unification, and discharges atoms from context — bounded by the
      -- goal's connective tree.
      -- RAW-GOAL build FIRST (no `unfold`): for a heavy existential def with a buried
      -- disjunction (`InCirc = ∃ X Y U V W, CI … ∧ (P = U ∨ …)`), `build_struct` now
      -- counts through the `def` head (whnf) and emits `exact ⟨_…, <prover>…⟩` against
      -- the still-folded goal — the anonymous constructor discharges ALL existentials +
      -- the top `∧` in ONE deferred-unification pass. This avoids the `whnf`/heartbeat
      -- blow-up of building from the `unfold`ed goal (where `prove_struct`'s per-witness
      -- `apply Exists.intro` descent costs ~85k heartbeats on a `Circle`-typed body, so
      -- three such builds in one declaration — e.g. `lemma_ondiameter` — exceed budget).
      | build_struct
      -- forward BUILD via unfold (fallback when the raw build doesn't apply — e.g. the
      -- fact is buried in a conjunction hypothesis that `spliter` must first break open).
      | (unfold $t; (try remove_double_neg); (try spliter);
         first | done | assumption | prove_struct | build_struct)
      -- CHEAP EXTRACT (backward, TARGETED): unfold the def only in the hypotheses that
      -- have head `t` (not context-wide), destructure, and rebuild the goal with
      -- `prove_struct`. This is the common extract case and avoids the quadratic `at *`
      -- blast below; the `at *` path is kept only as a correctness fallback.
      | (extract_def $t; (try remove_double_neg);
         first | done | assumption | prove_struct | build_struct)
      -- EXTRACT (backward): the fact lives in a hypothesis in def form; unfold the def
      -- in the context to expose it, then DESTRUCTURE the resulting existentials and
      -- conjunctions so the atoms land in the context as plain hypotheses. This is what
      -- makes extraction robust to existential REORDERING: the transpiler spells a def's
      -- witnesses in body-appearance order (`∃ p q r`) while the Lean def binds them in
      -- Coq's order (`∃ X U V`) — logically equal but NOT defeq, so a bare `assumption`
      -- against the unfolded hypothesis fails. By exposing the atoms and letting
      -- `prove_struct` rebuild the goal existential in whatever order it is written, we
      -- sidestep the mismatch entirely (and avoid the aesop blow-up). This is the
      -- expensive `at *` path, tried only after the cheap build path fails.
      | (unfold $t at *; (try (casesm* _ ∧ _, Exists _)); (try remove_double_neg);
         first | done | assumption | prove_struct | build_struct | tauto | aesop)
      -- last-resort: aesop (rule-bounded) for defs prove_struct doesn't yet cover.
      | aesop)

/-- GeoCoq `forward_using thm`: forward-apply `thm` to a hypothesis and use the
    result (possibly a conjunction) to close the goal. -/
macro "forward_using " t:term : tactic =>
  `(tactic|
    ((try spliter);
     -- ¬nCol ⟹ Col preamble normalisation. GeoCoq's `forward_using` collapses
     -- `¬ nCol _ _ _` (= `¬¬ Col`) to a positive `Col` implicitly; `expose_col`
     -- (a meta tactic, robust to macro hygiene) adds those positive facts so the
     -- bounded reorder below can fire on them.
     (try expose_col);
     first
       | done
       | assumption
       -- BOUNDED path: forward-apply `t` to a hypothesis and PROJECT the needed
       -- permutation out of the resulting conjunction. This is TYPE-DIRECTED: the
       -- goal's permutation unifies with one projection, which pins `t`'s point
       -- arguments, so `(by assumption)` finds the exact source hypothesis even
       -- among many similarly-shaped facts. Bounded (no search) and scales flat in
       -- the number of context facts — unlike `solve_by_elim [t, And.left, ...]`,
       -- whose backtracking over And-projections is superlinear (measured).
       -- Covers the 5-permutation reorder lemmas (collinearorder, NCorder, …).
       -- BOUNDED general path: forward-apply `t` (any arity; conclusion a single
       -- fact or a conjunction of permutations) and close with the matching
       -- conjunct, premises discharged head-indexed. Replaces the fixed 3-point
       -- `(… _ _ _ …).1` projection ladder.
       | forward_bounded $t
       -- last-resort fallbacks (rule-bounded aesop for the long tail)
       | solve_by_elim [$t:term, And.left, And.right]
       | aesop (add unsafe 90% forward ($t))
       | aesop))

/-- GeoCoq `contradict`: derive `False` from a collinearity/non-collinearity
    clash or any direct contradiction in the context.

    The final fallback handles the recurring `nCol`-refutation shape where the
    goal has been reduced to a betweenness disjunction (e.g.
    `BetS C B D ∨ BetS B C D ∨ BetS B D C`) and the needed betweenness fact is
    only available as a conditional (`¬BetS … → ¬BetS … → BetS …`). `aesop`
    stalls on this (no classical case-split over the betweenness atoms); after
    unfolding `nCol`/`Col` to expose the disjunction, `tauto` closes it by
    propositional case analysis. Purely additive — only reached when the prior
    alternatives fail, so it cannot regress lemmas that already close above. -/
macro "contradict" : tactic =>
  `(tactic|
    first
      | contradiction
      -- CHEAP geometric clash, tried BEFORE the `aesop`/`simp at *` fallbacks: a
      -- `nCol A B C` + `Col A B C` pair refutes via `Col_nCol_False`. Because `nCol`
      -- and `Col` are `def`s (not syntactic negations), plain `contradiction` MISSES
      -- this clash and falls straight through to `exfalso; aesop`, which runs `simp` on
      -- the (often 100-hypothesis) context — ~1 s per call, the dominant heartbeat sink
      -- in large proofs (`angletrichotomy2` has 38 `contradict`s; ~8 hit this clash and
      -- cost ~11 s of `simp` between them). A depth-bounded `solve_by_elim` over the one
      -- lemma `Col_nCol_False` finds the matching triple from context in a few steps.
      | (exfalso;
         solve_by_elim (config := { maxDepth := 4 }) [Col_nCol_False])
      | (exfalso; aesop)
      | tauto
      | (exfalso;
         unfold euclidean_neutral_basis.nCol euclidean_neutral_basis.Col at *;
         (try simp only [not_not, not_or] at *);
         tauto))

/-- GeoCoq `close`: finish by assumption, search, splitting conjunctions, or
    providing existential witnesses + deeper search. -/
macro "close" : tactic =>
  `(tactic|
    -- `expose_col`/`expose_ncol` first: a `Col A B C` goal backed by `¬ nCol A B C`
    -- (resp. a positive `nCol A B C` goal backed by `¬ Col A B C`) is closed cheaply by
    -- the FIRST `assumption` once the positive form is materialised. Without
    -- `expose_ncol` a positive `nCol` goal falls through to the `(repeat' apply
    -- And.intro) <;> aesop` tail, which SPLITS `nCol` into its six atoms and runs
    -- `aesop` (→ `simp` → seconds of typeclass inference) on each — six `simp`s per
    -- `nCol` close, the dominant heartbeat sink in large proofs (proposition_33).
    -- `spliter` first too: a proof's final `close` often discharges a CONJUNCTION goal
    -- (`CongA … ∧ RT …`, proposition_29C's conclusion) whose conjuncts live BUNDLED
    -- inside one hypothesis (`this : CongA … ∧ CongA … ∧ RT …`, from `conclude
    -- proposition_29`). Without splitting that bundle the conjuncts are not standalone
    -- facts, so `assumption`/`prove_struct` cannot reach them and the goal falls to the
    -- `aesop` tail (~19 `simp`s of typeclass inference — the proposition_29C sink).
    ((try spliter); (try expose_col); (try expose_ncol);
     first
      | assumption
      | (by_contra h; contradiction)      -- classical ¬¬-elim BEFORE aesop, which
                                          -- would normalise away the `¬¬` hypothesis
      -- A proof's FINAL `close` often discharges the theorem's existential
      -- conclusion (`∃ X Y Z, SumA … X Y Z`) from a fact just established
      -- (`SumA … E C B`). `prove_struct`/`build_struct` assemble it with deferred
      -- witnesses — WITHOUT this, `aesop` recurses on the existential and crashes
      -- with "maximum recursion depth" (proposition_17).
      | prove_struct
      | build_struct
      | solve_by_elim
      | ((repeat' apply And.intro) <;> (first | assumption | aesop))
      | tauto
      | aesop))

end GeocoqTranslate.Elements
