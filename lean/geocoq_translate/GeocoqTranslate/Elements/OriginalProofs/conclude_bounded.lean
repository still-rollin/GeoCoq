/-
A bounded, head-indexed backward-chaining core for the `conclude` tactic — a
hand port of Coq `eauto`'s mechanism (discrimination-net indexed hints + bounded
backtracking), as suggested by J. Narboux.

`conclude_bounded L`:
  1. `apply L` — unify L's conclusion with the goal, leaving L's premises as
     subgoals (some with metavariable arguments that the conclusion didn't pin).
  2. discharge the premises by HEAD-INDEXED BACKTRACKING over the local context:
       • most-ground premise first (fewest metavars → unique match → prunes);
       • for each premise, only try hypotheses whose head symbol matches
         (BetS-premise ⇒ only BetS hyps, not the whole ~30-fact context);
       • backtrack across premises (fixes "it is not always the first assumption
         that matches" — which is why `apply <;> assumption` fails here).
  No unbounded search: a failure is cheap, so it never burns the heartbeat budget
  the way the `aesop` fallback does.
-/
import Lean
import GeocoqTranslate.Elements.OriginalProofs.perm_core

namespace GeocoqTranslate.Tactics
open Lean Lean.Meta Lean.Elab.Tactic

/-- Discrimination key: the head constant of a proposition (the thing `eauto`
    would index a hint on). `BetS a b c ↦ `BetS`, `¬ P ↦ `Not`, `a = b ↦ `Eq`.
    `Ne` is normalised to `Not` because `a ≠ b` (`Ne a b`) is definitionally
    `¬ (a = b)`: a premise stated with `≠` must index-match a `¬ _ = _` hypothesis
    (and vice versa), which a raw head comparison would miss. -/
private def headKey (ty : Expr) : Option Name :=
  match ty.getAppFn.constName? with
  | some ``Ne => some ``Not
  | some n    => some n
  | none      => none

/-- Number of (unassigned) metavariables in `e` — used to order premises
    most-ground-first. -/
private def mvarCount (e : Expr) : MetaM Nat := do
  return (← instantiateMVars e).collectMVars {} |>.result.size

/-- For a symmetric geometric head, the `*_perm` lemma (one oriented fact →
    conjunction of ALL its argument permutations) and the head's point-argument
    count. This is the permutation "hint database" the premise-matcher consults. -/
private def permInfoFor (hd : Name) : Option (Name × Nat × Array (Array Nat)) :=
  -- perm tables list the conjuncts of each `*_perm` lemma IN ORDER, each as the
  -- index-permutation applied to the hypothesis's points. They MUST match the
  -- conjunct order in `perm_core.lean` exactly (that ordering is the contract).
  let s3 : Array (Array Nat) :=
    #[#[0,1,2], #[0,2,1], #[1,0,2], #[1,2,0], #[2,0,1], #[2,1,0]]
  if hd == ``euclidean_neutral_basis.Col then some (``GeocoqTranslate.Elements.Col_perm, 3, s3)
  else if hd == ``euclidean_neutral_basis.nCol then some (``GeocoqTranslate.Elements.nCol_perm, 3, s3)
  else if hd == ``euclidean_neutral_basis.BetS then
    some (``GeocoqTranslate.Elements.BetS_perm, 3, #[#[0,1,2], #[2,1,0]])
  else if hd == ``euclidean_neutral_basis.Cong then
    some (``GeocoqTranslate.Elements.Cong_perm, 4,
      #[#[0,1,2,3], #[0,1,3,2], #[1,0,2,3], #[1,0,3,2],
        #[2,3,0,1], #[2,3,1,0], #[3,2,0,1], #[3,2,1,0]])
  else none

/-- Cheap permutation guard: do `a` and `b` (a hypothesis's and the premise's
    point arguments) hold the SAME multiset of points? Skips the expensive
    `mkAppM`/`searchConj` for every non-permutation candidate — the difference
    between one perm-match and one whole-context scan per premise. -/
private def samePointMultiset (a b : Array Expr) : Bool :=
  a.size == b.size &&
    a.all (fun x => (a.filter (· == x)).size == (b.filter (· == x)).size)

/-- Project conjunct `i` (0-based) out of a right-nested `∧`-tree of `n` leaves:
    `And.right` `i` times, then `And.left` unless `i` is the last leaf. No type
    inference or `isDefEq` walk — the caller already knows which conjunct it wants,
    so this is a handful of cheap term applications, not a whnf search. -/
private def projectConj (proof : Expr) (i n : Nat) : MetaM Expr := do
  let mut p := proof
  for _ in [0:i] do p ← mkAppM ``And.right #[p]
  if i + 1 < n then p ← mkAppM ``And.left #[p]
  return p

/-- Prove atom `ty` from context MODULO argument permutation: find a same-head
    hypothesis, expand ALL its permutations with the `*_perm` lemma, and project
    the conjunct definitionally equal to `ty`. This is the perm-aware analogue of
    the direct `assumption` in `closeAtom`/`discharge`; it deletes the explicit
    `forward_using lemma_collinearorder` reorder steps that used to feed premises.
    Must be called inside the goal's local context. Returns the proof, or none. -/
private def permProof (ty : Expr) : MetaM (Option Expr) := do
  let some hd := ty.getAppFn.constName? | return none
  let some (lem, arity, perms) := permInfoFor hd | return none
  let tyArgs := ty.getAppArgs
  if tyArgs.size < arity then return none
  let tyPts := tyArgs.extract (tyArgs.size - arity) tyArgs.size
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let hty ← instantiateMVars d.type
    if hty.getAppFn.constName? != some hd then continue
    let hArgs := hty.getAppArgs
    if hArgs.size != tyArgs.size then continue
    let points := hArgs.extract (hArgs.size - arity) hArgs.size
    -- cheap guard first: only a same-point-multiset hypothesis can be a
    -- permutation of the premise — skip the costly proof build otherwise.
    unless samePointMultiset tyPts points do continue
    -- find WHICH conjunct matches by cheap point-`isDefEq` (points are usually the
    -- same local fvars), so we build and project exactly one conjunct — no whnf
    -- walk over the full 6-/8-way conjunction per candidate.
    let s ← saveState
    let mut idx : Option Nat := none
    for i in [0:perms.size] do
      let p := perms[i]!
      if ← (List.range arity).allM (fun j => isDefEq points[p[j]!]! tyPts[j]!) then
        idx := some i; break
    match idx with
    | none => s.restore
    | some i =>
      let conj ← mkAppM lem (points.push d.toExpr)
      let pf ← projectConj conj i perms.size
      if ← isDefEq (← inferType pf) ty then return some pf
      s.restore
  return none

/-- Close an ATOM goal `ty` (no top-level `∨`/`∧`) from the local context:
    a head-indexed `assumption`, with `rfl` as a fall-back for reflexive
    equalities (`X = X` disjuncts that the proof never asserted as a hypothesis). -/
private def closeAtom (g : MVarId) (ty : Expr) : MetaM Bool := g.withContext do
  let some hk := headKey ty | (do try g.refl; return true catch _ => return false)
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if headKey (← instantiateMVars d.type) == some hk then
      let s ← saveState
      if ← isDefEq ty (← inferType d.toExpr) then
        g.assign d.toExpr; return true
      s.restore
  -- permutation-modulo fallback: a `Col`/`nCol`/`BetS`/`Cong` atom matches a
  -- context hypothesis that is a permutation of it (deletes explicit reorders).
  if let some pf ← permProof ty then g.assign pf; return true
  -- reflexive equality leaf (e.g. a `B = B` disjunct)
  try g.refl; return true catch _ => return false

/-- Assign any still-unassigned metavariable in `ms` whose type is NOT a `Prop`
    (i.e. a leftover existential witness, such as a `Point` that appears only in an
    unchosen disjunct) to an arbitrary in-scope value of the right type. Returns
    `false` if some leftover witness has no suitable in-scope value. -/
private def fillWitnesses (ms : List MVarId) : MetaM Bool := do
  for m in ms do
    if ← m.isAssigned then continue
    let mty ← instantiateMVars (← m.getType)
    if ← Meta.isProp mty then return false   -- an unproved propositional goal
    -- pick any local declaration whose type matches the witness type
    let some val ← m.withContext (do
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        if ← isDefEq (← instantiateMVars d.type) mty then return some d.toExpr
      return none) | return false
    m.assign val
  return true

/- Bounded DNF/∃ solver (Julien's "conclude solves a disjunction of a conjunction
    of facts WITH METAVARIABLES"): prove a goal whose top structure is any nesting
    of `∃`/`∨`/`∧` over geometric atoms, where every atom must match a context
    hypothesis (or be a reflexive equality). `∨` tries each side with backtracking;
    `∧` splits and proves both; `∃` supplies the witness as a metavar pinned by the
    body's atom matches (leftover witnesses are defaulted to an in-scope point). No
    unbounded search — the recursion is bounded by the goal's own connective tree,
    so a failure is cheap. This is what lets `conclude_def Col` pick the right
    disjunct of `Col`'s 6-way definition and `conclude_def InCirc` build the
    existential from a `CI` hypothesis. -/
mutual

/-- Bounded DNF/∃ solver — see the doc-comment block above the `mutual`. -/
private partial def proveStruct (g : MVarId) : MetaM Bool := do
  if ← g.isAssigned then return true
  g.withContext do
    -- `consumeMData`: a goal coming out of `unfold` (e.g. `conclude_def LtA`) is
    -- wrapped in `mdata noImplicitLambda`, which hides the `∃`/`∧`/`∨` head from
    -- `getAppFnArgs` — without stripping it, `proveStruct` bails on EVERY
    -- unfolded-definition build (the bug that made `conclude_def LtA` fall through).
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    -- a whole-goal assumption match short-circuits the structural descent
    if ← closeAtom g ty then return true
    match ty.getAppFnArgs with
    | (``Or, #[_, _]) =>
      let tryside (ctor : Name) : MetaM Bool := do
        let s ← saveState
        try
          let gs ← g.apply (← mkConstWithFreshMVarLevels ctor)
          if ← gs.allM proveStruct then return true
          s.restore; return false
        catch _ => s.restore; return false
      if ← tryside ``Or.inl then return true
      tryside ``Or.inr
    | (``And, #[_, _]) =>
      -- Split the conjunction and discharge the parts with CROSS-CONJUNCT
      -- BACKTRACKING (via `discharge`), not a left-to-right first-match commit.
      -- This is what lets `conclude_def OS`/`CongA` build their existentials: an
      -- early conjunct (`Cong B U E u`) must not greedily pin a witness (`U`) in a
      -- way that dooms a later conjunct (`Cong U V u v`) with no way to undo it.
      let s ← saveState
      try
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
        if ← discharge gs then return true
        s.restore; return false
      catch _ => s.restore; return false
    | (``Exists, #[_, _]) =>
      let s ← saveState
      try
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
        -- prove the propositional subgoal(s); witness goals are pinned by their
        -- unification side-effects, then any leftover is filled with a point.
        let propGoals ← gs.filterM (fun m => do
          if ← m.isAssigned then return false
          Meta.isProp (← m.getType))
        if (← discharge propGoals) && (← fillWitnesses gs) then return true
        s.restore; return false
      catch _ => s.restore; return false
    | _ => return false

/-- Head-indexed, most-ground-first, backtracking discharge of a list of goals.
    Returns `true` iff every goal was closed. Used both for a lemma's premise
    goals (`conclude_bounded`) and for the conjuncts of a structured build goal
    (`proveStruct`'s `And` case). See the doc-comment block below the `mutual`. -/
private partial def discharge (gs : List MVarId) : MetaM Bool := do
  -- Branch only on the still-open *propositional* premises. `apply` also returns
  -- the unpinned data arguments (e.g. `?A ?B : Point`) as goals; those are filled
  -- in by unification when we match a premise, so we never choose them directly.
  let gs ← gs.filterM (fun g => do
    if ← g.isAssigned then return false
    Meta.isProp (← g.getType))
  match gs with
  | [] => return true
  | _  =>
    -- pick the most-ground premise to branch on first
    let scored ← gs.mapM (fun g => do
      let ty := (← instantiateMVars (← g.getType)).consumeMData
      return (g, ty, ← mvarCount ty))
    let sorted := (scored.toArray.qsort (fun a b => a.2.2 < b.2.2)).toList
    let (g, ty, _) := sorted.head!
    let rest := sorted.tail.map (·.1)
    -- structured premise → bounded DNF/∃ solver, then recurse on the rest
    let viaStruct : MetaM Bool := do
      let s ← saveState
      if (← proveStruct g) && (← discharge rest) then return true
      s.restore; return false
    match ty.getAppFnArgs with
    | (``Or, _) | (``And, _) | (``Exists, _) => viaStruct
    | _ =>
    let some hk := headKey ty | viaStruct
    -- All candidate gathering AND trial must run in `g`'s local context: a
    -- candidate hypothesis's free variables are only in scope there. Running
    -- `inferType`/`isDefEq`/`assign` in the ambient context throws "unknown free
    -- variable" whenever the goal's context differs from the ambient one (nested
    -- `have` blocks) — which is exactly the collinear4 shape.
    g.withContext do
      let mut cands : Array Expr := #[]
      for d in (← getLCtx) do
        if d.isImplementationDetail then continue
        if headKey (← instantiateMVars d.type) == some hk then
          cands := cands.push d.toExpr
      -- try each candidate; unify (assigning shared metavars) and recurse
      for c in cands do
        let s ← saveState
        let ok ← (do
          let cty ← inferType c
          if ← isDefEq ty cty then
            g.assign c
            discharge rest
          else
            pure false)
        if ok then return true
        s.restore
      -- permutation-modulo fallback: discharge the premise from a PERMUTED hyp,
      -- then continue with the rest (backtracks if the rest cannot be closed).
      if let some pf ← permProof ty then
        let s ← saveState
        g.assign pf
        if ← discharge rest then return true
        s.restore
      -- atom with no working head-match: bounded leaf (reflexive equalities, …)
      viaStruct

end

/-- `prove_struct` — bounded DNF/CNF solver over context atoms (see `proveStruct`). -/
elab "prove_struct" : tactic => do
  let g ← getMainGoal
  if ← proveStruct g then replaceMainGoal []
  else throwError "prove_struct: goal is not a ∨/∧-combination of available facts"

/-- Bounded core: apply `lem`, then head-indexed-backtrack its premises. -/
def concludeBounded (lem : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let newGoals ← g.withContext (g.apply lem)
  if !(← discharge newGoals) then
    throwError "conclude_bounded: could not discharge the premises of the applied lemma"
  -- after discharging the propositional premises, the data metavars (?A ?B …)
  -- must have been pinned by unification; nothing should remain open.
  let leftover ← newGoals.filterM (fun m => return !(← m.isAssigned))
  if !leftover.isEmpty then
    throwError "conclude_bounded: {leftover.length} argument(s) left unresolved after premises"
  replaceMainGoal []

/-- Search the right-nested `∧`-tree of `e` (a lemma's conclusion, instantiated
    with metavariables) for a conjunct definitionally equal to `goalTy`. On a hit,
    pin the lemma's point metavars by that unification, discharge its premise
    metavars head-indexed from context, and assign `g` the projected proof.
    `proof` carries the `And.left/And.right` chain that extracts the current
    conjunct from a proof of the whole conclusion. -/
private partial def findConjunct (g : MVarId) (goalTy : Expr) (premises : List MVarId)
    (e proof : Expr) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``And, #[_, _]) =>
    let a := e.appFn!.appArg!
    let b := e.appArg!
    if ← findConjunct g goalTy premises a (← mkAppM ``And.left #[proof]) then return true
    findConjunct g goalTy premises b (← mkAppM ``And.right #[proof])
  | _ =>
    let s ← saveState
    if (← isDefEq e goalTy) && (← discharge premises) then
      g.assign (← instantiateMVars proof); return true
    s.restore; return false

/-- Bounded `forward_using`: forward-apply `lem` (a reorder/derivation lemma whose
    conclusion is a single fact or a conjunction of permutations), then close the
    goal with whichever conjunct matches it. General over the lemma's arity and over
    conjunction-vs-single conclusion — unlike the fixed 3-point `(… _ _ _ …).1`
    projection ladder, which broke on 4-point lemmas (`doublereverse`) and on
    non-conjunction conclusions. Bounded: premises are discharged head-indexed. -/
def forwardBounded (lem : Expr) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let goalTy ← instantiateMVars (← g.getType)
    let (mvars, _, concl) ← forallMetaTelescopeReducing (← inferType lem)
    let lemApp := mkAppN lem mvars
    let premises := mvars.toList.map (·.mvarId!)
    if !(← findConjunct g goalTy premises concl lemApp) then
      throwError "forward_bounded: no conjunct of the conclusion matches the goal"
    replaceMainGoal []

/-- `forward_bounded L` — bounded, general forward application of `L` (see above). -/
elab "forward_bounded " t:term : tactic => withMainContext do
  -- `withMainContext` is ESSENTIAL: `t` may mention LOCAL hypotheses
  -- (`conclude (proposition_29 A B E F P G H)` applies the lemma to the proof's own
  -- points). Without it, `elabTermForApply` runs in the ambient context where `A`, `B`,
  -- … are "unknown identifier", the elaboration throws, the whole `forward_bounded`
  -- branch is skipped, and `conclude`/`forward_using` fall through to the last-resort
  -- `aesop` — which then searches the huge geometry context for minutes (the 212 s
  -- blow-up on proposition_30A / proposition_29C).
  let lem ← elabTermForApply t
  forwardBounded lem

/-- `conclude_bounded L` — bounded, head-indexed application of `L`. -/
elab "conclude_bounded " t:term : tactic => withMainContext do
  -- `elabTermForApply` elaborates `t` the way `apply` does: implicit/instance
  -- arguments are left as metavars to be resolved by unification with the goal,
  -- rather than synthesized eagerly (which gets "stuck" with no expected type).
  -- `withMainContext` so a `t` that mentions local hypotheses elaborates (see the
  -- note on `forward_bounded` above).
  let lem ← elabTermForApply t
  concludeBounded lem

end GeocoqTranslate.Tactics
