/-
Lean port of GeoCoq's `ColR` reflective collinearity tactic.

Source: `theories/Coinc/ColR.v` (reflective core) + `theories/Main/Tactics/ColR.v`
(the Ltac wrapper). See `docs/tarski_architecture.md` for the design.

This file is the **reflective core**: a decidable collinearity-closure procedure
plus its soundness theorem, parametric over the abstract `ColTheory` interface
(GeoCoq's `Col_theory`, `theories/Coinc/tactics_axioms.v`). It has NO dependency
on the Tarski geometry — the geometry only appears later as a `ColTheory` instance.

Design choice vs. the Coq original: Coq uses `MSetAVL` ordered-set functors so
`vm_compute` is fast. In Lean we use plain `List`s and let `decide` / `native_decide`
evaluate the closure at each call site. The soundness theorem below is proved
abstractly (kernel-checked, no `native_decide`); `native_decide` only ever enters
at a *call* to discharge `decideCol st a b c` for concrete data.
-/
import Mathlib.Tactic

namespace GeocoqTranslate.Tarski.ColR

/-! ## The interface (GeoCoq `Col_theory`) -/

/-- Minimal set of facts the collinearity procedure needs, mirroring GeoCoq's
    `Col_theory` (`theories/Coinc/tactics_axioms.v`). The Tarski instance is built
    from `col_trivial_1`, `col_permutation_1`, `col_permutation_5`, `col3`. -/
class ColTheory (P : Type*) (Col : P → P → P → Prop) : Prop where
  trivial : ∀ A B, Col A A B
  perm1 : ∀ A B C, Col A B C → Col B C A
  perm2 : ∀ A B C, Col A B C → Col A C B
  /-- Two lines sharing two distinct points coincide — the merge rule. -/
  col3 : ∀ X Y A B C, X ≠ Y → Col X Y A → Col X Y B → Col X Y C → Col A B C

/-! ## Reflective representation

Points are numbered `Nat`. A *line* is a list of point-ids known to be mutually
collinear; `ColState.lines` is the set of lines and `ColState.diff` the pairs known
to be distinct (the analogue of Coq's `ss` and `sp`). -/

abbrev PointId := Nat

structure ColState where
  lines : List (List PointId)
  diff  : List (PointId × PointId)

/-- Lines `s` and `t` share a *known-distinct* pair: some `(p,q) ∈ diff` with both
    `p` and `q` in `s` and in `t`. Two such lines are mergeable. -/
def sharesDiffPair (diff : List (PointId × PointId)) (s t : List PointId) : Prop :=
  ∃ pq ∈ diff, pq.1 ∈ s ∧ pq.2 ∈ s ∧ pq.1 ∈ t ∧ pq.2 ∈ t

instance (diff s t) : Decidable (sharesDiffPair diff s t) := by
  unfold sharesDiffPair; infer_instance

/-- Try to merge line `s` with the first later line sharing a distinct pair.
    Returns the merged line `s ++ t` and the remaining lines (with `t` removed). -/
def absorbOne (diff : List (PointId × PointId)) (s : List PointId) :
    List (List PointId) → Option (List PointId × List (List PointId))
  | [] => none
  | t :: ts =>
    if sharesDiffPair diff s t then
      some (s ++ t, ts)
    else
      match absorbOne diff s ts with
      | some (m, ts') => some (m, t :: ts')
      | none => none

/-- One saturation step: find any mergeable pair of lines and merge them,
    reducing the number of lines by one. `none` = already saturated. -/
def stepMerge (diff : List (PointId × PointId)) :
    List (List PointId) → Option (List (List PointId))
  | [] => none
  | s :: rest =>
    match absorbOne diff s rest with
    | some (m, rest') => some (m :: rest')
    | none =>
      match stepMerge diff rest with
      | some L' => some (s :: L')
      | none => none

/-- Fuel-bounded saturation: apply `stepMerge` until fixpoint. Fuel = number of
    lines suffices, since each step strictly decreases the line count. -/
def saturate (diff : List (PointId × PointId)) (lines : List (List PointId)) :
    Nat → List (List PointId)
  | 0 => lines
  | fuel + 1 =>
    match stepMerge diff lines with
    | some lines' => saturate diff lines' fuel
    | none => lines

/-- The decision: saturate, then look for a single line containing all three points. -/
def decideCol (st : ColState) (a b c : PointId) : Prop :=
  ∃ s ∈ saturate st.diff st.lines st.lines.length, a ∈ s ∧ b ∈ s ∧ c ∈ s

instance (st a b c) : Decidable (decideCol st a b c) := by
  unfold decideCol; infer_instance

/-! ## Soundness

Invariants mirroring Coq's `ss_ok` / `sp_ok`. `LineOk` says every ordered triple
of points on a line is collinear; `SPok` says every recorded pair is genuinely
distinct. -/

variable {P : Type*} {Col : P → P → P → Prop}

/-- Every ordered triple drawn from line `s` is collinear under `interp`. -/
def LineOk (Col : P → P → P → Prop) (interp : PointId → P) (s : List PointId) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, Col (interp a) (interp b) (interp c)

/-- Every line is collinear (`ss_ok`). -/
def LinesOk (Col : P → P → P → Prop) (interp : PointId → P)
    (L : List (List PointId)) : Prop :=
  ∀ s ∈ L, LineOk Col interp s

/-- Every recorded pair is distinct (`sp_ok`). -/
def SPok (interp : PointId → P) (diff : List (PointId × PointId)) : Prop :=
  ∀ pq ∈ diff, interp pq.1 ≠ interp pq.2

/-- The merge rule is sound: if `s` and `t` are collinear lines sharing a known
    distinct pair, their union is a collinear line. This is where `col3` is used. -/
theorem lineOk_append [ColTheory P Col] {interp : PointId → P}
    {s t : List PointId} {diff : List (PointId × PointId)}
    (hs : LineOk Col interp s) (ht : LineOk Col interp t)
    (hsp : SPok interp diff) (hshare : sharesDiffPair diff s t) :
    LineOk Col interp (s ++ t) := by
  obtain ⟨pq, hpqmem, hp_s, hq_s, hp_t, hq_t⟩ := hshare
  have hpq : interp pq.1 ≠ interp pq.2 := hsp pq hpqmem
  -- every point on `s ++ t` is collinear with the distinct pair `pq.1, pq.2`
  have key : ∀ x ∈ s ++ t, Col (interp pq.1) (interp pq.2) (interp x) := by
    intro x hx
    rcases List.mem_append.mp hx with hxs | hxt
    · exact hs pq.1 hp_s pq.2 hq_s x hxs
    · exact ht pq.1 hp_t pq.2 hq_t x hxt
  intro a ha b hb c hc
  exact ColTheory.col3 _ _ _ _ _ hpq (key a ha) (key b hb) (key c hc)

theorem absorbOne_ok [ColTheory P Col] {interp : PointId → P}
    {diff : List (PointId × PointId)} {s : List PointId}
    (hs : LineOk Col interp s) (hsp : SPok interp diff) :
    ∀ {rest m rest'}, LinesOk Col interp rest →
      absorbOne diff s rest = some (m, rest') →
      LineOk Col interp m ∧ LinesOk Col interp rest' := by
  intro rest
  induction rest with
  | nil => intro m rest' _ h; simp [absorbOne] at h
  | cons t ts ih =>
    intro m rest' hrest h
    have ht : LineOk Col interp t := hrest t (by simp)
    have hts : LinesOk Col interp ts := fun u hu => hrest u (by simp [hu])
    unfold absorbOne at h
    by_cases hshare : sharesDiffPair diff s t
    · -- merged with `t`
      rw [if_pos hshare] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hm, hrest'⟩ := h
      subst hm; subst hrest'
      exact ⟨lineOk_append hs ht hsp hshare, hts⟩
    · -- recurse into `ts`
      rw [if_neg hshare] at h
      cases hx : absorbOne diff s ts with
      | none => simp [hx] at h
      | some r =>
        obtain ⟨m0, ts0⟩ := r
        simp only [hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hm, hrest'⟩ := h
        subst hm; subst hrest'
        obtain ⟨hmOk, hts0Ok⟩ := ih hts hx
        refine ⟨hmOk, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with hut | huts0
        · subst hut; exact ht
        · exact hts0Ok u huts0

theorem stepMerge_ok [ColTheory P Col] {interp : PointId → P}
    {diff : List (PointId × PointId)} (hsp : SPok interp diff) :
    ∀ {L L'}, LinesOk Col interp L → stepMerge diff L = some L' →
      LinesOk Col interp L' := by
  intro L
  induction L with
  | nil => intro L' _ h; simp [stepMerge] at h
  | cons s rest ih =>
    intro L' hL h
    have hs : LineOk Col interp s := hL s (by simp)
    have hrest : LinesOk Col interp rest := fun u hu => hL u (by simp [hu])
    unfold stepMerge at h
    cases hab : absorbOne diff s rest with
    | some r =>
      obtain ⟨m, rest'⟩ := r
      simp only [hab, Option.some.injEq] at h
      subst h
      obtain ⟨hmOk, hrest'Ok⟩ := absorbOne_ok hs hsp hrest hab
      intro u hu
      rcases List.mem_cons.mp hu with hum | hurest'
      · subst hum; exact hmOk
      · exact hrest'Ok u hurest'
    | none =>
      cases hsm : stepMerge diff rest with
      | none => simp [hab, hsm] at h
      | some L'' =>
        simp only [hab, hsm, Option.some.injEq] at h
        subst h
        have hL''Ok : LinesOk Col interp L'' := ih hrest hsm
        intro u hu
        rcases List.mem_cons.mp hu with hus | huL''
        · subst hus; exact hs
        · exact hL''Ok u huL''

theorem saturate_ok [ColTheory P Col] {interp : PointId → P}
    {diff : List (PointId × PointId)} (hsp : SPok interp diff) :
    ∀ (fuel : Nat) {L}, LinesOk Col interp L →
      LinesOk Col interp (saturate diff L fuel) := by
  intro fuel
  induction fuel with
  | zero => intro L hL; simpa [saturate] using hL
  | succ k ih =>
    intro L hL
    rw [saturate]
    split
    · rename_i L' hL'
      exact ih (stepMerge_ok hsp hL hL')
    · exact hL

/-- **Soundness of the reflective procedure** (the analogue of Coq `test_col_ok`):
    if every line is genuinely collinear and every recorded pair genuinely
    distinct, then a positive `decideCol` verdict is a real collinearity fact. -/
theorem decideCol_sound [ColTheory P Col] (interp : PointId → P) (st : ColState)
    (hss : LinesOk Col interp st.lines) (hsp : SPok interp st.diff)
    {a b c : PointId} (h : decideCol st a b c) :
    Col (interp a) (interp b) (interp c) := by
  obtain ⟨s, hs_mem, ha, hb, hc⟩ := h
  exact saturate_ok hsp st.lines.length hss s hs_mem a ha b hb c hc

/-! ## Establishing the precondition from raw hypotheses

`decideCol_sound` needs `LinesOk` (every line collinear in every order) and `SPok`.
A raw hypothesis `Col A B C` only gives one ordering; `lineOk_of_col` closes it up
to all 27 ordered triples of `[a,b,c]`, using `perm1`/`perm2` (the S₃ closure) and
`trivial` (the degenerate triples with a repeated point). This is the piece the
`colr` tactic uses to turn scanned `Col` hyps into `LinesOk`. -/

theorem lineOk_of_col [ColTheory P Col] {interp : PointId → P} {a b c : PointId}
    (h : Col (interp a) (interp b) (interp c)) : LineOk Col interp [a, b, c] := by
  have p1 := @ColTheory.perm1 P Col _
  have p2 := @ColTheory.perm2 P Col _
  have tr := @ColTheory.trivial P Col _
  intro x hx y hy z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;>
    first
      | exact h
      | exact p1 _ _ _ h
      | exact p1 _ _ _ (p1 _ _ _ h)
      | exact p2 _ _ _ h
      | exact p2 _ _ _ (p1 _ _ _ h)
      | exact p2 _ _ _ (p1 _ _ _ (p1 _ _ _ h))
      | exact tr _ _
      | exact p1 _ _ _ (tr _ _)
      | exact p1 _ _ _ (p1 _ _ _ (tr _ _))

/-! ## Computational sanity checks (mentor's unit tests, at the algorithm level)

These reproduce GeoCoq `Col_refl` test goals purely computationally — no proof,
just evaluating `decideCol`. Establishing the `LinesOk`/`SPok` preconditions from
real `Col`/`≠` hypotheses (via `perm1`/`perm2`/`trivial`) and wiring
`decideCol_sound` into a `colr` tactic is the next step (see the doc, M1). -/

-- `A≠B, Col A B C, Col A B D ⊢ Col B C D`  with A,B,C,D = 1,2,3,4
private def stTest : ColState := { lines := [[1, 2, 3], [1, 2, 4]], diff := [(1, 2)] }

-- merges {1,2,3} ∪ {1,2,4} on the distinct pair (1,2) ⟹ Col B C D holds
example : decideCol stTest 2 3 4 := by decide
-- transitively also Col C D A, etc.
example : decideCol stTest 3 4 1 := by decide

-- WITHOUT the distinctness fact the merge must NOT fire ⟹ Col B C D not derivable
private def stNoDiff : ColState := { lines := [[1, 2, 3], [1, 2, 4]], diff := [] }
example : ¬ decideCol stNoDiff 2 3 4 := by decide

#eval decide (decideCol stTest 2 3 4)     -- true
#eval decide (decideCol stNoDiff 2 3 4)   -- false

/-! ## End-to-end pipeline (manual)

This proves the mentor's unit-test goal `A≠B, Col A B C, Col A B D ⊢ Col B C D`
*through the reflective core* — no `Bet`-unfolding, just the closure + `decide`.
It shows the whole chain works: `lineOk_of_col` builds `LinesOk` from the raw `Col`
hyps, the `≠` hyp gives `SPok`, and `decideCol_sound` + `decide` finish. The
`colr` tactic below automates exactly this assembly. -/

section Manual
variable {P : Type*} {Col : P → P → P → Prop} [ColTheory P Col]

-- ids: A=0, B=1, C=2, D=3 ; interp maps them back
example (A B C D : P) (hab : A ≠ B) (h1 : Col A B C) (h2 : Col A B D) :
    Col B C D :=
  decideCol_sound (Col := Col) (fun n => [A, B, C, D].getD n A)
    { lines := [[0, 1, 2], [0, 1, 3]], diff := [(0, 1)] }
    (by intro s hs; fin_cases hs <;>
        first | exact lineOk_of_col h1 | exact lineOk_of_col h2)
    (by intro pq hpq; fin_cases hpq; exact hab)
    (a := 1) (b := 2) (c := 3) (by decide)

end Manual

/-! ## The `colr` tactic

Automates the assembly above. It scans the local context for `Col _ _ _` facts
(→ lines) and `_ ≠ _` facts (→ distinct pairs), interns the point terms to `Nat`
ids, builds the `interp`/`ColState`, and closes the goal via `decideCol_sound` with
`decide`. The `Col`/`ColTheory` instance is read off the goal, so the tactic works
for any `ColTheory` (the abstract one here, and later the Tarski instance). -/

open Lean Elab Tactic Meta in
elab "colr" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    -- `mvarId.getType` can come back wrapped in `Expr.mdata` (e.g. a
    -- `noImplicitLambda` marker the elaborator attaches to goals synthesized
    -- through certain nested-tactic paths, such as `have ... := by rcases ...`
    -- case splits). `getAppArgs`/`isApp` do NOT see through `mdata`, so an
    -- un-consumed goal here silently looks like a 0-argument application and
    -- trips the arity check below even though the goal genuinely is
    -- `Col A B C`. `consumeMData` strips any such wrapper first.
    let goalType := (← instantiateMVars (← mvarId.getType)).consumeMData
    let gArgs := goalType.getAppArgs
    if gArgs.size < 3 then
      -- NB: `colr` only ever proves a *positive* `Col A B C` goal — it cannot
      -- prove `¬ Col A B C` (the reflective closure is sound in one direction
      -- only: `decideCol = true → Col`; `decideCol = false` does not entail
      -- `¬ Col`, so a negative prover would be unsound). If you have a `¬ Col`
      -- goal, `intro`/case on it first, or discharge it via
      -- `exact hNCol (by colr)` against the positive fact that contradicts it.
      throwError m!"colr: goal is not of the form `Col _ _ _` (got `{goalType}`) — \
        colr only proves positive `Col` goals, never `¬ Col`; if this is a \
        negation, restructure to a positive `Col` sub-goal (e.g. `exact hNCol (by colr)`)"
    let a := gArgs[gArgs.size - 3]!
    let b := gArgs[gArgs.size - 2]!
    let c := gArgs[gArgs.size - 1]!
    let colHead := mkAppN goalType.getAppFn (gArgs.extract 0 (gArgs.size - 3))
    -- fast-fail if the goal's relation is not a `ColTheory` (so `colr` is safe
    -- to include in `first | …` closers without doing wasted work on `Cong`/`≠` goals)
    let P ← inferType a
    let ok ← (do let _ ← synthInstance (← mkAppM ``ColTheory #[P, colHead]); pure true) <|> pure false
    unless ok do throwError "colr: goal relation has no ColTheory instance"
    let ptsRef ← IO.mkRef (#[] : Array Expr)
    let getId : Expr → TacticM Nat := fun e => do
      let pts ← ptsRef.get
      for i in [0:pts.size] do
        if ← isDefEq pts[i]! e then return i
      ptsRef.set (pts.push e)
      return pts.size
    let mut colHyps : Array (Name × Nat × Nat × Nat) := #[]
    let mut neHyps : Array (Name × Nat × Nat) := #[]
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      -- Same `mdata`-stripping as the goal above: a hypothesis whose type is
      -- still `mdata`-wrapped would otherwise be silently dropped from the
      -- scan (falls through both the `Col` check and the `Ne`/`Not` match
      -- with no error), making `colr` fail as if the fact were simply absent.
      let ty := (← instantiateMVars ldecl.type).consumeMData
      let tArgs := ty.getAppArgs
      if tArgs.size ≥ 3 then
        let head := mkAppN ty.getAppFn (tArgs.extract 0 (tArgs.size - 3))
        if ← isDefEq head colHead then
          let i ← getId tArgs[tArgs.size - 3]!
          let j ← getId tArgs[tArgs.size - 2]!
          let k ← getId tArgs[tArgs.size - 1]!
          colHyps := colHyps.push (ldecl.userName, i, j, k)
          continue
      match ty.getAppFnArgs with
      | (``Ne, #[_, x, y]) => neHyps := neHyps.push (ldecl.userName, ← getId x, ← getId y)
      | (``Not, #[e]) =>
        match e.getAppFnArgs with
        | (``Eq, #[_, x, y]) => neHyps := neHyps.push (ldecl.userName, ← getId x, ← getId y)
        | _ => pure ()
      | _ => pure ()
    let ia ← getId a
    let ib ← getId b
    let ic ← getId c
    let pts ← ptsRef.get
    if pts.isEmpty then throwError "colr: no points in goal"
    let ptStxs ← pts.mapM (fun e => Term.exprToSyntax e)
    let defaultStx := ptStxs[0]!
    let listLit ← `([$ptStxs,*])
    let interpStx ← `(fun n => List.getD $listLit n $defaultStx)
    let lineStxs ← colHyps.mapM fun (_, i, j, k) => `([$(quote i), $(quote j), $(quote k)])
    let linesStx ← `([$lineStxs,*])
    let diffStxs ← neHyps.mapM fun (_, i, j) => `(($(quote i), $(quote j)))
    let diffStx ← `([$diffStxs,*])
    let stStx ← `({ lines := $linesStx, diff := $diffStx })
    -- Every line came from *some* `Col` hyp; after `fin_cases` the residual
    -- `LineOk … [i,j,k]` goal is defeq to `lineOk_of_col` of that hyp, found by
    -- `assumption` (interp reduces the ids back to the point terms). Likewise each
    -- `SPok` goal `interp i ≠ interp j` is defeq to the originating `≠` hyp.
    let hssStx ← `(by intro s hs; fin_cases hs <;> exact lineOk_of_col (by assumption))
    let hspStx ← `(by intro pq hpq; fin_cases hpq <;> assumption)
    let term ← `(decideCol_sound $interpStx $stStx $hssStx $hspStx
        (a := $(quote ia)) (b := $(quote ib)) (c := $(quote ic)) (by decide))
    evalTactic (← `(tactic| exact $term))

/-! ## `colr` acceptance tests (mentor's unit-test goals, one-word proofs) -/

section ColReflTests
variable {P : Type*} {Col : P → P → P → Prop} [ColTheory P Col]

-- the canonical transitive-collinearity goal
example (A B C D : P) (hab : A ≠ B) (h1 : Col A B C) (h2 : Col A B D) : Col B C D := by
  colr

-- a direct hit (single line, no merge, no distinctness needed)
example (A B C : P) (h : Col A B C) : Col B C A := by colr

-- two-step merge chained through a shared distinct pair
example (A B C D E : P) (hab : A ≠ B) (h1 : Col A B C) (h2 : Col A B D) (h3 : Col A B E) :
    Col C D E := by colr

end ColReflTests

end GeocoqTranslate.Tarski.ColR
