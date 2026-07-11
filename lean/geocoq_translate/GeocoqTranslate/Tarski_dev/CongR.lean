/-
Lean port of GeoCoq's `CongR` reflective congruence tactic.

Source: `theories/Coinc/CongR.v` (reflective core) + `theories/Main/Tactics/CongR.v`.
Sibling of `ColR.lean`; see `docs/tarski_architecture.md`.

`CongR` decides *congruence closure*: given `Cong` facts, is a goal `Cong A B C D`
derivable by reflexivity / symmetry / transitivity (and endpoint swaps)? The
reflective structure is a set of **length classes** — sets of segments (point-id
pairs) known to be mutually congruent. Two classes sharing a common segment merge
(transitivity). This mirrors `ColR` but the merge needs no distinctness (`sp`/`diff`
disappear) and the closure step is `trans` instead of `col3`.

As in `ColR`: soundness is proved abstractly against the `CongTheory` interface
(kernel-checked, no reflection in the proof); `decide` only evaluates the closure at
each call site over `Nat` data.
-/
import Mathlib.Tactic

namespace GeocoqTranslate.Tarski.CongR

/-! ## The interface (GeoCoq `Cong_theory`) -/

/-- Minimal facts the congruence procedure needs, mirroring GeoCoq's `Cong_theory`
    (`theories/Coinc/tactics_axioms.v`): `Cong` is an equivalence on segment lengths
    with endpoint-swap symmetry. -/
class CongTheory (P : Type*) (Cong : P → P → P → P → Prop) : Prop where
  refl : ∀ A B, Cong A B A B
  left_comm : ∀ A B C D, Cong A B C D → Cong B A C D
  sym : ∀ A B C D, Cong A B C D → Cong C D A B
  trans : ∀ A B C D E F, Cong A B C D → Cong C D E F → Cong A B E F

/-! ## Reflective representation

A *segment* is a pair of point-ids; a *length class* is a list of mutually-congruent
segments; the state is the list of classes (GeoCoq `ss : SSP.t`). No distinctness
data — unlike `ColR`, congruence closure needs none. -/

abbrev PointId := Nat
abbrev Seg := PointId × PointId
abbrev SegClass := List Seg

/-- Classes `s` and `t` share a common segment ⇒ they are one length and merge. -/
def sharesSeg (s t : SegClass) : Prop := ∃ e ∈ s, e ∈ t

instance (s t) : Decidable (sharesSeg s t) := by unfold sharesSeg; infer_instance

/-- Merge class `s` with the first later class sharing a segment. -/
def absorbOne (s : SegClass) :
    List SegClass → Option (SegClass × List SegClass)
  | [] => none
  | t :: ts =>
    if sharesSeg s t then some (s ++ t, ts)
    else
      match absorbOne s ts with
      | some (m, ts') => some (m, t :: ts')
      | none => none

/-- One saturation step: merge some mergeable pair of classes. `none` = saturated. -/
def stepMerge : List SegClass → Option (List SegClass)
  | [] => none
  | s :: rest =>
    match absorbOne s rest with
    | some (m, rest') => some (m :: rest')
    | none =>
      match stepMerge rest with
      | some L' => some (s :: L')
      | none => none

/-- Fuel-bounded saturation (fuel = number of classes). -/
def saturate (classes : List SegClass) : Nat → List SegClass
  | 0 => classes
  | fuel + 1 =>
    match stepMerge classes with
    | some classes' => saturate classes' fuel
    | none => classes

/-- Decision: saturate, then look for a class containing both query segments. -/
def decideCong (classes : List SegClass) (a b c d : PointId) : Prop :=
  ∃ cl ∈ saturate classes classes.length, (a, b) ∈ cl ∧ (c, d) ∈ cl

instance (classes a b c d) : Decidable (decideCong classes a b c d) := by
  unfold decideCong; infer_instance

/-! ## Soundness (mirrors `ColR`, with `trans` in place of `col3`, no `SPok`). -/

variable {P : Type*} {Cong : P → P → P → P → Prop}

/-- Every ordered pair of segments in a class is congruent (GeoCoq `ss_ok`). -/
def SegClassOk (Cong : P → P → P → P → Prop) (interp : PointId → P) (s : SegClass) : Prop :=
  ∀ pq ∈ s, ∀ rw ∈ s, Cong (interp pq.1) (interp pq.2) (interp rw.1) (interp rw.2)

def SegClassesOk (Cong : P → P → P → P → Prop) (interp : PointId → P)
    (L : List SegClass) : Prop :=
  ∀ s ∈ L, SegClassOk Cong interp s

/-- Merge soundness: two congruent classes sharing a segment form one class.
    This is where `trans` is used (via a shared reference segment). -/
theorem segClassOk_append [CongTheory P Cong] {interp : PointId → P}
    {s t : SegClass} (hs : SegClassOk Cong interp s) (ht : SegClassOk Cong interp t)
    (hshare : sharesSeg s t) : SegClassOk Cong interp (s ++ t) := by
  obtain ⟨e, he_s, he_t⟩ := hshare
  -- every segment in `s ++ t` is congruent to the shared segment `e`
  have key : ∀ x ∈ s ++ t, Cong (interp x.1) (interp x.2) (interp e.1) (interp e.2) := by
    intro x hx
    rcases List.mem_append.mp hx with hxs | hxt
    · exact hs x hxs e he_s
    · exact ht x hxt e he_t
  intro pq hpq rw hrw
  exact CongTheory.trans _ _ _ _ _ _ (key pq hpq) (CongTheory.sym _ _ _ _ (key rw hrw))

theorem absorbOne_ok [CongTheory P Cong] {interp : PointId → P} {s : SegClass}
    (hs : SegClassOk Cong interp s) :
    ∀ {rest m rest'}, SegClassesOk Cong interp rest →
      absorbOne s rest = some (m, rest') →
      SegClassOk Cong interp m ∧ SegClassesOk Cong interp rest' := by
  intro rest
  induction rest with
  | nil => intro m rest' _ h; simp [absorbOne] at h
  | cons t ts ih =>
    intro m rest' hrest h
    have ht : SegClassOk Cong interp t := hrest t (by simp)
    have hts : SegClassesOk Cong interp ts := fun u hu => hrest u (by simp [hu])
    unfold absorbOne at h
    by_cases hshare : sharesSeg s t
    · rw [if_pos hshare] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hm, hrest'⟩ := h
      subst hm; subst hrest'
      exact ⟨segClassOk_append hs ht hshare, hts⟩
    · rw [if_neg hshare] at h
      cases hx : absorbOne s ts with
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

theorem stepMerge_ok [CongTheory P Cong] {interp : PointId → P} :
    ∀ {L L'}, SegClassesOk Cong interp L → stepMerge L = some L' →
      SegClassesOk Cong interp L' := by
  intro L
  induction L with
  | nil => intro L' _ h; simp [stepMerge] at h
  | cons s rest ih =>
    intro L' hL h
    have hs : SegClassOk Cong interp s := hL s (by simp)
    have hrest : SegClassesOk Cong interp rest := fun u hu => hL u (by simp [hu])
    unfold stepMerge at h
    cases hab : absorbOne s rest with
    | some r =>
      obtain ⟨m, rest'⟩ := r
      simp only [hab, Option.some.injEq] at h
      subst h
      obtain ⟨hmOk, hrest'Ok⟩ := absorbOne_ok hs hrest hab
      intro u hu
      rcases List.mem_cons.mp hu with hum | hurest'
      · subst hum; exact hmOk
      · exact hrest'Ok u hurest'
    | none =>
      cases hsm : stepMerge rest with
      | none => simp [hab, hsm] at h
      | some L'' =>
        simp only [hab, hsm, Option.some.injEq] at h
        subst h
        have hL''Ok : SegClassesOk Cong interp L'' := ih hrest hsm
        intro u hu
        rcases List.mem_cons.mp hu with hus | huL''
        · subst hus; exact hs
        · exact hL''Ok u huL''

theorem saturate_ok [CongTheory P Cong] {interp : PointId → P} :
    ∀ (fuel : Nat) {L}, SegClassesOk Cong interp L →
      SegClassesOk Cong interp (saturate L fuel) := by
  intro fuel
  induction fuel with
  | zero => intro L hL; simpa [saturate] using hL
  | succ k ih =>
    intro L hL
    rw [saturate]
    split
    · rename_i L' hL'
      exact ih (stepMerge_ok hL hL')
    · exact hL

/-- **Soundness** (GeoCoq `test_cong_ok`): a positive `decideCong` verdict, over
    congruent classes, is a real congruence fact. -/
theorem decideCong_sound [CongTheory P Cong] (interp : PointId → P)
    (classes : List SegClass) (hss : SegClassesOk Cong interp classes)
    {a b c d : PointId} (h : decideCong classes a b c d) :
    Cong (interp a) (interp b) (interp c) (interp d) := by
  obtain ⟨cl, hcl_mem, hab, hcd⟩ := h
  exact saturate_ok classes.length hss cl hcl_mem (a, b) hab (c, d) hcd

/-! ## Building a class from a raw `Cong` hypothesis

A `Cong A B C D` hyp seeds a length class. To make queries robust to endpoint
orientation (`Cong B A …` etc.), the class is closed under reversal:
`[(a,b),(b,a),(c,d),(d,c)]`. `SegClassOk` of it follows from all four segments being
congruent to the reference `(a,b)` — `refl`/`left_comm`/`sym` — then `trans`. -/

theorem congClassOk_of_cong [CongTheory P Cong] {interp : PointId → P}
    {a b c d : PointId} (h : Cong (interp a) (interp b) (interp c) (interp d)) :
    SegClassOk Cong interp [(a, b), (b, a), (c, d), (d, c)] := by
  have key : ∀ x ∈ [(a, b), (b, a), (c, d), (d, c)],
      Cong (interp x.1) (interp x.2) (interp a) (interp b) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact CongTheory.refl _ _
    · exact CongTheory.left_comm _ _ _ _ (CongTheory.refl _ _)
    · exact CongTheory.sym _ _ _ _ h
    · exact CongTheory.left_comm _ _ _ _ (CongTheory.sym _ _ _ _ h)
  intro pq hpq rw hrw
  exact CongTheory.trans _ _ _ _ _ _ (key pq hpq) (CongTheory.sym _ _ _ _ (key rw hrw))

/-! ## Raw-procedure sanity checks -/

-- `Cong A B C D, Cong C D E F ⊢ Cong A B E F` (transitivity), ids A..F = 0..5.
-- classes: {AB,CD}=[(0,1),(1,0),(2,3),(3,2)], {CD,EF}=[(2,3),(3,2),(4,5),(5,4)]
private def clsTest : List SegClass :=
  [[(0, 1), (1, 0), (2, 3), (3, 2)], [(2, 3), (3, 2), (4, 5), (5, 4)]]

-- merge on shared segment (2,3) ⟹ AB and EF in one class ⟹ Cong A B E F
example : decideCong clsTest 0 1 4 5 := by decide
-- endpoint-swapped query also holds (reversal-closed classes): Cong B A F E
example : decideCong clsTest 1 0 5 4 := by decide
-- unrelated segments are not congruent
private def clsNoLink : List SegClass :=
  [[(0, 1), (1, 0)], [(4, 5), (5, 4)]]
example : ¬ decideCong clsNoLink 0 1 4 5 := by decide

#eval decide (decideCong clsTest 0 1 4 5)     -- true
#eval decide (decideCong clsNoLink 0 1 4 5)   -- false

/-! ## The `cong_r` tactic (mirrors `colr`, 4-ary, no distinctness) -/

open Lean Elab Tactic Meta in
elab "cong_r" : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let goalType ← instantiateMVars (← mvarId.getType)
    let gArgs := goalType.getAppArgs
    if gArgs.size < 4 then
      throwError "cong_r: goal is not of the form `Cong _ _ _ _`"
    let a := gArgs[gArgs.size - 4]!
    let b := gArgs[gArgs.size - 3]!
    let c := gArgs[gArgs.size - 2]!
    let d := gArgs[gArgs.size - 1]!
    let congHead := mkAppN goalType.getAppFn (gArgs.extract 0 (gArgs.size - 4))
    -- fast-fail if the goal's relation is not a `CongTheory` (safe to include in
    -- `first | …` closers without wasted work on `Col`/`≠` goals)
    let P ← inferType a
    let ok ← (do let _ ← synthInstance (← mkAppM ``CongTheory #[P, congHead]); pure true) <|> pure false
    unless ok do throwError "cong_r: goal relation has no CongTheory instance"
    let ptsRef ← IO.mkRef (#[] : Array Expr)
    let getId : Expr → TacticM Nat := fun e => do
      let pts ← ptsRef.get
      for i in [0:pts.size] do
        if ← isDefEq pts[i]! e then return i
      ptsRef.set (pts.push e)
      return pts.size
    let mut congHyps : Array (Nat × Nat × Nat × Nat) := #[]
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let tArgs := ty.getAppArgs
      if tArgs.size ≥ 4 then
        let head := mkAppN ty.getAppFn (tArgs.extract 0 (tArgs.size - 4))
        if ← isDefEq head congHead then
          let i ← getId tArgs[tArgs.size - 4]!
          let j ← getId tArgs[tArgs.size - 3]!
          let k ← getId tArgs[tArgs.size - 2]!
          let l ← getId tArgs[tArgs.size - 1]!
          congHyps := congHyps.push (i, j, k, l)
    let ia ← getId a
    let ib ← getId b
    let ic ← getId c
    let id ← getId d
    let pts ← ptsRef.get
    if pts.isEmpty then throwError "cong_r: no points in goal"
    let ptStxs ← pts.mapM (fun e => Term.exprToSyntax e)
    let defaultStx := ptStxs[0]!
    let listLit ← `([$ptStxs,*])
    let interpStx ← `(fun n => List.getD $listLit n $defaultStx)
    let clsStxs ← congHyps.mapM fun (i, j, k, l) =>
      `([($(quote i), $(quote j)), ($(quote j), $(quote i)),
         ($(quote k), $(quote l)), ($(quote l), $(quote k))])
    let classesStx ← `([$clsStxs,*])
    let hssStx ← `(by intro s hs; fin_cases hs <;> exact congClassOk_of_cong (by assumption))
    let term ← `(decideCong_sound $interpStx $classesStx $hssStx
        (a := $(quote ia)) (b := $(quote ib)) (c := $(quote ic)) (d := $(quote id)) (by decide))
    evalTactic (← `(tactic| exact $term))

/-! ## `cong_r` acceptance tests -/

section CongReflTests
variable {P : Type*} {Cong : P → P → P → P → Prop} [CongTheory P Cong]

-- transitivity through a shared segment
example (A B C D E F : P) (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F := by
  cong_r

-- reflexive / direct
example (A B C D : P) (h : Cong A B C D) : Cong A B C D := by cong_r

-- symmetry + endpoint swap through the closure
example (A B C D : P) (h : Cong A B C D) : Cong D C B A := by cong_r

-- two-hop transitive chain
example (A B C D E F G H : P) (h1 : Cong A B C D) (h2 : Cong C D E F) (h3 : Cong E F G H) :
    Cong A B G H := by cong_r

end CongReflTests

end GeocoqTranslate.Tarski.CongR
