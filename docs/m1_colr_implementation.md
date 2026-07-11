# M1 — `ColR` reflective collinearity tactic in Lean 4: implementation report

Status: **complete & verified** · Artifact: [`GeocoqTranslate/Tarski_dev/ColR.lean`](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/ColR.lean)
(395 lines) · Companion to [`tarski_architecture.md`](tarski_architecture.md) · Build: `lake build GeocoqTranslate.Tarski_dev.ColR` → *Build completed successfully (2942 jobs)*, no `sorry`, no `axiom`, no `native_decide` in code.

This document specifies, at implementation level, the Lean port of GeoCoq's `ColR`
reflective decision procedure for collinearity. Sources ported:
`theories/Coinc/ColR.v` (1501 LOC reflective core) and `theories/Main/Tactics/ColR.v`
(the Ltac driver `Col_refl`). The port is **not** line-by-line; it re-derives the
same algorithm and soundness on Lean-native data structures. Correspondences to the
Coq originals are given throughout.

---

## 0. What M1 delivers

A single self-contained file providing:

1. `ColTheory` — the abstract interface (= Coq `Col_theory`), 4 fields.
2. A **decidable** collinearity-closure procedure `decideCol` over a `List`-based
   reflective state, with a `Decidable` instance so `decide`/`native_decide` can
   evaluate it.
3. `decideCol_sound` — the soundness theorem (= Coq `test_col_ok`), proved
   abstractly against `ColTheory` (kernel-checked, no reflection in the proof).
4. `lineOk_of_col` — lifts a single raw `Col a b c` hypothesis to the full
   per-line invariant.
5. `colr` — an `elab` tactic that scrapes the goal + context, reifies them into
   a `ColState`, and closes the goal through `decideCol_sound`.
6. An acceptance test set: GeoCoq `Col_refl` unit-test goals as one-word
   `by colr` proofs, plus `#eval`/`decide` checks of the raw procedure.

The whole pipeline is exercised end-to-end: the canonical transitive-collinearity
goal `A ≠ B, Col A B C, Col A B D ⊢ Col B C D` — which the previous aesop-over-`Bet`
`Col` closer could not do — is discharged by `colr`.

---

## 1. The interface: `ColTheory` (ColR.lean:27–32)

```lean
class ColTheory (P : Type*) (Col : P → P → P → Prop) : Prop where
  trivial : ∀ A B, Col A A B
  perm1 : ∀ A B C, Col A B C → Col B C A
  perm2 : ∀ A B C, Col A B C → Col A C B
  col3 : ∀ X Y A B C, X ≠ Y → Col X Y A → Col X Y B → Col X Y C → Col A B C
```

Exact image of Coq `Col_theory` (`theories/Coinc/tactics_axioms.v`):

| Lean field | Coq field | meaning |
|---|---|---|
| `trivial`  | `CTcol_trivial`       | `Col A A B` (degenerate collinearity) |
| `perm1`    | `CTcol_permutation_1` | rotate `ABC ↦ BCA` |
| `perm2`    | `CTcol_permutation_2` | swap `ABC ↦ ACB` |
| `col3`     | `CTcol3`              | two lines sharing 2 distinct points coincide |

`⟨perm1, perm2⟩` generate the full symmetric group S₃ acting on a collinear triple
(§6); `col3` is the mathematical content of the merge rule (§4.1); `trivial` covers
degenerate triples. It is a `Prop`-valued class (all fields are proofs), so instances
are erased and carry no data.

**Design note.** The procedure is parametric over `(P, Col)`. The geometry never
enters the core — the Tarski instance `ColTheory Tpoint Col` is a *separate* artifact
(pending; needs `col3` proven Lean-side, currently `sorry` in `Ch04_col`). This is
what makes the same `colr` reusable across models.

---

## 2. Reflective representation (ColR.lean:40–44)

```lean
abbrev PointId := Nat
structure ColState where
  lines : List (List PointId)          -- Coq `ss : SS.t`   (set of lines)
  diff  : List (PointId × PointId)     -- Coq `sp : SP.t`   (distinct pairs)
```

- A **line** `List PointId` is a bag of point-ids asserted mutually collinear
  (Coq: an `S.t`, a set of `positive`).
- `lines` is the working set of lines (Coq `ss`, an `SS.t` = set of sets).
- `diff` is the set of pairs known distinct (Coq `sp`, an `SP.t` = set of pairs).

**Divergence from Coq — deliberate.** Coq builds ordered-set ADTs via `MSetAVL`/
`MSetList` functors (`theories/Coinc/Utils/sets.v`, 36 KB) purely so `vm_compute`
runs fast on canonical representations. We drop all of that: `List` is directly
computable, and we let `decide` / `native_decide` evaluate the closure at each call
site. Consequences:
- No ordering/canonicity invariants to maintain or prove.
- Membership is `List.Mem` (decidable over `Nat`), so `∃ … ∈ …` predicates are
  auto-`Decidable`.
- The soundness proof (§5) never mentions AVL invariants — it is pure induction over
  `List`.

`interp : PointId → P` (Coq `interp : positive → COLTpoint`) maps ids back to points;
it is supplied at the call site, not stored in `ColState`.

---

## 3. The algorithm (ColR.lean:46–95)

### 3.1 `sharesDiffPair` — the merge precondition (48–52)

```lean
def sharesDiffPair (diff) (s t : List PointId) : Prop :=
  ∃ pq ∈ diff, pq.1 ∈ s ∧ pq.2 ∈ s ∧ pq.1 ∈ t ∧ pq.2 ∈ t
instance (diff s t) : Decidable (sharesDiffPair diff s t) := by
  unfold sharesDiffPair; infer_instance
```

`s` and `t` share a *known-distinct* pair `(p,q)` — both endpoints lie in each line.
Coq computes this with `pick_line (S.inter s1 s2) sp` (a distinct pair inside the
intersection); we inline the intersection as “`pq.1,pq.2` in both `s` and `t`”. The
`Decidable` instance is derived (a bounded `∃` over `List` + decidable `Nat`
membership), which is why `if sharesDiffPair …` type-checks in `absorbOne`.

### 3.2 `absorbOne` — merge `s` with one compatible later line (54–65)

```lean
def absorbOne (diff) (s : List PointId) :
    List (List PointId) → Option (List PointId × List (List PointId))
  | []      => none
  | t :: ts =>
    if sharesDiffPair diff s t then some (s ++ t, ts)
    else match absorbOne diff s ts with
         | some (m, ts') => some (m, t :: ts')
         | none          => none
```

Scans `ts` for the first line sharing a distinct pair with `s`; returns the merged
line `s ++ t` (union, with duplicates — harmless: membership is all the invariant
cares about) and the remaining lines. Structural recursion on the list ⇒ trivially
terminating. Corresponds to Coq `pick_lines_aux`.

### 3.3 `stepMerge` — one global saturation step (67–78)

```lean
def stepMerge (diff) : List (List PointId) → Option (List (List PointId))
  | []        => none
  | s :: rest =>
    match absorbOne diff s rest with
    | some (m, rest') => some (m :: rest')
    | none            => match stepMerge diff rest with
                         | some L' => some (s :: L')
                         | none    => none
```

Tries to absorb from the head `s`; if `s` is inert, recurses into `rest`, threading
`s` back on. Returns `some L'` when *some* merge happened (⇒ `|L'| = |L| − 1`), `none`
when the whole set is saturated. Corresponds to Coq `pick_lines` + the merge branch of
`identify_lines`.

> The earlier draft used `(stepMerge diff rest).map (s :: ·)`; it was rewritten to an
> explicit nested `match` because `Option.map` fought the case-splitting in the
> soundness proof (`split`/`Option.map_some'` friction). Behaviourally identical.

### 3.4 `saturate` — fuel-bounded fixpoint (80–88)

```lean
def saturate (diff) (lines) : Nat → List (List PointId)
  | 0        => lines
  | fuel + 1 => match stepMerge diff lines with
                | some lines' => saturate diff lines' fuel
                | none        => lines
```

Iterates `stepMerge` to a fixpoint. Coq `identify_lines ss sp n` proves the fuel
`n := |ss|` is enough by a cardinality argument (each merge drops `SS.cardinal` by 1);
we take the same fuel at the call site (`decideCol` below passes `st.lines.length`).
Because soundness (§5) holds for **any** fuel, we do not need to *prove* the fuel
suffices — under-fuelling could only make the procedure incomplete, never unsound.
Structural recursion on `fuel : Nat`.

### 3.5 `decideCol` — the decision (90–95)

```lean
def decideCol (st : ColState) (a b c : PointId) : Prop :=
  ∃ s ∈ saturate st.diff st.lines st.lines.length, a ∈ s ∧ b ∈ s ∧ c ∈ s
instance (st a b c) : Decidable (decideCol st a b c) := by
  unfold decideCol; infer_instance
```

Saturate with fuel `|lines|`, then ask whether some resulting line contains all three
query ids. Coq `test_col`. Note `decideCol` is a **`Prop`** with a derived `Decidable`
instance (not a `Bool`); this lets call sites write `by decide` and lets
`decideCol_sound` take `h : decideCol …` directly. The instance is what `by decide`
runs; it touches only `Nat` data — **`interp` and the geometry never appear in the
computation**, only in the soundness statement.

---

## 4. Invariants (ColR.lean:103–116)

```lean
variable {P : Type*} {Col : P → P → P → Prop}

def LineOk  (Col) (interp) (s : List PointId) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, Col (interp a) (interp b) (interp c)
def LinesOk (Col) (interp) (L : List (List PointId)) : Prop :=
  ∀ s ∈ L, LineOk Col interp s
def SPok (interp) (diff : List (PointId × PointId)) : Prop :=
  ∀ pq ∈ diff, interp pq.1 ≠ interp pq.2
```

Exact Lean forms of Coq's `ss_ok` / `sp_ok` (`theories/Coinc/ColR.v:366–372`):

- `LineOk` = Coq `∀ p1 p2 p3, S.mem p1 s ∧ … → CTCol (interp p1)(interp p2)(interp p3)`
  — *every ordered triple* on a line is collinear. The “every ordering” strength is
  essential: it is exactly what makes the merge and the final read-off go through
  without permutation bookkeeping.
- `LinesOk` = `ss_ok`: every line is `LineOk`.
- `SPok` = `sp_ok`: every recorded pair is genuinely distinct under `interp`.

---

## 5. Soundness (ColR.lean:118–230)

Goal: `decideCol_sound` (= Coq `test_col_ok`). The proof is a 4-lemma chain; each
step is a `List` induction. **No `Decidable`/`decide`/reflection appears in any of
these proofs** — they are ordinary kernel-checked term proofs, so the trusted base of
the *theorem* is just the Lean kernel + `ColTheory`.

### 5.1 `lineOk_append` — the merge rule is sound (120–134)

```lean
theorem lineOk_append [ColTheory P Col] (hs : LineOk Col interp s)
    (ht : LineOk Col interp t) (hsp : SPok interp diff)
    (hshare : sharesDiffPair diff s t) : LineOk Col interp (s ++ t)
```

The heart of the whole file, and **the only use of `col3`**. Given the shared
distinct pair `(p,q)` (so `interp p ≠ interp q` by `SPok`), every `x ∈ s ++ t` is
collinear with `p,q`:

- if `x ∈ s`: `p,q,x ∈ s` and `s` is `LineOk` ⇒ `Col (interp p)(interp q)(interp x)`;
- if `x ∈ t`: symmetric via `t`.

(`List.mem_append` does the case split — ColR.lean:130.) Then for any `a,b,c ∈ s++t`,
`col3` with `interp p ≠ interp q` and the three `Col (interp p)(interp q)(interp ·)`
facts yields `Col (interp a)(interp b)(interp c)` (line 134). This is precisely
“two lines through two distinct points are one line.”

### 5.2 `absorbOne_ok` (136–171)

```lean
absorbOne diff s rest = some (m, rest') →
  LineOk … m ∧ LinesOk … rest'      -- given LineOk s, SPok, LinesOk rest
```

Induction on `rest`. The `t :: ts` step splits on `sharesDiffPair diff s t`
(`by_cases` + `rw [if_pos/if_neg]`, lines 150/158):
- **hit**: `m = s ++ t`, `rest' = ts`; `LineOk m` from `lineOk_append`, `LinesOk ts`
  by weakening (lines 152–156).
- **miss**: recurse via `ih` on `ts`; the returned lines get `t` prepended, still
  `LineOk` (lines 159–171).

Option/pair equalities are peeled with `simp only [hx, Option.some.injEq,
Prod.mk.injEq]` and the goals closed by `subst`.

### 5.3 `stepMerge_ok` (173–205)

```lean
stepMerge diff L = some L' → LinesOk … L → LinesOk … L'
```

Induction on `L`. `cases` on `absorbOne diff s rest`: the success branch invokes
`absorbOne_ok` (line 190); the failure branch `cases` on `stepMerge diff rest` and
uses `ih` (line 201). Same `simp only [hab, hsm, Option.some.injEq]` + `subst`
discipline.

### 5.4 `saturate_ok` (207–220)

```lean
LinesOk … L → LinesOk … (saturate diff L fuel)     -- for every fuel
```

Induction on `fuel`. `zero`: identity. `succ`: `split` on `stepMerge`; the merge
branch chains `stepMerge_ok` then `ih` (line 219). This is the invariant-preservation
analogue of Coq `identify_lines_ok`, but with fuel induction replacing the
strong-cardinality induction (Coq `strong_induction`) — cheaper, because we do not
need the fixpoint-reached property, only monotonicity.

### 5.5 `decideCol_sound` (222–230)

```lean
theorem decideCol_sound [ColTheory P Col] (interp) (st)
    (hss : LinesOk Col interp st.lines) (hsp : SPok interp st.diff)
    (h : decideCol st a b c) : Col (interp a) (interp b) (interp c) := by
  obtain ⟨s, hs_mem, ha, hb, hc⟩ := h
  exact saturate_ok hsp st.lines.length hss  s hs_mem  a ha b hb c hc
```

Destructure the `decideCol` witness (a saturated line `s ∋ a,b,c`); `saturate_ok`
gives `LinesOk` of the saturated set, hence `LineOk s`, hence
`Col (interp a)(interp b)(interp c)`. One line of glue.

---

## 6. `lineOk_of_col` — raw hypothesis ⇒ line invariant (232–258)

```lean
theorem lineOk_of_col [ColTheory P Col] (h : Col (interp a) (interp b) (interp c)) :
    LineOk Col interp [a, b, c]
```

`decideCol_sound` needs `LinesOk` (every line collinear in *every order*), but a
context hypothesis `Col A B C` gives only one ordering. This lemma closes the gap: it
proves all `3³ = 27` ordered triples of `[a,b,c]`.

Mechanism (lines 245–258): `intro x hx y hy z hz`; reduce `∈ [a,b,c]` to
`x = a ∨ x = b ∨ x = c` (`simp only [List.mem_cons, List.not_mem_nil, or_false]`);
`rcases … <;> rcases … <;> rcases …` explodes the 27 cases; a single `first | …`
combinator closes them all from a fixed toolkit:

- the **6 genuine permutations** of `h` — `h`, `p1 h`, `p1 (p1 h)`, `p2 h`,
  `p2 (p1 h)`, `p2 (p1 (p1 h))` — which realise all of S₃ from the two generators
  `perm1`,`perm2`;
- the **degenerate triples** (some id repeated), from `trivial` and its perms:
  `tr`, `p1 tr`, `p1 (p1 tr)`.

Nine alternatives suffice for all 27 goals (the linter confirmed candidates 10–12 were
unreachable and they were removed). This is the Lean analogue of GeoCoq deriving
`CTcol_permutation_1..5` + `CTcol_trivial_1/2` inside `Section Col_refl`
(`ColR.v:325–366`); there it is used to justify `collect_cols`, here to build the
initial `LinesOk`.

---

## 7. The `colr` tactic (ColR.lean:313–375)

`elab "colr" : tactic`. This is the reification driver, the analogue of Coq's
`Col_refl` Ltac (`theories/Main/Tactics/ColR.v`), but Coq builds the reified sets *in
the proof term* via `collect_cols`/`collect_diffs`; we build them as **syntax** and
let elaboration + `decide` finish. Walkthrough:

**(a) Parse the goal (317–324).** `getAppArgs` on the goal; the last three args are the
query points `a,b,c`; `colHead := mkAppN goalType.getAppFn (args.drop-last-3)` is the
`Col` (with any leading implicit/instance args) used to recognise hypotheses. Works
whether `Col` is a section variable (abstract case, 0 leading args) or a fully-applied
constant `@Col Tpoint inst` (Tarski case).

**(b) Point interning (325–331).** An `IO.Ref (Array Expr)` plus

```lean
getId e := for i in [0:pts.size] do if ← isDefEq pts[i]! e then return i
           pts.push e; return pts.size
```

assigns each *definitionally distinct* point term a stable `Nat` id. Using `isDefEq`
(not syntactic `==`) means `interp`-equal points collapse correctly — important once
substitutions/`Bet`-permutations enter.

**(c) Context scraping (332–355).** Iterate the local context (skipping
implementation-detail decls):
- if a hyp type is `colHead x y z` up to `isDefEq` on the head (line 340) → record a
  line `(name, id x, id y, id z)`;
- if it is `@Ne _ x y` **or** `@Not (@Eq _ x y)` (lines 346–352) → record a distinct
  pair `(name, id x, id y)`. Both surface forms of `≠` are matched.

Query points `a,b,c` are also interned (353–355) so their ids exist even if they
appear in no hypothesis.

**(d) Reify to syntax (356–366).**
- `interp := fun n => List.getD [p₀,…,p_{k−1}] n p₀` — point terms are emitted via
  `Term.exprToSyntax` (robust for fvars and compound terms); `p₀` is the default.
  Crucially `interp id_x` **reduces definitionally** to the point term `x`.
- `ColState` literal `{ lines := [[i,j,k], …], diff := [(i,j), …] }` with `Nat`
  literals via `quote`.

**(e) Discharge the preconditions uniformly (367–372).** No per-hypothesis term
building — two fixed scripts exploit the defeq from (d):

```lean
hss := by intro s hs; fin_cases hs <;> exact lineOk_of_col (by assumption)
hsp := by intro pq hpq; fin_cases hpq <;> assumption
```

After `fin_cases`, each `hss` subgoal is `LineOk Col interp [i,j,k]`; `lineOk_of_col`
reduces its premise to `Col (interp i)(interp j)(interp k)`, which is **defeq** to the
originating `Col …` hypothesis, so `by assumption` finds it. Likewise each `hsp`
subgoal `interp i ≠ interp j` is defeq to the originating `≠` hypothesis. This is the
key simplification that made the tactic tractable: correctness of the line/pair
*ordering* is delegated to defeq + `assumption`, not tracked in metaprogramming. (It
also handles the empty-context edge: `fin_cases` on `∈ []` yields 0 goals.)

**(f) Assemble (373–375).**

```lean
exact decideCol_sound $interp $st $hss $hsp (a := ⟨ia⟩) (b := ⟨ib⟩) (c := ⟨ic⟩) (by decide)
```

`Col` and the `ColTheory` instance are inferred: after fixing `a,b,c := ia,ib,ic`, the
result type `Col (interp ia)(interp ib)(interp ic)` reduces to the goal `Col a b c`,
which pins the implicit `Col`; the instance is then synthesised. The residual
`decideCol st ia ib ic` is closed by `by decide` (kernel evaluation of the closure).

**Trusted base of a `colr` proof.** kernel + `ColTheory` instance + `Decidable`
instances; `by decide` is kernel reduction (no compiler). Swapping to `native_decide`
(for large instances, §9) would add the compiler — an opt-in per call, not baked into
soundness.

---

## 8. Tests & verification (ColR.lean:260–393)

- **Raw-procedure checks** (267–280): `decideCol stTest 2 3 4` (merge fires) and
  `¬ decideCol stNoDiff 2 3 4` (no distinct pair ⇒ no merge) by `decide`, plus
  `#eval` printing `true`/`false`. These are GeoCoq `Col_refl` scenarios at the
  algorithm level.
- **Manual end-to-end** (290–301): the canonical goal proved by hand through
  `decideCol_sound` — documents exactly what the tactic assembles.
- **`colr` acceptance** (379–393): three one-word proofs — the canonical
  transitive merge `Col B C D`; a direct single-line hit `Col B C A`; a two-step merge
  `Col C D E` from three `Col A B _` lines sharing `(A,B)`.

Verification performed:
- `lake build GeocoqTranslate.Tarski_dev.ColR` → **success (2942 jobs)**, olean
  produced.
- `grep -nE '\bsorry\b|\badmit\b'` → none. `native_decide` → docstring only.
- LSP diagnostics clean (only the two intended `#eval` infos).

---

## 9. Known limitations / not yet done (feeds M1-finish and M2)

1. **No Tarski `ColTheory` instance yet.** Acceptance tests use the abstract
   `[ColTheory P Col]`. Instantiating for Tarski needs `col3` (and the perms/trivial)
   proven Lean-side — currently `sorry` in `Ch04_col` (“Phase 0”). Until then
   `colr` cannot fire on a concrete Tarski goal, only abstractly.
2. **Scraping is by surface syntax.** A fact `Col A C B` present but goal needs a
   permuted form is fine (the closure permutes internally); but a collinearity
   *hidden* inside `Bet`/`Out`/definitional wrappers is not recognised until unfolded.
   GeoCoq’s driver has the same limitation (it reads `Col …` hyps).
3. **`decide`, not `native_decide`.** Fine for small goals; the ~140-point `ColR.v`
   stress goal will need `native_decide` (and a benchmark). Trivial to switch the
   final closer; left out to keep the trusted base minimal by default.
4. **Fuel = `|lines|`, no completeness proof.** Sound at any fuel; matching Coq’s
   completeness (fuel always suffices) is not needed for use and is not proved.
5. **Union keeps duplicates** (`s ++ t`). Correct (membership-only invariant) but not
   size-optimal; irrelevant at these scales.

## 10. Map

| Lines | Contents |
|---|---|
| 27–32   | `ColTheory` interface |
| 40–44   | `PointId`, `ColState` |
| 46–95   | algorithm: `sharesDiffPair`, `absorbOne`, `stepMerge`, `saturate`, `decideCol` (+ `Decidable`) |
| 103–116 | invariants `LineOk`/`LinesOk`/`SPok` |
| 118–230 | soundness chain `lineOk_append` → `absorbOne_ok` → `stepMerge_ok` → `saturate_ok` → `decideCol_sound` |
| 232–258 | `lineOk_of_col` (S₃ + degenerate closure) |
| 260–303 | raw-procedure checks + manual end-to-end |
| 313–375 | `colr` elaboration tactic |
| 379–393 | `colr` acceptance tests |
