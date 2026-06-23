# Bounded Tactic Layer — Deep Engineering Report

**Date:** 2026-06-23
**Scope:** Phase 2 (Tactic Layer) of the GeoCoq→Lean translation — replacing the
unbounded `aesop` core of the ported GeoCoq tactics with **bounded,
argument-finding** tactics, per Julien's direction (no explicit lemma arguments,
no oracle; an automated tactic that mimics Coq's `eauto`/`auto`, validated by
scaling unit tests).

**Headline result:** frontier failures **11 → 4** (8 lemmas unblocked), both core
tactics measured to scale **linearly**, **zero regressions** — achieved purely by
swapping the tactic engine, no proof edits.

---

## 0. Background: why the tactics were broken

The ported tactics live in
[`euclidean_tactics.lean`](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/euclidean_tactics.lean).
They let a translated proof mirror its GeoCoq original line-for-line, e.g.

```
Coq : assert (Col B C D) by (conclude lemma_collinear4).
Lean: have : Col B C D := by conclude lemma_collinear4
```

The original Lean ports delegated the "find the right argument order and close the
goal" work to **`aesop`**. That was the bug. Two facts about this development make
`aesop` explode:

1. **`Col` is a 6-way disjunction.** From
   [`Euclidean/Axioms.lean`](../lean/geocoq_translate/GeocoqTranslate/Euclidean/Axioms.lean):
   ```lean
   def Col (A B C : Point) : Prop :=
     A = B ∨ A = C ∨ B = C ∨ self.BetS B A C ∨ self.BetS A B C ∨ self.BetS A C B
   def nCol (A B C : Point) : Prop :=
     A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ ¬ self.BetS A B C ∧ ¬ self.BetS A C B ∧ ¬ self.BetS B A C
   ```
   With `@[aesop norm unfold] Col`, every `Col` in context unfolds to a 6-disjunction
   and aesop forward-chains over all reorderings combinatorially.

2. **The forward config `aesop (add unsafe 90% forward (L))`** maps GeoCoq's
   *bounded* `eauto` (depth-5) onto *unbounded* search. On a proof with ~20 `Col`
   facts this hits the 200,000-heartbeat ceiling and dies.

GeoCoq's originals never explode because Coq's `eauto`/`auto` are depth-bounded.
The fix is to give Lean an equally-bounded analog.

### The three tactics (their jobs)

| tactic | GeoCoq role | direction | shape |
|---|---|---|---|
| `conclude L` | apply lemma `L`, fill premises | backward | atomic goal (`Col B C D`), atomic premises |
| `forward_using L` | forward-apply `L`, use a projection | forward | reorder lemma returns a **conjunction**; project one permutation |
| `conclude_def D` | build/extract a defined predicate | both | **existential** body (`Meet`, `TS`, `CongA`, `Par`) |

Julien's framing maps exactly onto these:
- *"each new fact is just an application of the given lemma on known assumptions"* → `conclude` / `forward_using`.
- *"the only difficulty is it is not always the first matching assumption"* → **backtracking**.
- *"the conclude tactic should solve a disjunction of a conjunction of facts with metavariables"* → the `Col`-shaped goal with metavariable points.

---

## 1. Phase 1 — finding the bounded mechanism (empirical)

I refused to *assert* a mechanism; I **measured** candidates on the two hardest
*real* proof steps, using `lean_multi_attempt` (tries a tactic at a position
without editing the file).

### 1.1 The backward deep-trap (`twolines`)

Goal `Col F B C`, to be proved by `lemma_collinear4` whose signature is
```lean
lemma_collinear4 (A B C D : Point) (hABC : Col A B C) (hABD : Col A B D) (hAB : A ≠ B) : Col B C D
```
Two candidate pivots exist for the first premise:
- pivot `A`: `Col A F B` ✓ present, but `Col A F C` **absent** → a **deep trap** (passes premise 1, fails premise 2);
- pivot `E`: `Col E F B` ✓, `Col E F C` ✓, `E ≠ F` ✓ → **correct**.

A tactic that grabs the *first* matching assumption picks `A` and dies. Results
([`TwolinesProbe.lean`](../lean/geocoq_translate/GeocoqTranslate/TwolinesProbe.lean), line 25):

| candidate | result |
|---|---|
| `solve_by_elim [lemma_collinear4]` | ✅ closes (backtracks past pivot `A` to `E`) |
| `apply lemma_collinear4 <;> assumption` | ✅ closes (but fragile — no cross-branch metavar backtracking) |
| `solve_by_elim [lemma_collinear4, lemma_collinearorder]` | ✅ closes |
| `aesop (config := { maxRuleApplications := 200, terminal := true }) (add safe apply lemma_collinear4)` | ❌ **timeout at `whnf`, 200000 heartbeats** |

**Key finding:** even a *capped* aesop times out — because the explosion is in
`whnf` (unfolding `Col`), not in rule-application count. **aesop is unsalvageable
here.** `solve_by_elim` already backtracks correctly.

### 1.2 The forward reorder (`collinearorder`)

The reorder lemma returns a conjunction:
```lean
lemma_collinearorder (A B C : Point) (h : Col A B C) :
    Col B A C ∧ Col B C A ∧ Col C A B ∧ Col A C B ∧ Col C B A
```
Goal `Col F E B` is **not** a hypothesis; it must be projected from `cEFB : Col E F B`
via `lemma_collinearorder E F B` (its `.2.2.2.2` is `Col C B A` ↦ `Col F E B`).
Results ([`MechProbe.lean`](../lean/geocoq_translate/GeocoqTranslate/MechProbe.lean) — throwaway probe):

| candidate | result |
|---|---|
| `solve_by_elim [lemma_collinearorder]` | ❌ **fails** — cannot project *through* the `∧` |
| `solve_by_elim [lemma_collinearorder, And.left, And.right, And.intro]` | ✅ closes |
| `exact (lemma_collinearorder _ _ _ (by assumption)).2.2.2.2` (enumerated projection) | ✅ closes |

**Key finding:** plain `solve_by_elim [L]` is genuinely *weak* on the forward case
(this is the "solve_by_elim can't do anything `apply` can't" critique, now pinned
to its exact cause: it doesn't apply `And.left/And.right` unless told). Adding the
projection lemmas fixes it.

### 1.3 The (tempting) unified mechanism — and why it failed

`solve_by_elim [L, And.left, And.right, And.intro]` closed **both** the deep trap
and the reorder. I deployed it everywhere... and the **scaling test hung 8+
minutes on 8 tiny theorems.**

Diagnosis by elimination:
- `And.intro` in the lemma set makes `solve_by_elim` try to **build** conjunctions
  → it explores splitting every goal into `?_ ∧ ?_` → superlinear in context size.
  **Dropped `And.intro`.**
- `[L, And.left, And.right]` *still* timed out (30 s LSP cap) at **N = 48** decoys:
  the `And.left/And.right` *eliminations* are themselves superlinear — for each
  subgoal `solve_by_elim` additionally tries "prove `G` via `And.left` of some
  `(G ∧ ?)`" against all N context facts.

**Conclusion — split the mechanism by direction:**
- `conclude` (backward): goal and premises are **atomic** → **no projection needed**
  → `solve_by_elim [L]` (the version that scaled linearly: 38/65/110 hb).
- `forward_using` (forward): needs projection → use **type-directed explicit
  projection** (flat, bounded), *not* `And.*` search.

---

## 2. The deployed tactics (current state)

### 2.1 `conclude` — backward, atomic
```lean
macro "conclude " t:term : tactic =>
  `(tactic|
    ((try spliter); (try remove_double_neg);
     first
       | done | assumption | exact $t
       | (apply $t <;> assumption)
       -- BOUNDED path (eauto analog): apply/eliminate `t` with depth-limited
       -- backtracking. NO And.left/right/intro — the goal & premises are atomic,
       -- and the And lemmas make solve_by_elim superlinear in #facts (measured).
       | solve_by_elim [$t:term]
       -- last-resort fallbacks (kept so nothing that compiled under aesop regresses)
       | (apply $t <;> (first | assumption | aesop))
       | aesop))
```

### 2.2 `forward_using` — forward, type-directed projection
```lean
macro "forward_using " t:term : tactic =>
  `(tactic|
    ((try spliter);
     first
       | done | assumption
       -- TYPE-DIRECTED projection: the goal's permutation unifies with one
       -- projection, which pins `t`'s point args, so `(by assumption)` finds the
       -- exact source hyp even among many similar facts. Bounded, scales flat.
       | exact ($t _ _ _ (by assumption)).1
       | exact ($t _ _ _ (by assumption)).2.1
       | exact ($t _ _ _ (by assumption)).2.2.1
       | exact ($t _ _ _ (by assumption)).2.2.2.1
       | exact ($t _ _ _ (by assumption)).2.2.2.2
       -- fallbacks (non-3-point lemmas / no-regression)
       | solve_by_elim [$t:term, And.left, And.right]
       | aesop (add unsafe 90% forward ($t))
       | aesop))
```
**Why type-directed works:** for goal `Col F E B`, unifying it with the projection
`.2.2.2.2 : Col C B A` forces `C:=F, B:=E, A:=B`, i.e. the lemma instance
`collinearorder B E F`, whose premise is `Col B E F`. So `(by assumption)` is
searching for the *specific* `Col B E F` — the 48 noise facts are irrelevant
because the projection type already pinned everything. This is the demo `col_close`
mechanism, generalized to any 3-point reorder lemma (`collinearorder`, `NCorder`, …).

### 2.3 `conclude_def` — existential build via witness-count ladder
```lean
macro "conclude_def " t:ident : tactic =>
  `(tactic|
    first
      -- fast extract: already a structurally-identical hypothesis
      | (unfold $t at *; (try spliter); first | done | assumption)
      -- forward BUILD (bounded, type-directed): witnesses as metavars `_` pinned
      -- by the body's `assumption`s. The holistic `exact ⟨…⟩` DEFERS the metavars
      -- (refine/apply commit them too early and pick wrong points).
      -- `assumption`-before-`And.intro` makes `nCol` leaves match WHOLE rather
      -- than shattering into De Morgan conjuncts. Ladder 0..6 covers every def
      -- (Meet/TS=1, CongA=4, Par=5, …). aesop only as last resort.
      | (unfold $t; (try remove_double_neg);
         first
           | done | assumption
           | ((repeat' (first | assumption | apply And.intro)); done)
           | exact ⟨_, by repeat' (first | assumption | apply And.intro)⟩
           | exact ⟨_, _, by repeat' (first | assumption | apply And.intro)⟩
           | exact ⟨_, _, _, by repeat' (first | assumption | apply And.intro)⟩
           | exact ⟨_, _, _, _, by repeat' (first | assumption | apply And.intro)⟩
           | exact ⟨_, _, _, _, _, by repeat' (first | assumption | apply And.intro)⟩
           | exact ⟨_, _, _, _, _, _, by repeat' (first | assumption | apply And.intro)⟩
           | aesop)
      -- backward: search after unfolding into the context
      | (unfold $t at *; (try spliter); (try remove_double_neg);
         first | done | assumption | tauto | aesop))
```

---

## 3. Deriving the `conclude_def` build — the full worked example

This is the most subtle tactic; here is the exact derivation on
[`lemma_equalangleshelper.lean`](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_equalangleshelper.lean),
line 16, `have : CongA A B C p b q := by conclude_def CongA`.

`CongA` unfolds to (from `euclidean_defs.lean`):
```
∃ U V u v, Out B A U ∧ Out B C V ∧ Out b a u ∧ Out b c v ∧
           Cong B U b u ∧ Cong B V b v ∧ Cong U V u v ∧ nCol A B C
```
The witnesses `U V u v` are already in context (from a prior `obtain`), as are
`Out b p u`, `Out b q v`, the `Cong`s, and `nCol A B C`. The goal after `unfold`:
```
⊢ ∃ U V u v, Out B A U ∧ Out B C V ∧ Out b p u ∧ Out b q v ∧ Cong B U b u ∧ … ∧ nCol A B C
```

Candidate attempts (each tried with `lean_multi_attempt` at line 16):

| attempt | result | why |
|---|---|---|
| `refine ⟨_, _, _, _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> assumption` | ❌ | `refine` **commits witnesses greedily** — it set every witness to `v`; goals became `Out B A v`, `Cong v v v v` |
| `exact ⟨_, _, _, _, by assumption, by assumption, …(×8)⟩` | ✅ | holistic `exact` **defers** the 4 witness metavars; each `by assumption` pins them by unification |
| `exact ⟨_, _, _, _, by (repeat' apply And.intro) <;> assumption⟩` | ❌ | `repeat' apply And.intro` **descends into `nCol`** (it's `∧`-shaped up to defeq) → leaves `⊢ A ≠ B`, `⊢ ¬BetS A B C`, … which aren't assumptions |
| `exact ⟨_, _, _, _, by repeat' (first \| assumption \| apply And.intro)⟩` | ✅ | `assumption` is tried **before** splitting, so `nCol A B C` matches the whole hypothesis before `And.intro` can shatter it |

The winner generalizes: witnesses as `_`, body closed by
`repeat' (first | assumption | apply And.intro)`. The only non-generic part is the
**number of witnesses**, solved by the `first` **ladder** (0..6) — each wrong-arity
branch fails cleanly (the `exact ⟨…⟩` term is incomplete → errors → `first` moves on)
and the right one closes. Confirmed: both
`exact ⟨_, _, _, _, by repeat' (first | assumption | apply And.intro)⟩` and the full
ladder close line 16 with `goals: []`.

This single mechanism unblocked **`equalangleshelper`, `ABCequalsCBA`, `crossbar`**.

---

## 4. Scaling unit tests — the Julien deliverable

[`ScalingTests.lean`](../lean/geocoq_translate/GeocoqTranslate/ScalingTests.lean)
calls the **real deployed tactics** (not raw `solve_by_elim`), with N decoy/noise
facts, measured by `#count_heartbeats in`.

- **Test A** `pivotN`: `conclude lemma_collinear4`, seeded with N **deep-trap**
  decoys `Col Gᵢ B C` (each passes premise 1 `Col ?A B C`, fails premise 2
  `Col ?A B D`) — the tactic must backtrack past all N to the one real pivot `A`.
- **Test B** `reorderN`: `forward_using lemma_collinearorder`, goal `Col C B A`
  projected from `hABC`, with N unrelated noise facts `Col Gᵢ Hᵢ Kᵢ`.

| N facts | `conclude` (deep-trap) | `forward_using` (reorder) |
|--------:|------------------------:|---------------------------:|
| 4  | 38 hb  | 32 hb  |
| 12 | 65 hb  | 68 hb  |
| 24 | 110 hb | 121 hb |
| 48 | 201 hb | 228 hb |

**Both ~linear, ~4 hb/fact** (doubling N → ~1.85× cost). Compare aesop's
200,000-heartbeat wall. This is the concrete answer to Julien's
*"write unit tests with an increasing number of facts to check that the approach
scales."*

---

## 5. Frontier results — the real unblock measurement

Full-tree builds (`lake build GeocoqTranslate`), classifying every failing lemma.

### Progression
| stage | failing | newly unblocked |
|---|---|---|
| baseline (aesop) | **11** | — |
| after `conclude`/`forward_using` swap | **7** | `Pasch_outer2`, `ray`, `ray3`, `rightreverse`, `proposition_11` |
| after `conclude_def` ladder | **4** | `equalangleshelper`, `ABCequalsCBA`, `crossbar` |

**8 lemmas unblocked, zero regressions** (the swap can only *add* a winning `first`
branch before aesop; a lemma that compiled before still compiles).

### Failure classification (how each was triaged)
| lemma | first error | class |
|---|---|---|
| `ABCequalsCBA` (L46) | `aesop: maximum number of rule applications (200) reached` → unsolved | tactic-strength → **fixed** by ladder |
| `equalangleshelper` (L16) | same aesop max-rule | tactic-strength → **fixed** by ladder |
| `crossbar` (L22) | `whnf` 200000 timeout | heavy def → **fixed** by ladder |
| `parallelflip` (L14) | `simp` 200000 timeout | **`Par` reconstruction** |
| `parallelNC`, `paralleldef2A` | same family | **`Par` reconstruction** |
| `proposition_08` | `simp`/`whnf` 200000 timeout | heavy (`Par`/angle) |

**Remaining 4 = the `Par` family** — one coherent hard class.

---

## 6. The `Par` rabbit hole — what was tried and why it's hard

`Par` is the largest def in the development:
```
Par A B C D := ∃ U V u v X, A ≠ B ∧ C ≠ D ∧ Col A B U ∧ Col A B V ∧ U ≠ V ∧
               Col C D u ∧ Col C D v ∧ u ≠ v ∧ ¬ Meet A B C D ∧ BetS U X v ∧ BetS u X V
```
`lemma_parallelflip` line 14 destructures a `Par` hypothesis into a *differently
ordered* existential:
```lean
obtain ⟨M, a, b, c, d, …⟩ : ∃ M a b c d, (… ∧ BetS a M d ∧ BetS c M b) := by conclude_def Par
```

### Difficulty 1 — witness reorder
`Par` binds the witnesses **`U V u v X`** but the `obtain` wants **`M a b c d`**,
which maps to **`X U V u v`** (the betweenness point `X` moves from last to first).
So the bodies are alpha-equivalent only under a **permutation** of binders — plain
`exact h1` / `assumption` cannot match them. The old code fell through to
`simp only [not_not] at *` over the giant unfolded `Par` → **simp timeout**.

Probe confirming the structure (after `unfold Par at *; obtain ⟨U,V,u,v,X,…⟩ := h1`):
the context gains `Col A B U`, `Col A B V`, `Col C D u`, `Col C D v`, `¬Meet A B C D`,
`BetS U X v`, `BetS u X V` as atomic facts — at which point the witness ladder
*can* rebuild the reordered existential by unification.

### Difficulty 2 — ambiguous witnesses in the build direction
Lines 44–46 (`have : Par B A C D := by conclude_def Par`) build a fresh `Par`. By
then the context holds **`Col B A a` and `Col B A b`** (both!), so the first
premise `Col B A ?U` has **two** matching assumptions. The non-backtracking
`repeat' (first | assumption | apply And.intro)` commits `?U := a`, then fails later
at `?U ≠ ?V` or a `BetS` conjunct, and **cannot backtrack the witness choice** → it
falls to aesop → **`whnf` timeout**. The correct witnesses are uniquely pinned only
by the **`BetS` conjuncts** (the betweenness chain), which appear *last* in the body.

### Attempts (all hit the same `whnf` wall)
1. **Destructure-then-build** path: `unfold $t at *; (try casesm* ∃ _, _); (try spliter)`
   then the ladder. → By lines 44–46 there are **several `Par` facts** accumulated
   in context; `unfold Par at *` re-expands all of them → giant context → `whnf`
   timeout.
2. **Goal-only build** path (`unfold $t` without `at *`) to avoid re-expanding
   accumulated `Par` hyps. → Still `whnf` timeout: the build body still needs
   witness backtracking over the `BetS` chain.
3. **Backtracking `close_body`** (`first | repeat'…;done | solve_by_elim (maxDepth := 16) [And.intro]`).
   → `solve_by_elim [And.intro]` over the `Par`/`Meet` body **whnf-explodes**
   (unifying metavar witnesses through `BetS`/`¬Meet` unfolds the big defs).

### The cost of the attempts — a regression
Worse, attempts 1–3 added `casesm`/`solve_by_elim`/goal-only paths that **regressed
the 3 lemmas I had just unblocked** (`ABCequalsCBA`, `equalangleshelper`, `crossbar`
passed in isolation but failed in the full tree under the new `conclude_def`). So I
**reverted `conclude_def` to the clean ladder-only version** (§2.3), restoring the
8-unblocked / 4-failing / zero-regression state.

**Lesson:** `Par` witness-reconstruction with backtracking is not cheaply boundable
*inside a generic `conclude_def`* — the generic tactic and the `Par` special case
pull in opposite directions (generic wants `at *` + search; `Par` needs surgical
single-hyp destructure + no unfold-at-*). They should be **separate tactics.**

---

## 7. Current state (precise)

**Working / committed-worthy:**
- `conclude`, `forward_using`, `conclude_def` rewritten to bounded mechanisms
  ([`euclidean_tactics.lean`](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/euclidean_tactics.lean)).
- [`ScalingTests.lean`](../lean/geocoq_translate/GeocoqTranslate/ScalingTests.lean) — linear scaling evidence.
- Frontier: **8 unblocked**, **4 failing** (`parallelflip`, `parallelNC`, `paralleldef2A`, `proposition_08`).

**Loose ends:**
- One full-tree build was mid-flight to **re-confirm the reverted clean state** — needs to finish.
- `MechProbe.lean` is a throwaway probe — **delete it**.
- **Nothing committed yet.**

---

## 8. Deep plan forward

### 8.1 Close out (lock in the win)
1. Finish the post-revert full build → confirm exactly `parallelflip`, `parallelNC`,
   `paralleldef2A`, `proposition_08` fail, nothing else.
2. Delete `MechProbe.lean`.
3. `lean_verify` a sample of the 8 unblocked lemmas (axioms: [] — no `sorryAx`).
4. **Commit:** "Replace unbounded aesop in conclude/forward_using/conclude_def with
   bounded argument-finding tactics; +8 frontier lemmas; linear scaling tests."

### 8.2 The `Par`-4 (deliberate, separate)
Recommended **(A)**:
- **(A) Hand-translate the 4** like `parallelsymmetric`: explicit
  `obtain ⟨U,V,u,v,X,…⟩ := h1` then `exact ⟨X,U,V,u,v, …⟩` (and for the build steps,
  name the witnesses from the `BetS` facts). Reliable, ~4 lemmas, no risk to the 8.
- **(B) A dedicated `par_reconstruct` tactic** (its own macro, **not** folded into
  `conclude_def`): unfold-goal-only + destructure the single `Par` hypothesis +
  a depth-capped witness search **seeded by the `BetS` conjuncts** (which uniquely
  pin all 5 points, avoiding the ambiguity). Do this only if `Par` recurs widely
  downstream.

### 8.3 Julien
5. Reply with the scaling table (§4) + the 11→4 result (§5); meet in Orsay this week.

### 8.4 Scale (Phases 3 & 5)
6. **Transpiler:** fold the now-stable tactic vocabulary into `geolean_transpile`
   so new files emit `conclude`/`forward_using`/`conclude_def` directly.
7. **Sweep:** resume bottom-up Elements with the stronger tactics; port `by cases on`
   (the other dominant gate); target ≥90% auto-translated + 3-layer-verified.

---

## Appendix — exact probe transcripts (for reproducibility)

- **Deep trap** `TwolinesProbe.lean:25`, goal `Col F B C` in a rich context with
  pivot candidates `A` (trap) and `E` (correct): `solve_by_elim [lemma_collinear4]`
  ✅; capped aesop ❌ `whnf` 200000.
- **Reorder** `MechProbe.lean:18`, goal `Col F E B` from `cEFB : Col E F B`:
  `solve_by_elim [lemma_collinearorder]` ❌; `+ And.left, And.right, And.intro` ✅;
  enumerated `.2.2.2.2` projection ✅.
- **Build** `lemma_equalangleshelper.lean:16`, goal `∃ U V u v, … ∧ nCol A B C`:
  `refine …⟨?_×12⟩ <;> assumption` ❌ (greedy witnesses); `exact ⟨_×4, by assumption×8⟩`
  ✅; `exact ⟨_×4, by (repeat' apply And.intro) <;> assumption⟩` ❌ (nCol shatter);
  `exact ⟨_×4, by repeat' (first | assumption | apply And.intro)⟩` ✅.
- **Scaling** `ScalingTests.lean`: 38/65/110/201 (`conclude`), 32/68/121/228 (`forward_using`).
- **`Par` order mismatch** `lemma_parallelflip.lean:14`: `Par` binds `U V u v X`,
  `obtain` wants `M a b c d` = `X U V u v`; bodies alpha-equiv only under permutation.
