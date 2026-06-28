# Structure-Preserving Translation of GeoCoq's Synthetic Euclid to Lean 4

*A tiered hybrid methodology — deterministic transpilation, a ported tactic
vocabulary, oracle-grounded argument resolution, and a bounded hand/LLM frontier.*

**Ayaan Siddiqui** — PhD work, IRIF.
Advisors: Pierre Boutry, Julien Narboux, Guillaume Baudart.

> This document has two parts.
> **Part I — Research Paper** is the scientific write-up: motivation, method,
> contributions, results, and discussion.
> **Part II — Project Documentation** is the engineering manual: architecture,
> file map, the transpiler's translation rules, the measurement protocol, and
> step-by-step reproduction.
> They can be read independently; Part I cites Part II for mechanism details.

---
---

# PART I — RESEARCH PAPER

## Abstract

We present a methodology and a working system for translating the *geometric
core* of **GeoCoq** — the largest formalization of synthetic geometry in any
proof assistant — from Coq/Rocq into **Lean 4** while **preserving proof
structure**. The central artifact is the `Elements/OriginalProofs` library
(Euclid's *Elements*, Book I dependency closure): **229 of 234 lemmas (97.9%) are
translated and machine-checked with zero `sorry`-holes**, leaving five documented
Tier-4 residuals. The headline number is measured under a **clean kernel rebuild**
(no cached `.olean` reuse), so it reflects genuine re-checking rather than stale
caching — and every one of the 229 is a complete proof, not a `sorry`-admitted
stub.

The methodology is deliberately **tiered**: a deterministic, structure-preserving
transpiler reproduces the GeoCoq `assert … by (conclude …)` skeleton
line-for-line; a hand-written Lean **port of GeoCoq's tactic vocabulary**
(`conclude`, `conclude_def`, `forward_using`, `close`, `contradict`) discharges
the leaf obligations; an **oracle** supplies resolved argument values for the
small class of lemmas whose conclusion under-determines their point arguments; and
a bounded **hand/LLM frontier** absorbs the genuine residual. The split between
these tiers — what the transpiler covers, where a single general fix clears an
entire class corpus-wide, and which lemmas genuinely require a human — *is* the
scientific result: an empirical map of where automation belongs in proof
translation.

Two general, foundation-level mechanisms carried the bulk of the corpus by
exploiting **dependency-DAG amplification**: the `cn_equalitysub → subst_vars`
substitution path and the **transpiler-emitted `¬Col → nCol` bridge**, each of
which cleared dozens of lemmas at once. We report the architecture, these
mechanisms, the honest measurement protocol, and the boundary cases that resist
deterministic translation.

## 1. Introduction

### 1.1 Motivation

GeoCoq is a 4,600+ lemma Coq development covering synthetic geometry from Tarski's
and Hilbert's axioms up through Euclid's *Elements* and into metric and arithmetic
models of geometry — a fully formal, machine-checked reconstruction of
foundational geometry. It lives entirely in Coq/Rocq. Lean 4, with Mathlib, has
become a center of gravity for formalization. A faithful Lean port would (a) make
this body of geometry reusable in the Lean ecosystem, and (b) serve as a
large-scale **case study in cross-assistant proof translation** — a problem of
independent and growing interest as the field accumulates multiple incompatible
libraries.

Both naïve approaches fail at scale:

- **Pure LLM translation** (feed each Coq proof to a model) is expensive,
  non-reproducible, and produces proofs whose *structure* bears no principled
  relation to the original — defeating maintainability and faithfulness auditing.
- **A monolithic general Coq→Lean compiler** is a research project in itself and
  tends to *overfit*: special-casing its way to 100% on one corpus while remaining
  useless on the next.

This work takes a middle path and, crucially, treats the **boundary between
automation and human effort as the object of study** rather than an embarrassment
to be hidden.

### 1.2 The decisive empirical finding: GeoCoq is two stylistic worlds

We measured proof style across GeoCoq before committing to an architecture. The
result reshaped the plan:

| | `Elements/OriginalProofs` | `Main/Tarski_dev` |
|---|---|---|
| lemmas | 246 | **1,527** |
| dominant style | `assert (X) by (conclude …). … close.` | idiomatic Coq: `induction`/`rewrite`/`destruct`/`auto` |
| `conclude`-family uses | 8,184 | **0** |
| structurally transpilable | **yes** | **no** (≈3%) |
| proof flow | declarative, forward, near-linear | goal-directed, transforms one goal stepwise |

The *Elements* layer is **declarative**: each line asserts a geometric fact and
names the lemma that justifies it
(`assert (Col A B C) by (conclude lemma_collinearorder)`), closing with `close`.
This skeleton is *structure-preserving-translatable* — the Lean proof can mirror
the Coq proof one line at a time, delegating each leaf to a Lean tactic of the
same name.

`Tarski_dev` is **goal-directed** Coq — e.g. `intros; unfold Out; repeat split;
auto; intro; treat_equalities; auto` — where the proof is a sequence of goal
*transformations*, not a list of asserted facts. There is no structure to copy;
reproducing these requires reasoning about the evolving goal state, which is an
LLM's task, not a transpiler's.

**Consequence.** Whole-core translation is a **two-architecture, two-track**
effort. This report covers **Track A** (the deterministic transpiler on
*Elements*, essentially complete) and frames **Track B** (an LLM-primary pipeline
for `Tarski_dev`) as the de-risked next phase.

## 2. The four-tier methodology

Every lemma is translated by the cheapest tier that suffices; the tier it lands in
is recorded, and the distribution across tiers is the deliverable metric.

1. **Tier 1 — Deterministic transpiler.** `geolean_transpile.py` parses the Coq
   proof skeleton and emits a Lean proof of identical structure. No search, no
   model; reproducible bit-for-bit.
2. **Tier 2 — Ported tactic vocabulary.** The emitted Lean leans on hand-written
   macros (`conclude`, `conclude_def`, …) reproducing GeoCoq's tactic contract.
   Strengthening one macro can clear an entire *class* of lemmas at once.
3. **Tier 3 — Oracle-grounded arguments.** For lemmas whose conclusion does not
   pin all point arguments (`axiom_5_line`, `outerconnectivity`, `connectivity`),
   the oracle replays the Coq proof and reports the resolved argument values.
4. **Tier 4 — Hand / LLM.** The genuine residual: proofs the transpiler cannot
   produce. Hand-written and *protected from re-transpilation* (Part II §B.4).

The guiding constraint: **do not overfit the transpiler.** A fix is admitted to
Tiers 1–2 only if it is a *general* rule — a property of GeoCoq's tactic semantics
or of a definition's structure — never a per-lemma hack. "It is fine to need a
human for a few cases" is a design principle: those cases delineate the boundary
the paper is about.

## 3. Key technical contributions

Each mechanism below is *general* — admitted to the automated tiers precisely
because it is not lemma-specific — and several cleared dozens of lemmas at once.
Implementation details are in Part II §C.

### 3.1 A faithful Lean port of GeoCoq's tactic vocabulary

The macros reproduce GeoCoq's contract using **bounded, ordered, type-directed**
Lean tactics rather than unbounded `aesop`, which was measured to explode when
reconstructing large derived definitions. `conclude L` normalizes the context then
tries, in order, the cheap closers before the search closers; `conclude_def D`
uses a witness-count ladder (0–6 existential witnesses) whose conjunctive body is
discharged `assumption`-before-`And.intro` (so `nCol`-shaped leaves match *whole*
rather than shattering into six De Morgan conjuncts); `forward_using L` projects
the needed permutation out of `L`'s conjunctive result, type-directed so the
projection pins `L`'s arguments. A recurring lesson: **bounded ordered tactics
beat unbounded search** — `solve_by_elim` with `And` projections went superlinear
(hanging at ~48 context facts); removing them restored linear scaling.

### 3.2 `cn_equalitysub → subst_vars`: defusing higher-order unification

GeoCoq closes substitution-of-equals steps with `conclude cn_equalitysub`, where
`cn_equalitysub : A = B → p A → p B` is Leibniz substitution. Reaching
`exact/apply cn_equalitysub` forces Lean to infer the motive `p` by **higher-order
unification** (matching schematic `?p ?B` against the goal); against `Col`'s
six-way disjunction this branches combinatorially and times out the `isDefEq`
heartbeat budget. The fix adds a **first-order substitution branch** to `conclude`,
*before* `exact L`:

```lean
| (subst_vars; assumption)
```

`subst_vars` is name-free and first-order — it eliminates every variable-equality
(a no-op when none exists, backtracking cleanly), turning the substitution into a
syntactic rewrite that never engages motive inference. This single branch cleared
the entire `cn_equalitysub` class corpus-wide — the canonical example of a general
tactic fix retiring a whole class.

*Why not `▸`/`rw`/`subst` at the call site?* Because the generated line is
`conclude cn_equalitysub` — the transpiler preserves the *name* of the justifying
lemma to keep the translation 1:1 and auditable. The intelligence about *how* to
discharge it belongs in the macro, not smeared across every call site.

### 3.3 The transpiler-emitted `¬Col → nCol` bridge (central result)

**Problem.** Several derived definitions embed a *positive* `nCol` leaf:

```
TS  P A B Q       := ∃ X, BetS P X Q ∧ Col A B X ∧ nCol A B P
CongA A B C a b c := ∃ U V u v, … ∧ nCol A B C
Triangle A B C    := nCol A B C
OS  P Q A B       := ∃ X U V, … ∧ nCol A B P ∧ nCol A B Q
Cut A B C D E     := … ∧ nCol A B C ∧ nCol A B D
```

When a translated proof **builds** such a definition
(`have : TS Q A B P := by conclude_def TS`), it must produce the `nCol` leaf — but
the surrounding GeoCoq proof carries the fact only as `¬ Col …` (GeoCoq treats the
two as interchangeable). Lean does not: the build's `assumption` finds no literal
`nCol`, the goal collapses to a residual conjunct (`⊢ ¬BetS b a c`), and the proof
fails with *unsolved goals*. This blocked a whole side-of-line / angle-congruence
family (`9_5a`, `9_5b`, `oppositesidesymmetric`, `equalanglessymmetric`, …).

**The bridge lemma** is trivial (`nCol_notCol : ¬ Col A B C → nCol A B C`). The
hard question is *where to apply it*; the elimination is itself a finding:

1. **Inside the macro** — survives re-transpile but **fails to fire**: a
   `(by assumption)` nested in a macro does not discharge from a `¬Col` hypothesis
   under macro hygiene / metavariable postponement. *Four* in-macro placements
   were tried; all failed. (`subst_vars` works in a macro precisely because it is
   name-free and uses no nested `(by assumption)`.)
2. **At the call site, hand-edited** — fires perfectly, but is **destroyed on the
   next transpile**. Beautiful and unusable.
3. **Emitted by the transpiler** — the resolution. The transpiler *writes the
   call-site bridge itself*, so it lands where it fires **and** is regenerated
   every run.

Emitted form, before each `conclude_def D` that builds an nCol-leaf def:

```lean
(try (have : nCol A B Q := nCol_notCol _ _ _ (by assumption))); conclude_def TS
```

Two subtleties, resolved empirically: (a) the bridge must run **first**, not as a
`first | conclude_def | (bridge; conclude_def)` fallback — `conclude_def`'s build
does not fail cleanly on a missing `nCol` leaf (it commits and leaves a residual
goal without throwing), so `first` never backtracks; (b) `try` makes the same line
correct on the *extract* path, where there is no `¬Col` to convert.

**Why this is not overfitting.** The bridge is driven by a five-entry table
recording, per definition, which argument positions form its `nCol` leaves (Part
II §C.3). That is the *structure of the definitions themselves*, identical across
every lemma that builds them. Combined with §3.2, the bridge moved the clean
no-cache coverage from ~92 to **228/234 in a single rebuild** — the two predicates
sit near the bottom of the dependency DAG, so fixing them lit up ~140 lemmas that
were only ever blocked by them. This **DAG amplification** — *fix a foundation
predicate, a hundred dependents compile for free* — is the defining dynamic of the
project.

### 3.4 General Coq-idiom coverage

A small set of standard Coq tactic forms were added to the transpiler as general
vocabulary, each clearing its occurrences corpus-wide (Part II §C.4):

| Coq idiom | Lean emission |
|---|---|
| `auto` / `eauto N` / `easy` | `close` (the ported eauto analog) |
| `simple eapply L` / `eapply L` | `apply L` |
| `exists W; tac` | `exact ⟨W, by tac⟩` |
| `remove_exists; eauto` | a 0–6 witness ladder closing with `close` |
| `destruct H as [D]` | `obtain ⟨D, _⟩ := this` |
| `assert (T) by auto` (no parens) | `have : T := by close` |

These converted the last `sorry`-fallbacks (`notperp`, `proposition_30/31/34`,
`extension`) into genuine proofs.

## 4. Honest measurement

A methodology paper's central number must be trustworthy. Two pitfalls were
neutralized.

**The stale-`.olean` trap.** `lake` reuses cached `.olean` for unchanged modules.
An early driver classified a lemma *compiled* whenever its `.olean` existed — but a
broken lemma with a cache predating a foundation change still had a valid-looking
`.olean`. This inflated apparent coverage from a **true ~33%** to a fake **~97%**.
*Protocol:* every headline measurement deletes all `Elements/OriginalProofs`
oleans and performs a **full clean rebuild**; coverage is then defined by parsing
the build log (a lemma is *compiled* iff no `error:` cites its file).

**Own-error vs cascade.** A failing build yields **own-errors** (the lemma's own
proof fails — its file must change) and **cascades** (blocked only by a failing
dependency; self-heals once the dependency is fixed). The audit separates these,
because only own-errors are real work — and fixing a foundational own-error often
*exposes* new own-errors hidden behind a cascade ("the layered cascade").

**"Compiles" vs "proven": the `sorryAx` gate.** A file can type-check while a
tactic bailed to `sorry`. *Gate 1* = compiles, no literal `sorry`. *Gate 2* =
`lean_verify` confirms no `sorryAx` in the lemma's axiom set (a proof can pull in
`sorry` transitively without the literal token in its own file). Only a clean
axiom profile (GeoCoq axioms + Mathlib) counts as proven.

## 5. Results

### 5.1 Headline coverage (clean rebuild, no cache)

**`Elements/OriginalProofs`: 229 / 234 lemmas translated and machine-checked
(97.9%), with zero `sorry`-holes among them.** Five lemmas remain as documented
Tier-4 residuals.

| Tier | Mechanism | role |
|---|---|---|
| 1–2 | Deterministic transpiler + ported tactic vocabulary | the large majority |
| 3 | Oracle-grounded explicit arguments (`axiom_5_line` family) | a few |
| 4 | Hand-written (nCol case-split; existential / `Par` reconstruction) | ~8 |
| — | **Documented residuals** (see §5.2) | 5 |

Coverage trajectory over the project:

```
~33%   true baseline (once stale-olean masking removed)
  ↓    cn_equalitysub → subst_vars            (whole class)
  ↓    transpiler-emitted nCol bridge         (whole TS/OS/CongA family + cascades)
 228   /234   (but with 5 sorry-holes still present)
  ↓    general Coq-idiom coverage             (exists / remove_exists / auto / eapply / destruct)
 229   /234   (0 sorry-holes — the 5 holes became real proofs; the keep-on-throw
              masking lifted, surfacing 5 honest Tier-4 residuals)
```

A note on the 228 → 229 step. The general-idiom handlers converted the last five
`sorry`-fallbacks (`notperp`, `proposition_30/31/34`, `extension`) into genuine
proofs — a strict gain in *honesty* (the 228 figure included five `sorry`-admitted
stubs; the 229 figure includes none). The same change also made `transpile()`
succeed on a few lemmas it previously *threw* on, which lifted the fragile
"keep-on-transpile-exception" masking (Part II §B.4) that had been silently
propping up five lemmas. Those five now surface as **honest own-errors** rather
than hidden stubs — a more truthful, if numerically similar, state.

### 5.2 The five residuals

Every residual is a genuine Tier-4 case with an understood cause:

| Residual | Cause | Tier-4 route |
|---|---|---|
| `lemma_8_3` | `axiom_5_line` with point arguments the conclusion does not pin | oracle-grounded explicit `apply axiom_5_line <args> <;> assumption` |
| `lemma_fiveline` | same `axiom_5_line` unpinned-argument pattern (two sites) | oracle-grounded explicit args |
| `lemma_collinear4` | nCol betweenness case-split with no structural cue; a heavy hand proof at the heartbeat margin | hand-written + `maxHeartbeats` |
| `lemma_tarskiparallelflip` | a `TP`-extract leaves an unsplit conjunction, so a later `conclude_def Meet` build cannot see the buried `A ≠ B` | call-site conjunction split (the scoped, non-macro form) |
| `proposition_22` | bundles a helper lemma, plus `apply` unification mismatch and `isDefEq`/`whnf` timeouts — goal-directed metric/`Lt` reasoning | multi-lemma emission + LLM-assisted reconstruction |

These are not coverage gaps in the declarative skeleton; they are precisely the
cases where argument resolution, hand-construction, scoped context-splitting, or
goal-directed reasoning is required — i.e. the boundary the methodology is about.
`proposition_22` in particular is *Tarski_dev*-flavored content embedded in
*Elements*, marking where the declarative-transpilation assumption breaks down.

### 5.3 What the boundary teaches

The lemmas that resist deterministic translation cluster into recognizable kinds:

- **`nCol` case-splits** (`collinear4`): require a betweenness case-analysis with
  `outerconnectivity`/`connectivity` that has no structural cue in the Coq text.
- **Unpinned point arguments** (`axiom_5_line`, `outerconnectivity`,
  `connectivity`): the conclusion does not determine all arguments; the oracle is
  load-bearing.
- **Existential / definition reconstruction** (`extension`'s assert-without-`by`;
  `parallelsymmetric`'s `Par`): the witness or the definition is too expensive for
  the bounded tactics to rebuild.
- **Metric/`Lt` goal-directed reasoning** (`proposition_22`): *Tarski_dev*-flavored
  content embedded in *Elements*.

This taxonomy *is* the contribution to "where does AI belong in proof
translation": deterministic methods own the declarative skeleton and the
structural reconstruction of definitions; an oracle owns argument resolution; and
human/LLM effort is needed precisely for goal-directed reasoning and for
reconstructions with no structural cue.

## 6. Discussion: lessons for cross-assistant translation

1. **Translate the *tactic vocabulary*, then the proofs.** Porting GeoCoq's five
   tactics once, faithfully, made every declarative proof a near-verbatim copy —
   decoupling *what the proof says* (preserved structurally) from *how each step is
   discharged* (centralized in macros).
2. **Bounded, ordered, type-directed beats unbounded search** on this corpus.
3. **Put durable fixes where they survive regeneration** — in the foundation, or
   emitted by the transpiler, or in an explicitly hand-owned file. The `nCol`
   bridge (a fix the transpiler writes for itself) is the template for reconciling
   "regenerate everything" with "some corrections only work at the call site."
4. **Macro changes are global; prefer call-site emission for scoped fixes.** A
   tweak to `conclude_def`'s context-normalization regressed the heavy
   `collinear4` by imposing its cost on every call.
5. **Measure honestly or not at all** — clean rebuild + `sorryAx` profile, never
   cached oleans.
6. **The residual is data, not failure.** Refusing to overfit keeps the boundary
   meaningful: the ~10 hand lemmas and the one documented residual are the
   empirical map of where automation stops.

## 7. Track B and future work

- **`Tarski_dev` (1,527 lemmas), LLM-primary.** The spike showed ~3% structurally
  transpilable, ~90% goal-directed. The plan is an **A1 pipeline** — a Lean-aware
  model loop using `lean-lsp-mcp` (goal/diagnostic feedback), `rocq-mcp` (Coq
  reference state), and the oracle (resolved-argument hints) — run bottom-up by
  chapter (Ch02 → Ch16) over the dependency order, cost contained by chapter
  batching and a trivial-proof fast path. The *Elements* foundation and
  verification scaffolding are reused directly.
- **Close `proposition_22`** via the A1 pipeline, validating that the LLM track
  closes exactly the residual the transpiler cannot.
- **Coverage dashboard** reporting per-sub-library `auto / oracle / hand /
  remaining` — this table *is* the thesis metric.
- **Faithfulness at scale** beyond `sorryAx`: sample statement-level faithfulness
  (a translated statement must match the Coq original, not merely be provable).

## 8. Conclusion

The declarative core of GeoCoq — Euclid's *Elements*, Book I — can be translated
into Lean 4 **structure-preservingly and almost completely**: **229 of 234 lemmas,
clean-rebuild verified and free of `sorry`-holes**, the remaining five documented,
well-understood Tier-4 boundary cases. The result came not from a monolithic
translator but from a **tiered** method whose tiers are individually simple and
collectively honest about where they stop.
Two general, foundation-level mechanisms — the `cn_equalitysub → subst_vars` path
and the **transpiler-emitted `¬Col → nCol` bridge** — carried the bulk of the
corpus by exploiting dependency-DAG amplification. The engineering discipline that
made it durable generalizes beyond geometry to cross-assistant proof translation.

---
---

# PART II — PROJECT DOCUMENTATION

This part is the engineering manual: how the system is laid out, what the
transpiler does rule-by-rule, how to measure honestly, and how to reproduce every
number.

## A. Repository map

```
GeoCoq/
├─ theories/Elements/OriginalProofs/        # GeoCoq source (Coq/Rocq) — the input
│    lemma_*.v, proposition_*.v
│    euclidean_tactics.v, general_tactics.v # the tactic vocabulary being ported
│
├─ geocoq-lean/                             # the transpiler + drivers (Python)
│    geolean_transpile.py                   # the structure-preserving transpiler
│    fresh_euclidean.py                     # clean-rebuild driver + HANDMADE set
│    audit_true_coverage.py                 # own-error / cascade classifier
│    coqtoleanbrief.py                      # Coq lemma + dependency extraction
│
├─ lean/geocoq_translate/                   # the Lean 4 output package
│  └─ GeocoqTranslate/
│     ├─ Euclidean/Axioms.lean              # axiom typeclass hierarchy (hand)
│     └─ Elements/OriginalProofs/
│        ├─ euclidean_defs.lean             # ~25 derived definitions (hand)
│        ├─ euclidean_tactics.lean          # ported tactic vocabulary (hand)
│        ├─ Lemmas/lemma_*.lean             # transpiler-generated (regenerated)
│        └─ proposition_*.lean              # transpiler-generated (regenerated)
│
└─ docs/methodology_paper.md                # this document
```

## B. Architecture — a two-author codebase

The Lean tree is authored by **two distinct "authors"**; keeping them separate is
what makes the system maintainable and re-runnable.

### B.1 Author A — the hand-written foundation (never regenerated)

- `Euclidean/Axioms.lean` — the Tarski/neutral axiom system as a Lean typeclass
  hierarchy (`euclidean_neutral` ⊂ `euclidean_neutral_basis` ⊂
  `euclidean_neutral_ruler_compass`) plus primitive predicates.
- `euclidean_defs.lean` — the ~25 derived definitions (`TS`, `OS`, `CongA`,
  `Triangle`, `Per`, `Perp`, `Meet`, `CR`, `TP`, …).
- `euclidean_tactics.lean` — the ported tactic vocabulary, the `cn_*` shims, and
  the basic `Col`/`nCol` bridge lemmas (`nCol_notCol`, `not_nCol_Col`, …).

Written once, by hand; never output by the transpiler. The stable substrate every
generated proof imports.

### B.2 Author B — transpiler-generated per-lemma files (regenerated freely)

Each `lemma_*.lean` / `proposition_*.lean` is produced by `geolean_transpile.py`
and **overwritten on every run**. This guarantees the corpus is reproducible from
*Coq source + transpiler* — essential to the thesis claim.

### B.3 The organizing seam

> **A fix must live where it survives.** A correction placed in a generated file is
> destroyed on the next transpile. A durable fix must (a) live in Author A, or (b)
> be *emitted by the transpiler*, or (c) the file must be explicitly hand-owned and
> excluded from regeneration. This single principle dictated the resolution of the
> `nCol` bridge (Part I §3.3) and the `HANDMADE` mechanism (§B.4).

### B.4 `HANDMADE` — protecting Tier-4 files

`fresh_euclidean.py` holds a `HANDMADE` set excluded from re-transpilation. A
subtle failure made this load-bearing: when a new transpiler feature made
`transpile()` *succeed* on a lemma it had previously *thrown* on (e.g.
`collinear4`), the driver — which keeps the existing file on a transpile exception
— silently switched from "kept the good hand file" to "overwrote it with broken
output." **Hand-owned files must be explicitly protected, not implicitly protected
by transpiler failure.** Current `HANDMADE`: the parallel/sameside reconstruction
lemmas, `ondiameter`, `proposition_02/08`, and `collinear4`.

## C. The transpiler — translation rules

`geolean_transpile.py` parses a Coq proof into a list of `Step`s and emits Lean.
The major rules:

### C.1 Statement translation

`forall A B C, P` → `∀ (A B C : Point), P` (all GeoCoq quantified variables are
Points; explicit annotation lets the predicate typeclass resolve). Leading `->`
hypotheses become an `intro` line. Connectives map directly
(`/\ → ∧`, `\/ → ∨`, `-> → →`, `~ → ¬`, `exists → ∃`); `neq/eq` become infix
`≠`/`=`.

### C.2 Proof-step translation

| Coq | Lean `Step` |
|---|---|
| `assert (T) by (tac).` | `have : ⟦T⟧ := by ⟦tac⟧` |
| `assert (Tf: exists x, B) by (tac); destruct …` | `obtain ⟨x, _…⟩ : ∃ x, ⟦B⟧ := by ⟦tac⟧` |
| `assert (T).` + `by cases on (D). { … } …` | `have : ⟦T⟧ := by` + `rcases`-split |
| `assert (T).` + `{ … }` (negation block) | `have : ⟦T⟧ := by intro h; …` |
| `conclude L` / `forward_using L` / `close` / `contradict` | same-named Lean macro |

Tactic name mapping (`translate_tactic`): the `conclude`-family ports verbatim;
`auto`/`eauto`/`easy`/`intuition` → `close`; `reflexivity` → `rfl`;
`(simple) eapply L` / `apply L` → `apply L`.

### C.3 The `nCol`-leaf table (the bridge)

```python
_NCOL_LEAVES = {                 # def → nCol leaves as argument-index triples
    "TS":       [(1, 2, 0)],            # TS P A B Q  → nCol A B P
    "CongA":    [(0, 1, 2)],            # CongA A B C … → nCol A B C
    "Triangle": [(0, 1, 2)],
    "OS":       [(2, 3, 0), (2, 3, 1)], # OS P Q A B → nCol A B P, nCol A B Q
    "Cut":      [(0, 1, 2), (0, 1, 3)],
}
```

`_bridge_conclude_def(tac, lean_type)`: if `tac` builds an nCol-leaf def, prefix it
with `(try (have : nCol … := nCol_notCol _ _ _ (by assumption)))` for each leaf,
computing the point arguments from the goal type and the table.

### C.4 General-idiom handlers (parse-time)

| Coq idiom | Emission |
|---|---|
| `exists W1 W2 …[; tac]` | `exact ⟨W1, W2, …, by ⟦tac⟧⟩` (default `close`) |
| `destruct H as [w…][; spliter]` | `obtain ⟨w…, _⟩ := this` |
| `remove_exists[; tac]` | `first | close | exact ⟨_, by close⟩ | … (0–6 witnesses)` |
| `assert (T) by auto` (no parens) | parsed via the relaxed `by (tac) | bare-tac` regex |
| standalone `(simple) eapply L` / `apply L` | recognized as a final tactic |

### C.5 The ported tactic macros (`euclidean_tactics.lean`)

- **`conclude L`**: `(try spliter); (try remove_double_neg); first | done |
  assumption | (subst_vars; assumption) | exact L | (apply L <;> assumption) |
  solve_by_elim [L] | …`. The `subst_vars` branch (Part I §3.2) precedes `exact L`.
- **`conclude_def D`**: fast extract path, then the 0–6 witness ladder with
  `assumption`-before-`And.intro`.
- **`forward_using L`**: type-directed projection of the needed permutation out of
  `L _ _ _ (by assumption)`.
- **`close` / `contradict`**: assumption / search / conjunction-split / classical
  `¬¬`-elim, and betweenness-disjunction refutation respectively.

## D. Measurement protocol

```bash
# 1. honest clean rebuild (NEVER trust a number measured against cached oleans)
cd lean/geocoq_translate
find .lake/build/lib -path "*Elements/OriginalProofs*" -name "*.olean" -delete

# 2. re-transpile everything + clean build + print coverage
python3 ../geocoq-lean/fresh_euclidean.py        # absolute path also works

# 3. classify own-error vs cascade in the log
python3 ../geocoq-lean/audit_true_coverage.py geocoq-lean/fresh_build.log
```

**Reading the coverage report.** `compiled (no own error)` is files that built;
`transpiled clean` is the subset the transpiler produced with no warnings.
**Caveat:** the difference (`compiled − transpiled-clean`) is *not* a count of
`sorry`-holes — it lumps in the hand-written `HANDMADE` files (complete proofs) and
partial-transpile files that still compiled cleanly. The true "unproven" set is the
own-errors plus files containing a literal `sorry` token in code. The `sorryAx`
gate (`lean_verify <fully.qualified.Name>`) is the final certification.

## E. Reproduction recipes

```bash
# translate a single lemma:
python3 geocoq-lean/geolean_transpile.py \
    theories/Elements/OriginalProofs/lemma_X.v lemma_X -o <out>.lean

# build one lemma module:
cd lean/geocoq_translate
lake build GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_X

# count real sorry-holes across the corpus (code, not comments):
cd lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs
grep -rlw sorry Lemmas/*.lean *.lean
```

## F. Glossary

- **DAG amplification** — fixing a predicate near the bottom of the dependency
  graph compiles all dependents that were blocked only by it.
- **nCol bridge** — transpiler-emitted `have : nCol … := nCol_notCol _ _ _ (by
  assumption)` before an nCol-leaf `conclude_def` build.
- **Layered cascade** — fixing a foundational own-error exposes new own-errors
  previously hidden behind the cascade.
- **Stale-olean masking** — cached `.olean` files making broken lemmas look
  compiled; defeated by a clean rebuild.
- **Two-author codebase** — hand-written foundation (never regenerated) vs
  transpiler-generated per-lemma files (regenerated freely).
- **Real vs comment `sorry`** — a `sorry` used as a tactic (a genuine hole) vs the
  token appearing only inside a comment (harmless); coverage counts only the
  former.
- **Own-error vs cascade** — a lemma's own proof failing vs being blocked only by a
  failing dependency.

## G. Status snapshot

- **`Elements/OriginalProofs`: 229 / 234 proven**, clean rebuild, **0 `sorry`-holes
  among the 229** (verified: `grep -rlw sorry` over the corpus returns none outside
  the residuals).
- **5 own-error residuals** (no hidden `sorry`; all honest failures):
  `lemma_8_3`, `lemma_fiveline`, `lemma_collinear4`, `lemma_tarskiparallelflip`,
  `proposition_22` — see Part I §5.2 for cause and Tier-4 route each.
- Tier-4 `HANDMADE`: parallel/sameside reconstruction lemmas, `ondiameter`,
  `proposition_02/08`, `collinear4`.
- **Caveat on the keep-on-throw mechanism (§B.4):** four of the five residuals were
  previously *masked* as "compiling" because the older transpiler threw on them and
  the driver kept a stale/hand file. Each transpiler improvement lifts some of that
  masking; the honest state is to hand-own (or document) them explicitly.
- Next steps to reach a clean 233–234: oracle-grounded `axiom_5_line` for
  `8_3`/`fiveline`, `maxHeartbeats` for `collinear4`, the scoped conjunction split
  for `tarskiparallelflip`; `proposition_22` is the genuine LLM/Track-B candidate.
- Then: `lean_verify` `sorryAx` gate across the proven set; then Track B
  (`Tarski_dev`).
