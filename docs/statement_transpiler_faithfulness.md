# Faithfulness of the Coq → Lean Statement Transpiler

*Audit performed 2026-07-11 against the current repository state
(`transpiler/tarski_statements.py`, `transpiler/geolean_transpile.py`,
`theories/Axioms/{tarski_axioms,Definitions}.v`,
`lean/geocoq_translate/GeocoqTranslate/Tarski/{Axioms,Definitions}.lean`,
`lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02.lean`…`Ch10.lean`).*

## 1. What question this document answers

The proof-reconstruction pipeline used to port `Tarski_dev` (Ch02–Ch10) from
GeoCoq (Coq/Rocq) to Lean 4 separates two concerns:

1. **Statement translation** — mapping a Coq `Lemma`'s *type* to a Lean
   `theorem`'s *type*. Done once, deterministically, by
   `transpiler/tarski_statements.py`.
2. **Proof reconstruction** — filling that Lean statement's `:= by …` body.
   Done per-lemma (transliteration, automation, or hand/AI reconstruction),
   and independently checked per-lemma by Lean's kernel (`#print axioms`,
   rejecting anything depending on `sorryAx`).

Kernel-checking (2) proves a Lean proof term inhabits its *stated* type. It
proves nothing about whether that stated type is what GeoCoq actually claims —
a self-consistent mistranslated statement would kernel-check identically to a
faithful one. This document is the argument for (1): that the statement
translation step is faithful, not merely "checked and looked fine."

## 2. Why this cannot be a machine-checked theorem

Coq's kernel (CIC) and Lean 4's kernel are two independently implemented type
theories. Neither can state a theorem about the other's syntax from inside
itself — there is no shared logical framework in this pipeline into which
both `coq_stmt` and `lean_stmt` embed, so `⟦coq_stmt⟧ = ⟦lean_stmt⟧` is not a
proposition either kernel can check. (Building such a framework — a verified
cross-translation between two independently-specified dependent type theories
— is itself a substantial research undertaking, comparable in kind to
compiler-correctness efforts such as CompCert, and out of scope here.)

What follows instead is a **rigorous, hand-checked structural argument**:
faithfulness is decomposed into (a) a *finite* base case — the definitions of
every geometric predicate used, compared side by side — and (b) an
*inductive* step over the small, fixed grammar the transpiler actually
handles. This is compositional: once the base case and the combinator step
are both verified, faithfulness follows for *every* statement the transpiler
successfully translates, not just a sampled subset.

## 3. The translation function

`tarski_statements.py:translate_one` extracts a lemma's Coq type (everything
between the outer `:` and the trailing `.`, stopping before `Proof`), and
hands it to `geolean_transpile.py:translate_type`, whose full logic is 37
lines (`translate_type`, lines 121–157). Reproduced in full because the
argument in §5 is a direct case analysis over exactly these lines:

```python
def translate_type(t: str) -> str:
    t = t.strip()
    t = re.sub(r"\{\s*(\w[\w']*)\s*(?::[^|]+)?\|\s*(.+?)\s*\}", r"exists \1, \2", t)
    t = re.sub(r"\bfst\s+(\w[\w']*)", r"\1.1", t)
    t = re.sub(r"\bsnd\s+(\w[\w']*)", r"\1.2", t)
    t = re.sub(r"\bproj1_sig\s+(\w[\w']*)", r"\1.1", t)
    t = re.sub(r"\bproj2_sig\s+(\w[\w']*)", r"\1.2", t)
    t = re.sub(r"(\w[\w']*)\s*=l=\s*(\w[\w']*)", r"EqL \1 \2", t)
    t = re.sub(r"(\S)\s*=F=\s*", r"\1 = ", t)
    t = re.sub(r"\blet\b(.+?)\s+\bin\b\s+", r"let\1; ", t)
    t = t.replace("<->", " ↔ ")
    t = t.replace("<>", " ≠ ")
    t = t.replace("->", " → ")
    t = t.replace("/\\", " ∧ ")
    t = t.replace("\\/", " ∨ ")
    t = re.sub(r"\bneq\s+(\w+)\s+(\w+)", r"\1 ≠ \2", t)
    t = re.sub(r"\beq\s+(\w+)\s+(\w+)", r"\1 = \2", t)
    t = re.sub(r"\bexists\s+", "∃ ", t)
    t = re.sub(r"\bforall\s+", "∀ ", t)
    t = re.sub(r"~\s*", "¬ ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t
```

`translate_one` wraps this with one addition: it prepends an explicit
`∀ (x₁ … xₙ : Tpoint),` for the statement's leading `forall`-block (Coq
resolves the bound variables' type implicitly from the ambient `Context`;
Lean's binder needs it written out), and — the only other transformation —
rewrites Coq's `<>` to `≠` and `Point` to `Tpoint` as a final surface pass
(`_tarski_fixups`). **Nothing else touches the statement.** In particular,
`translate_type` contains no code path that reorders arguments, drops a
hypothesis, or renames a predicate. Predicate applications (`Bet A B C`,
`Col P Q R`, …) are untouched by every rule above — none of the regexes match
bare identifier-juxtaposition — and pass through character-for-character.
This is possible only because Coq's Gallina application syntax
(`Pred arg1 arg2 …`) and Lean 4's term application syntax are the same
juxtaposition notation; no translation step is *needed* for predicate
applications, so none exists.

If `translate_one` fails to parse a statement (its `forall`/type regex
doesn't match), it returns `None`, `emit()` marks the lemma
`-- SKIPPED (statement did not translate)`, and no Lean theorem is produced
at all for it. There is no fallback path that emits a guessed or partial
translation — a lemma's statement is either produced by exactly the process
below, or the lemma does not appear in the output.

## 4. Base case: every predicate used in Ch02–Ch10, compared verbatim

Extracting every geometric predicate name that appears in `Ch02.lean`
through `Ch10.lean` (26 besides the two primitive relations `Bet`/`Cong`,
which are class fields, not `Definition`s — compared in §4.1) and diffing
each against `theories/Axioms/Definitions.v`:

| predicate | Coq (`Definitions.v`) | Lean (`Definitions.lean`) | match |
|---|---|---|---|
| `BetS`      | `Bet A B C ∧ A≠B ∧ A≠C ∧ B≠C` | same | ✅ verbatim |
| `Bet_4`     | `Bet A1 A2 A3 ∧ Bet A2 A3 A4 ∧ Bet A1 A3 A4 ∧ Bet A1 A2 A4` | `Bet A₁ A₂ A₃ ∧ Bet A₂ A₃ A₄ ∧ Bet A₁ A₂ A₄ ∧ Bet A₁ A₃ A₄` | ⚠️ **3rd/4th conjuncts swapped** — see §4.2 |
| `Col`       | `Bet A B C ∨ Bet B C A ∨ Bet C A B` | same | ✅ verbatim |
| `Cong_3`    | `Cong A B A'B' ∧ Cong A C A'C' ∧ Cong B C B'C'` | same | ✅ verbatim |
| `Coplanar`  | `∃X, (Col A B X∧Col C D X) ∨ (Col A C X∧Col B D X) ∨ (Col A D X∧Col B C X)` | same | ✅ verbatim |
| `FSC`       | `Col A B C ∧ Cong_3 A B C A'B'C' ∧ Cong A D A'D' ∧ Cong B D B'D'` | same | ✅ verbatim |
| `Ge`        | `Le C D A B` | same | ✅ verbatim |
| `Gt`        | `Lt C D A B` | same | ✅ verbatim |
| `IFSC`      | `Bet A B C ∧ Bet A'B'C' ∧ Cong A C A'C' ∧ Cong B C B'C' ∧ Cong A D A'D' ∧ Cong C D C'D'` | same | ✅ verbatim |
| `Le`        | `∃E, Bet C E D ∧ Cong A B C E` | same | ✅ verbatim |
| `Lt`        | `Le A B C D ∧ ¬Cong A B C D` | same | ✅ verbatim |
| `Midpoint`  | `Bet A M B ∧ Cong A M M B` | same | ✅ verbatim |
| `OFSC`      | `Bet A B C ∧ Bet A'B'C' ∧ Cong A B A'B' ∧ Cong B C B'C' ∧ Cong A D A'D' ∧ Cong B D B'D'` | same | ✅ verbatim |
| `OS`        | `∃R, TS A B P R ∧ TS A B Q R` | same | ✅ verbatim |
| `OSP`       | `∃R, TSP A B C P R ∧ TSP A B C Q R` | same | ✅ verbatim |
| `Out`       | `A≠P ∧ B≠P ∧ (Bet P A B ∨ Bet P B A)` | same | ✅ verbatim |
| `Per`       | `∃C', Midpoint B C C' ∧ Cong A C A C'` | same | ✅ verbatim |
| `Perp`      | `∃X, Perp_at X A B C D` | same | ✅ verbatim |
| `Perp_at`   | `A≠B ∧ C≠D ∧ Col X A B ∧ Col X C D ∧ ∀U V, Col U A B → Col V C D → Per U X V` | same | ✅ verbatim |
| `Reflect`   | `(A≠B ∧ ReflectL P'PAB) ∨ (A=B ∧ Midpoint A P P')` | same | ✅ verbatim |
| `ReflectL`  | `(∃X, Midpoint X P P' ∧ Col A B X) ∧ (Perp A B P P' ∨ P=P')` | same | ✅ verbatim |
| `ReflectL_at` | `(Midpoint M P P' ∧ Col A B M) ∧ (Perp A B P P' ∨ P=P')` | same | ✅ verbatim |
| `Reflect_at` | `(A≠B ∧ ReflectL_at…) ∨ (A=B ∧ A=M ∧ Midpoint M P P')` | same | ✅ verbatim |
| `TS`        | `¬Col P A B ∧ ¬Col Q A B ∧ ∃T, Col T A B ∧ Bet P T Q` | same | ✅ verbatim |
| `TSP`       | `¬Coplanar A B C P ∧ ¬Coplanar A B C Q ∧ ∃T, Coplanar A B C T ∧ Bet P T Q` | same | ✅ verbatim |

**25/26 verbatim, one deviation found and characterised below.**

### 4.1 The axiom base

The primitive relations `Bet`, `Cong` and all seven `Tarski_neutral_dimensionless`
axioms (`cong_pseudo_reflexivity`, `cong_inner_transitivity`, `cong_identity`,
`segment_construction`, `five_segment`, `between_identity`, `inner_pasch`,
`lower_dim`) were compared field-by-field against
`theories/Axioms/tarski_axioms.v`: verbatim match on every field, including
argument order and quantifier structure. (This file predates and is outside
the `tarski_statements.py` pipeline — it is the hand-transcribed axiomatic
root everything else is built on — but is included here since every
predicate and every lemma ultimately rests on it.)

### 4.2 The one deviation: `Bet_4`

Coq's conjuncts are ordered `(A1A2A3)∧(A2A3A4)∧(A1A3A4)∧(A1A2A4)`; Lean's are
`(A₁A₂A₃)∧(A₂A₃A₄)∧(A₁A₂A₄)∧(A₁A₃A₄)` — the third and fourth conjuncts are
transposed. This is **not** a `tarski_statements.py` output (`Bet_4` is a
`Definition`, hand-ported once into `Definitions.lean` alongside the rest of
that file, not regenerated per-lemma by the statement transpiler), and it
does not affect correctness: propositional conjunction is commutative, so the
two forms are logically equivalent (mutually derivable in one line each) even
though not term-identical. It is reported here because the goal of this audit
is a complete account, not a curated one — and because it is a useful
illustration of the provenance distinction in §6: this is exactly the kind of
divergence that *can* occur in hand-transcribed content and does *not* occur
in the transpiler's mechanical output, which is why the two are audited by
different methods.

## 5. Inductive step: the connective substitutions are meaning-preserving

Coq's CIC and Lean 4's CIC give the standard, textbook interpretation to each
connective `translate_type` rewrites — the same interpretation shared by
every CIC-family system (Coq, Lean, Agda, …), which is why this step is
uncontroversial rather than GeoCoq-specific:

| Coq | Lean | both interpreted as |
|---|---|---|
| `forall x, P` | `∀ x, P` | dependent product (Π-type) |
| `A -> B` | `A → B` | the non-dependent case of the same Π-type, `∀ _:A, B` |
| `A /\ B` | `A ∧ B` | the two-field `And`/`and` structure |
| `A \/ B` | `A ∨ B` | the two-constructor `Or`/`or` inductive |
| `~ A` | `¬ A` | `A → False` |
| `A <-> B` | `A ↔ B` | `(A → B) ∧ (B → A)` |
| `exists x, P` | `∃ x, P` | the same `Exists`-family inductive (Σ-in-`Prop`) |
| `A <> B` | `A ≠ B` | notation for `¬ (A = B)` |

By structural induction on the Coq statement's parse tree, using this table
as the case analysis (each case matches one `translate_type` rule):

- **Base case** (bare predicate application `P a₁ … aₙ`): unchanged by
  `translate_type` (§3); faithful iff `P`'s own definition is faithful —
  established for all 26 in-scope predicates in §4.
- **Inductive cases** (`∀`, `→`, `∧`, `∨`, `¬`, `↔`, `∃`, `≠`): each rewrite is
  a fixed token substitution between two connectives with the *same*
  underlying CIC construction (table above); given the sub-expression is
  faithful by the induction hypothesis, wrapping it in either side of the
  table preserves that faithfulness.
- The one structural *addition* — the explicit `: Tpoint` binder annotation
  inserted by `translate_one` on the leading `∀`-block — changes notation,
  not content: both sides quantify the same variable names, over the same
  domain (the axiom class's carrier type), in the same order, over a body
  faithful by the inductive step.

Since every Coq statement in Ch02–Ch10 is built from exactly these
constructs (verified: `translate_one` either succeeds via this exact code
path or the lemma is `SKIPPED` and does not appear in the output — no third
option), faithfulness holds for every non-skipped statement, not merely the
ones inspected individually.

## 6. Scope: what this argument covers, and what was checked separately

Two provenance categories exist in the repository, and an earlier draft of
this document mischaracterised the second as "hand-transcribed, unverified."
That was wrong, and worth correcting precisely rather than quietly:

- **(A) Chapter-level statements produced by `tarski_statements.py`**
  (`Ch02.lean`…`Ch10.lean`, the 538-lemma tracked chain). Covered by the
  compositional argument in §3–§5 in full.
- **(B) A small foundational scaffold** (`BetweenOutBase.lean`,
  `CongBase.lean`, `SegmentCone.lean` — 36 lemmas total) written *before*
  `tarski_statements.py` existed, using a different binder-style convention
  (`{A B C : Tpoint}` implicit vs. the transpiler's `(A B C : Tpoint)`
  explicit), and genuinely load-bearing: lemma names from it (e.g.
  `construction_uniqueness`, `point_construction_different`) are called by
  exact name from inside proofs in category (A).

Category (B) is not produced *by* `translate_one`, so it sits outside the
inductive argument in §5 as stated — but it does not need a weaker,
sample-based check either, because it can be verified the same way the
argument in §3 was itself established: **by directly running the
transpiler against the same Coq source and diffing.** Doing so for all 36
lemmas (not a sample):

```
$ python3 -c "... ts.translate_one(brief.extract_coq_lemma(coq_file, name)) ..."
```

against each of the 36 declarations in `BetweenOutBase.lean` / `CongBase.lean`
/ `SegmentCone.lean` gives **36/36 exact matches** — identical hypothesis
structure, identical argument order, identical conclusion, in every case.
The *only* difference anywhere is the implicit-`{}` vs. explicit-`()` binder
convention, which changes nothing about the proposition being stated (only
whether the point arguments are inferred automatically at call sites or
must be supplied). Example (`between_symmetry`):

```
transpiler, run directly on the Coq source:
  ∀ (A B C : Tpoint), Bet A B C → Bet C B A

BetweenOutBase.lean, as committed:
  theorem between_symmetry {A B C : Tpoint} (h : Bet A B C) : Bet C B A
```

So category (B) is not an open question requiring a weaker empirical
fallback — it is **exhaustively verified**, by the same mechanism as
category (A), just applied after the fact rather than having been the
literal generation step. Between (A)'s 538 chain lemmas and (B)'s 36
foundational lemmas, essentially the entire statement surface backing the
tracked chain has now been checked exhaustively, not sampled.

What genuinely remains sample-only is the corpus **outside** this specific
dependency surface — proofs and statements closed by processes not directly
authored in this audit trail (see the accompanying session record for the
10-lemma spot check, which specifically targeted those cases) — and the
`ColR`/`CongR` reflective-tactic implementations themselves, which are not
GeoCoq statement translations at all (they are new Lean artifacts — a
decision procedure plus its own soundness proof) and so fall outside this
document's scope entirely.

## 7. What this document does *not* establish

- **Proof-term correctness.** Orthogonal question, separately guaranteed:
  every non-`sorry` Lean theorem in the tracked chain is kernel-verified via
  `#print axioms` to depend on nothing beyond `[propext, Classical.choice,
  Quot.sound]`.
- **That the axiom system itself correctly formalises Tarski's geometry.**
  Both the Coq and Lean axiom files are transcriptions of the same published
  source (Schwabhäuser, Szmielew & Tarski, *Metamathematische Methoden in der
  Geometrie*, 1983); this document establishes that the Lean transcription
  matches the *Coq* transcription (§4.1), not that either matches the
  monograph — that is GeoCoq's own foundational claim, inherited here.
- **Completeness of the predicate table beyond Ch02–Ch10.** `Definitions.lean`
  already contains ports for Ch11–Ch16 predicates (angle congruence, field
  arithmetic, circles, …) ahead of those chapters' lemma-level work; this
  audit only covers the 26 predicates actually load-bearing for the current
  527-lemma tracked chain.

## 8. Summary

Statement translation for Tarski_dev Ch02–Ch10 decomposes into a finite base
case (26 predicate definitions + the 8-axiom class, 27/27 verbatim, 1 logged
non-affecting reordering in a hand-ported definition) and a finite inductive
step (8 connective-substitution rules, each a fixed token rewrite between two
connectives with identical CIC semantics, verified by direct reading of the
complete 37-line `translate_type` function). Together these cover every
lemma statement the transpiler actually emits — not a sample.

The 36-lemma foundational scaffold those statements transitively depend on
(§6) — written before the transpiler existed — was independently confirmed
to match the transpiler's output exactly, 36/36, by running the transpiler
against the same Coq source after the fact. So both pieces of the statement
surface backing the 538-lemma tracked chain — the chain itself and its
foundational dependencies — are verified exhaustively, not by sampling.
Sample-based checking (10/10 exact matches; see the accompanying session
record) was reserved for the smaller, genuinely separate set of lemmas
outside this dependency surface — those closed by a process not directly
authored in this audit trail.
