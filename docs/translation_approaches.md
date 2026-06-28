# GeoCoq → Lean 4: translation approaches

A record of how the translation strategy evolved, why it changed, and how the
current (transpiler) approach differs from the earlier (LLM-driven) ones. Written
to be readable standalone — for advisors, for the thesis, and for future-me.

Companion docs: [translation_design.md](translation_design.md) (the *axiom/def*
translation decisions), [claude_mcp_workflow.md](claude_mcp_workflow.md) (MCP
wiring details), [../geolean_oracle/README.md](../geolean_oracle/README.md) (the
oracle internals).

---

## 0. The goal (unchanged across all approaches)

Port GeoCoq — a large Rocq/Coq formalization of geometry (Tarski, Euclid's
*Elements*, Hilbert) — into Lean 4, with **machine-checked** fidelity (real Lean
compilation, no hand-waving). The axiom systems and definitions are already
translated (see [translation_design.md](translation_design.md)); the open problem
is **translating the hundreds of proofs**.

Two requirements emerged from advisor feedback (June 2026) and now drive
everything:

1. **Readability** — a translated proof should *read like the GeoCoq original*, so
   a GeoCoq author recognizes their own proof. Not idiomatic-mathlib; *faithful*.
2. **Scale** — translating hundreds of proofs by hand (or by per-proof LLM calls)
   is too slow and too expensive. The intelligence must be amortized into a
   reusable artifact. ("Use AI smartly.")

---

## 1. The approaches, in order

### A0 — Python orchestrator + Gemini (the original demo)

```
orchestrator/demo.py  ──MCP──►  rocq-mcp      (read Coq goal)
                      ──HTTPS─►  Gemini 2.5 Flash   (translate)
                      ──MCP──►  lean-lsp-mcp   (compile, get diagnostics)
```

A Python script drove an external LLM (Gemini) between the two prover MCP servers,
looping translate → compile → feed-error-back. See `TRANSLATION_DEMO.md` (now
removed).

**Character:** external LLM, external orchestration glue.
**Problems:** a second LLM hop, an orchestrator to maintain, nondeterministic.

### A1 — Claude Code in-line with MCP (the "MCP workflow")

```
Claude Code ──MCP──► rocq-mcp        (rocq_start: extract Coq statement)
            ──MCP──► lean-lsp-mcp    (lean_run_code / lean_diagnostic_messages)
```

The orchestrator and Gemini are removed; **Claude Code itself** talks MCP to both
provers and writes the Lean in its agent loop. Per proof: extract the Coq
statement, write Lean 4 directly, compile, read diagnostics, rewrite, repeat — no
fixed attempt cap.

**Character:** one LLM (Claude), no glue, verification by real Lean compilation.
**Output:** *idiomatic* Lean — term-mode, `obtain`, explicit positional
arguments. Correct, but it does **not** look like the GeoCoq proof. Example
(`proposition_01`, Phase-1 line):

```lean
obtain ⟨J, hCI_J⟩ := postulate_Euclid3 A B hAB
have hCong_AC_AB : Cong A C A B := axiom_circle_center_radius A A B J C hCI_J hOnC_J
```

**Problems:** (a) opaque — a nested term `axiom_betweennesssymmetry D B A (lemma_3_7a …)`
is unrecognizable as "the 3.7b proof"; (b) expensive — every proof is an LLM
session with multiple compile round-trips; (c) the dominant cost was Claude
re-deriving each lemma's *argument order* by trial and error against the compiler.

### A1.5 — A1 + the oracle (argument-order assist)

```
.v proof ──► geolean_oracle (SerAPI `Show Proof.`) ──► resolved lemma calls
                                                       (name + positional args)
              ▼
        fed to Claude so the .lean is written in one pass (no arg-order iteration)
```

[geolean_oracle](../geolean_oracle/README.md) runs the Coq proof through SerAPI,
captures the elaborated proof term, and extracts *which lemma was applied with
which arguments after unification*. This is exactly the information lost when
translating tactic scripts by hand, and it collapsed the 5–6 diagnostic
round-trips per proof into (ideally) one-shot translations.

**Character:** still LLM-per-proof, but the oracle removes the argument-order
guesswork.
**Problem the advisors raised:** if the method is "resolve the Coq proof term →
re-emit a Lean proof term," then because both languages are CIC-based lambda
calculi, that's a near-mechanical term-to-term map — and it produces the *opaque*
nested-term style (A1's output), which loses the proof's human structure ("the
essence of translation is lost"). The oracle, as a *translation driver*, pushes
toward unreadable proofs.

### A2 — Tactic-port + deterministic transpiler (current)

```
euclidean_tactics.v ──(hand, once)──► euclidean_tactics.lean   (conclude, close, …)

.v proof ──► geolean_transpile.py ──► structure-preserving .lean ──► lake build ✓
   (deterministic; no LLM in the loop for handled proofs)

geolean_oracle ──► used to VERIFY faithfulness, not to translate
```

Two moves:

1. **Port the GeoCoq tactic vocabulary to Lean** (`conclude`, `conclude_def`,
   `forward_using`, `contradict`, `close`, `spliter`, `remove_double_neg`) as Lean
   macros backed by `aesop`/`solve_by_elim`. This is the key enabler — once Lean
   *understands the same tactics*, a proof can be written in the same shape.
2. **A deterministic Python transpiler** (`geocoq-lean/geolean_transpile.py`) that
   maps the Coq proof **structure** to Lean line-for-line:
   `assert (X) by (tac).` → `have : X := by tac`, the `…fresh…;destruct…;spliter`
   idiom → `obtain ⟨w, _, _⟩ : ∃ … := by tac`, `assert (~X). { intro. … contradict. }`
   → nested `have : ¬X := by intro h; …`. Unhandled constructs → `sorry -- TODO`
   + a logged warning (never crashes).

**Output** is structure-preserving and reads like the original:

```lean
have : OutCirc D K := by conclude_def OutCirc          -- vs Coq: assert (OutCirc D K) by (conclude_def OutCirc).
have : Cong B C A B := by forward_using lemma_congruenceflip
have : ¬ BetS A C B := by intro h; …; contradict
close
```

**The oracle is repurposed:** no longer the translation driver, but the
independent **proof-faithfulness validator** (see §4, layer 3). This directly
answers the advisors' critique: term-level resolution is the wrong basis for
*translating* a proof, but the right basis for *verifying* the translation.

---

## 2. Side-by-side

| | A1 / A1.5 (LLM-driven) | A2 (transpiler, current) |
|---|---|---|
| **Who translates** | Claude, per proof | a deterministic script, once |
| **Cost** | O(LLM calls × proofs), many compile round-trips | O(1) script run over the whole chapter |
| **Determinism** | nondeterministic | fully reproducible / auditable |
| **Output style** | idiomatic term-mode (opaque) | structure-preserving (reads like GeoCoq) |
| **Readability** | low — nested proof terms | high — same skeleton, same tactic names |
| **Role of the oracle** | feeds resolved args *into* translation | *verifies* proof faithfulness after the fact |
| **LLM's role** | does everything | reserved for the residual hard cases only |
| **Failure mode** | silent divergence from the original proof | explicit `sorry -- TODO` + coverage report |

The pivot is not "drop the LLM." It's **relegate the LLM to the residual** — the
script handles the mechanical majority; Claude is reserved for the proofs the
parser can't yet handle. That is the concrete meaning of "use AI smartly."

---

## 3. Considerations / design decisions behind A2

- **Why a tactic port at all?** Without Lean `conclude`/`close`, the only faithful
  rendering of a GeoCoq proof is the opaque nested term (A1). Porting the tactics
  is what makes *both* readability *and* scriptability possible — the script just
  copies tactic names; Lean's macros do the work the Coq Ltac did.
- **Why `aesop` under the macros?** GeoCoq's `conclude` is `solve [… eauto …]`.
  The closest Lean engine for "build the existential / apply with unification" is
  `aesop`; verified on the hardest case (`proposition_01`, 25 steps) before
  committing. `solve_by_elim` handles the backtracking-apply cases.
- **Why deterministic script over "just keep using Claude"?** Cost and
  reproducibility at chapter scale, and — per the advisors — the intelligence
  belongs in a reusable artifact, not in repeated per-proof inference.
- **Tactics in one shared file.** Defining the macros inline per proof file causes
  duplicate-declaration build errors; they live in one `euclidean_tactics.lean`
  that every proof imports.
- **Never crash.** A whole-chapter run must always produce a buildable file plus a
  coverage number, so unparsed constructs become `sorry -- TODO`, logged — silent
  truncation would read as "covered everything."
- **Compile-readiness is gated by the dependency frontier.** A transpiled proof
  only builds if its dependency *lemmas* are already in Lean. So translation
  proceeds bottom-up; the transpiler runs ahead of the frontier and the proofs
  light up as their dependencies land.

---

## 4. Correctness methodology (three independent layers)

"It compiles" proves the *written* statement, never that the statement is the
*right* one. So correctness is checked in three layers, none relying on compilation
alone:

1. **Proof soundness** — MCP `lean_verify`: a proof's axioms are only
   `propext` / `Classical.choice` / `Quot.sound`, no `sorryAx`. (Geometry axioms
   are typeclass *hypotheses*, not Lean `axiom`s, so they correctly don't appear.)
2. **Statement faithfulness** — for every lemma with a hand-written Lean version,
   `example : <transpiled statement> := <hand_lemma>` compiles iff the two are
   **definitionally equal** (kernel-checked). Currently **24/24** pass.
3. **Proof faithfulness** — the **oracle** gives Coq's resolved proof-term lemma
   calls; compared against the Lean proof's `conclude`/`forward_using` names, the
   **lemma set is identical** (verified on `proposition_01`, `lemma_3_7b`). This
   rules out "aesop closed the goal via an unrelated shortcut."

Honest limits: layer 2 is verified only on lemmas that *have* a hand version
(~24); layer 3 is set-level (not full proof-isomorphism), and the oracle's filter
currently skips `postulate_*` calls.

---

## 5. Current status

- Tactic vocabulary ported and validated; `proposition_01` (Euclid I.1, 25 steps)
  compiles structure-preserving with no `sorry`.
- Transpiler runs over all of `theories/Elements/OriginalProofs`:
  **149 / 234 (63%) transpile clean** (zero fallbacks) on the first pass.
- The 37% gap is dominated by one un-ported construct: GeoCoq's `by cases on`
  case-split tactic (and its `{ }` branch blocks).
- Tooling: `geocoq-lean/geolean_transpile.py`, `geocoq-lean/run_coverage.py`,
  `…/Elements/OriginalProofs/euclidean_tactics.lean`, `…/faithfulness_check.lean`.

### Production demonstration (speed/cost)

A topological sweep of the transpiler produced **23 new lemma translations in
under a second, $0 API cost** (vs. a multi-turn LLM session per proof under A1).
Building them surfaced an honest gap between *produced* and *compiles*:

| Stage | Compiling |
|---|---|
| As generated | 4 / 20 |
| After 3 tooling fixes (import-root path, `open` the detected class, two `cn_` shims) | **11 / 20** |

The remaining 9, categorized — **none a translation-approach flaw**:
- **6 — definition frontier:** use derived predicates not yet in the Lean port
  (`Par`, `TT`, `RE`, `Per`); resolve bottom-up like the lemma frontier.
- **3 — tactic-strength residual:** faithfully translated, but `conclude`/`close`
  don't discharge a step. The genuine hard core (where AI/human help belongs).

Takeaway: producing structure-preserving Lean is instant and free; compile-rate is
gated by the dependency/definition frontier plus a small genuine-hard residual —
not by the transpiler.

### Frontier advance (bottom-up)

Acting on the categories above, in order of leverage:

1. **Definition frontier** — translated the 21 missing derived predicates
   (`Par`, `Per`, `Meet`, `Midpoint`, `OS`, `CongA`, `PG`, `RE`, `TT`, `SQ`, `RT`,
   `LtA`, `Supp`, `CR`, `TP`, `SumA`, `Perp`, `Perp_at`, `InAngle`, `isosceles`,
   `Cut`) into `euclidean_defs.lean`, registered for aesop unfolding. Immediately
   unblocked the 5 "function expected" lemmas.
2. **Tactic strength** — two fixes, each general (helps the whole chapter, not one
   proof):
   - `close` gained a **classical ¬¬-elimination** branch (`by_contra; contradiction`)
     ordered *before* the aesop branch — aesop normalises the `¬¬` hypothesis away,
     so the classical step must run first. Unblocks every `assert (~~X) … close`
     proof (e.g. `lemma_ray1/ray5/supplementsymmetric`). *Diagnosed with the
     lean-lsp MCP* (`lean_goal` + `lean_multi_attempt`).
   - `conclude_def` gained a **fast hypothesis-extraction branch** (extract a fact
     already in context instead of having aesop reconstruct it).
3. **Net result this pass:** translated lemma files **24 → 43**, all compile-verified.

Remaining genuine residual: `lemma_parallelsymmetric` — `conclude_def Par` makes
aesop reconstruct `Par`'s deeply-nested definition (5 ∃ + `¬ Meet`) and hits the
heartbeat limit. A candidate for the LLM/hand fallback or a smarter `conclude_def`.
The dominant remaining lever is still porting **`by cases on`**, which gates the
bulk of the un-translated lemmas.

---

## 6. What's next

1. **Port `by cases on`** — the single highest-leverage coverage lever; should move
   the 63% substantially (most partial proofs are case-splits).
2. **Tighten layer-3 faithfulness** — fix the oracle's name filter to include
   `postulate_*`, and report multiplicity (not just set) alignment.
3. **Advance the dependency frontier** — translate lemmas bottom-up so transpiled
   proofs become compile-ready; each new hand/checked lemma also extends layer-2
   coverage.
4. **Coverage as the headline result** — once `by cases on` lands, re-run the
   chapter and report the auto-translate %; the residual bucket defines exactly
   where LLM/human judgment is justified (the thesis's "where AI belongs" argument).
