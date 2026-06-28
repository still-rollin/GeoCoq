# GeoCoq → Lean 4 — progress memo

*For Julien, Guillaume, Pierre. Summarises the work done since the last meeting.*

## Your feedback → what was built

| What you asked for | Delivered |
|---|---|
| Proofs should **read like the GeoCoq originals**, not opaque proof-terms | Structure-preserving translation: `assert (X) by (conclude L).` → `have : X := by conclude L`. Euclid I.1 (`proposition_01`, 25 steps) now reads line-for-line like the `.v` and compiles with no `sorry`. |
| Use a **script** to scale, not an LLM per lemma — "use AI smartly" | A deterministic transpiler (`geolean_transpile.py`): a `.v` proof → structure-preserving Lean in <1 s, $0. The LLM is reserved for the residual the script can't reach. |
| Term/lambda resolution is the **wrong basis for translation** | Agreed — the oracle was repurposed from *translator* to **proof-faithfulness validator**. It now checks the translation; it no longer drives it. |

## Concrete state (all machine-checked)

- **Foundations** (hand, once): Tarski / Euclidean / Hilbert axioms; 25 derived definitions;
  the GeoCoq tactic vocabulary ported to Lean (`conclude`, `conclude_def`, `forward_using`,
  `contradict`, `close`), backed by `aesop`.
- **Elements/OriginalProofs:** **49 translations compile-verified** (45 lemmas + 4
  propositions), structure-preserving, no `sorry`. The transpiler **auto-translates the
  structure of 71 % (167/234)** of the chapter.
- **Three-layer correctness audit** (not just "it compiles"):
  1. *Soundness* — `lean_verify`: proofs rest only on `propext`/`Classical.choice`/`Quot.sound`,
     no `sorryAx`.
  2. *Statement faithfulness* — for the 24 lemmas with an independent hand translation, the
     transpiler's statement is **definitionally equal** to the human one (kernel-checked, 24/24).
  3. *Proof faithfulness* — the oracle confirms the Lean proofs use the **same lemma set** as
     Coq's verified proof term (`proposition_01`, `lemma_3_7b`).

## The strategic finding (measured, not assumed)

GeoCoq is **two stylistic worlds**, which dictates a two-architecture plan:

| | Elements/OriginalProofs | Main/Tarski_dev |
|---|---|---|
| lemmas | 246 | 1 527 |
| style | `assert … by (conclude …) … close.` | idiomatic Coq: `induction`/`rewrite`/`destruct` |
| `conclude` uses | 8 184 | **0** |
| deterministic transpiler | **applies** (71 % auto) | **3 %** — proofs are goal-directed |

So the **deterministic transpiler** owns the regular assert-chain proofs; the **LLM pipeline**
(Claude + rocq/lean MCP + oracle hints) owns the goal-directed tail in *both* libraries. The
boundary between them is *itself a result*: a precise, measured account of where automation
ends and judgement begins.

## Roadmap (geometric core first)

- **Track A — Elements (transpiler):** continue the bottom-up dependency build; LLM-translate
  the complex-branching tail that blocks downstream lemmas in the dependency graph.
- **Track B — Tarski_dev (LLM pipeline):** stand up per-chapter, bottom-up, cost-budgeted;
  validate on a small Ch02 batch before scaling (~1 380 goal-directed proofs).
- **Throughout:** the 3-layer verification, a per-library coverage dashboard, and a canonical
  `GeoLean` repository kept green by CI.

## Honest open items
- The transpiler's deterministic ceiling on Elements is gated by an interleaved dependency
  graph (clean proofs depend on the complex tail) — completing Elements needs the LLM tail.
- Tarski_dev cost (LLM per proof × ~1 380) is the dominant project expense; batching, oracle
  hints, and dependency ordering are the levers to contain it.

**Documentation:** full methodology + approach history in `docs/translation_approaches.md`.
