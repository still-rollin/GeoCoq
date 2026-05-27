# Rocq → LLM → Lean translation demo

A working cross-prover translation pipeline on this branch
(`lean-translation-demo`). One Python orchestrator drives two MCP
servers — `rocq-mcp` and `lean-lsp-mcp` — with a Gemini call in the
middle. Output below is a real terminal capture from a clean run, not
a mockup.

## What the pipeline does

```
.v file (Rocq)
   │
   │   (1) rocq-mcp          extract theorem statement (MCP/stdio)
   ▼
plain-text statement
   │
   │   (2) Gemini 2.5 Flash  translate to Lean 4 (HTTPS)
   ▼
.lean file
   │
   │   (3) lean-lsp-mcp      fetch diagnostics (MCP/stdio)
   ▼
pass / fail
```

Every arrow is a real protocol call. Nothing is mocked. The two prover
sides speak MCP (JSON-RPC over stdio); the LLM hop is HTTPS to Google.

## Where to look

| File | Purpose |
|---|---|
| [orchestrator/demo.py](orchestrator/demo.py) | The orchestrator. Single-theorem version. |
| [orchestrator/pipeline.py](orchestrator/pipeline.py) | Slimmer first-version pipeline (no lean-mcp, uses `lake env lean` subprocess). |
| [orchestrator/demo_progression.py](orchestrator/demo_progression.py) | Runs the same pipeline across 5 progressively harder Rocq theorems. |
| [theories/Axioms/playground.v](theories/Axioms/playground.v) | Source of `neq_sym` (the theorem used in the captured run below). |
| [theories/Axioms/rocq_demo.v](theories/Axioms/rocq_demo.v) | 5 progressively harder Rocq theorems used by `demo_progression.py`. |
| [lean/geocoq_translate/](lean/geocoq_translate/) | Stock Lean 4 Lake project; serves as the Lean verifier. |
| [docs/demo_experiment.md](docs/demo_experiment.md) | Detailed architecture writeup + known limitations. |
| [docs/setup_journey.md](docs/setup_journey.md) | Toolchain and editor-config issues we resolved while building this. |
| [docs/sample_run.txt](docs/sample_run.txt) | Raw terminal capture of the run shown below. |

## Captured run (verbatim from `orchestrator/demo.py`)

```
[1/4] rocq-mcp: extracting neq_sym from theories/Axioms/playground.v
      -> forall (A : Type) (a b : A), a <> b -> b <> a

[2/4] gemini (gemini-2.5-flash): translating to Lean 4
      generated:

        theorem neq_sym (A : Type) (a b : A) : a ≠ b → b ≠ a := by
          -- Assume `h_ab : a ≠ b`. Recall `a ≠ b` is notation for `¬ (a = b)`.
          intro h_ab
          -- We want to prove `b ≠ a`, which is `¬ (b = a)`.
          -- To prove a negation `¬ P`, we assume `P` and derive a contradiction.
          -- So, assume `h_ba : b = a`.
          intro h_ba
          -- We have `h_ab : ¬ (a = b)` and `h_ba : b = a`.
          -- From `h_ba : b = a`, we can get `a = b` using `Eq.symm`.
          have h_eq_ab : a = b := Eq.symm h_ba
          -- Now we have `h_ab : ¬ (a = b)` and `h_eq_ab : a = b`.
          -- Applying the negation `h_ab` to the equality `h_eq_ab` yields `False`.
          exact h_ab h_eq_ab

[3/4] writing lean/geocoq_translate/GeocoqTranslate/Scratch.lean

[4/4] lean-mcp: fetching diagnostics for Scratch.lean
      diagnostics:
        {
          "success": true,
          "timed_out": false,
          "items": [],
          "failed_dependencies": []
        }

RESULT: all parts worked -- rocq-mcp + LLM + lean-mcp -- and the Lean translation type-checks.
```

### What that output means, step by step

1. **`rocq-mcp` extracted a theorem from a real `.v` file.** It spawned
   the `rocq-mcp` server over stdio, called the `rocq_start` tool with
   `theorem=neq_sym`, and parsed the resulting goal string. No
   precompiled `.vo` lookup, no source-text regex — actual proof-engine
   state.
2. **Gemini 2.5 Flash produced a complete Lean 4 file.** Note it picked
   the right Lean idioms (`a ≠ b → b ≠ a`, `Eq.symm`, tactic mode)
   without any few-shot examples in the prompt.
3. **Lean diagnostics came back empty** — `"items": []` means zero
   errors and zero warnings. The translation type-checks cleanly under
   stock Lean 4.

## Progression across 5 theorems

Beyond the single `neq_sym` example above, `orchestrator/demo_progression.py`
runs the same pipeline on five progressively harder Rocq theorems from
[theories/Axioms/rocq_demo.v](theories/Axioms/rocq_demo.v). One real run
(captured in [docs/sample_progression.txt](docs/sample_progression.txt)):

| # | Rocq theorem | Statement | Result |
|---|---|---|---|
| 1 | `add_0_r` | `forall n : nat, n + 0 = n` | **PASS** |
| 2 | `add_comm` | `forall n m : nat, n + m = m + n` | **PASS** |
| 3 | `length_app` | `forall A l l', length (l ++ l') = length l + length l'` | FAIL |
| 4 | `de_morgan` | `forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q` | **PASS** |
| 5 | `exists_not_all` | `forall P, (exists n, P n) -> ~ (forall n, ~ P n)` | FAIL |

3/5 verified end-to-end on a single zero-shot prompt, no retries on
the Lean side. The two failures are *informative*:

- **`length_app`**: Gemini hallucinated a lemma name
  (`append_nil_left_eq`) that doesn't exist in Lean 4 core. A plain
  `simp` would have closed it; the model went looking for a specific
  rewrite lemma and invented one.
- **`exists_not_all`**: Gemini used `cases h with n0 h_P_n0` — that's
  **Lean 3 syntax**. Lean 4 wants `obtain ⟨n0, h_P_n0⟩ := h` or
  `cases h with | intro n0 h_P_n0=> …`. Classic Lean-3-vs-Lean-4 slip
  that a feedback loop should be able to fix.

Both failures suggest the same next step: when Lean returns errors,
feed them back to the LLM with the original statement and ask for a
fix. The current pipeline doesn't yet do that. The MCP infrastructure
already returns structured diagnostics that are ideal for this.

The full failed Lean files are checked in at
[docs/sample_failures/length_app.lean](docs/sample_failures/length_app.lean)
and [docs/sample_failures/exists_not_all.lean](docs/sample_failures/exists_not_all.lean)
for inspection.

## Reproducing it locally

Prerequisites: Coq 8.18 opam switch, the project's `.venv` (with
`google-genai`, `mcp`, `rocq_mcp`), `lean-lsp-mcp` on `PATH`
(installed via `uv tool install lean-lsp-mcp`), and Lean 4 / `lake`.
Full setup is in [docs/setup_journey.md](docs/setup_journey.md).

```bash
# build the Rocq side
dune build theories/Axioms/playground.vo

# run
export GEMINI_API_KEY=<your-key>
.venv/bin/python orchestrator/demo.py
```

For the progression across 5 theorems:

```bash
dune build theories/Axioms/rocq_demo.vo
.venv/bin/python orchestrator/demo_progression.py
```

## Status

- **What works:** End-to-end pipeline. All six Rocq theorems (`neq_sym`
  plus the five in `rocq_demo.v`) extract cleanly via `rocq-mcp`.
  Translation pass-rate from a single zero-shot prompt: **4/6** (`neq_sym`,
  `add_0_r`, `add_comm`, `de_morgan` — the two failures are documented
  above with concrete diagnoses).
- **What doesn't (yet):**
  - Theorems whose statements depend on Tarski/GeoCoq predicates
    (e.g. `Bet`, `Cong`). `rocq-mcp`'s `find_thm` mode doesn't
    pre-process file-level imports, so the identifiers fail to resolve.
    Workarounds (position-based extraction, text fallback) are sketched
    in `docs/demo_experiment.md`.
  - Self-repair: when Lean errors, the pipeline currently gives up
    instead of feeding the diagnostics back to the LLM. The two
    documented failures would likely be fixed by a single retry loop.
- **What this proves:** the architecture works. Two prover-side MCP
  servers plus an LLM hop can be wired together from a single Python
  process to translate and verify across systems. Translation
  *quality* on harder inputs is the next axis to push on, separately
  from plumbing.
