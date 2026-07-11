# geolean_pipeline — autonomous GeoCoq → Lean transliteration

A deterministic, kernel-gated pipeline that turns GeoCoq (Coq/Rocq) `Tarski_dev`
proofs into Lean 4 proofs, using the Coq proof term as an oracle. It follows
Julien's method: **port tactics → translate statements → reconstruct proofs
via automation**, with a *minimal, kernel-gated* LLM only where the
deterministic path can't reach.

## The funnel (per lemma)

```
Coq lemma ──▶ oracle (Show Proof term)  +  Lean statement (from the stub)
          ──▶ transliterator: term / tactic emitter
                • lemma app  → port_map picks the CONE (proven) variant,
                               drops implicit args  → `exact f …`
                • case-split → or_ind→rcases, and_ind/ex_ind→obtain ⟨⟩,
                               ex_intro/conj→⟨⟩, let→have
          ──▶ VERIFY GATE: `lake env lean` + `#print axioms`
                • clean (no sorryAx) → ACCEPT
                • else                → queue (unsupported / blocked / failed)
```

Only lemmas that compile **axiom-clean** are accepted. Original `.lean` files are
never modified — accepted proofs are written to a fresh output module.

## Components

| file | role |
|------|------|
| `../geolean_oracle/src/oracle.py` | Coq-side oracle: `Show Proof` → resolved lemma calls |
| `../geolean_oracle/src/port_map.py` | Lean-side: Coq name → ported Lean signature(s) |
| `translit.py` | proof-term → Lean (term + tactic emitters); cone-strict |
| `orchestrator.py` | batch driver + verify gate + `#print axioms` + ledger |
| `scaffold.py` | LLM-path: bundle everything an LLM needs for a proof the emitter can't do |
| `run.py` | CLI |
| `signature_index.py` | ground-truth `_c` signature index for the canonical Ch02–Ch10 chain — **always look up a signature here, never grep the tree** (stale non-authoritative scaffold duplicates like `Ch09_plane.lean` sit alongside the real files and will give you wrong argument orders) |

```bash
python geolean_pipeline/signature_index.py                     # regenerate signature_index.json — do this after any signature change
python geolean_pipeline/signature_index.py colx_c l8_22_c       # look up one or more names
```

## Run

```bash
python geolean_pipeline/run.py Ch03_bet          # chapter shorthand
python geolean_pipeline/run.py Ch04_cong_bet Orch_Ch04
```
Prints the ledger and the verify-gate result. Needs the Coq `_build` consistent
with the active opam switch (`dune build <target>` if the oracle errors on stale
`.vo`), and the Lean project under `lean/geocoq_translate`.

## Current results (deterministic, zero-LLM, axiom-clean)

- `Ch03_bet.v`: **10 / 29** accepted → **10 verified axiom-clean** (incl. `l3_17`,
  a real theorem with existential construction).
- `Ch04_cong_bet.v`: **1** verified (`l4_3_1`).

## Honest limits

- **Constructs**: the term parser handles `fun/let/app` + `or_ind/and_ind/ex_ind/
  ex_intro/conj`. It does **not** yet handle `eq_ind_r` (rewriting/`subst`) or
  in-term type ascriptions `(e : T)` — common in Ch04+ → those are queued.
- **Base-limited yield**: accepted lemmas must resolve to the proven cone
  (Ch02–Ch05 Cong/Bet). Chapters needing un-ported base (Out, midpoint, …) are
  mostly `blocked` until the base climbs.
- **LLM path** (`scaffold.py`) is demonstrated but **not wired to an API** — the
  scaffold is proven sufficient; the orchestrator→API→verify loop is TODO.

## Roadmap

1. ✅ orchestrator (batch + verify gate + queue)
2. ✅ LLM-path scaffold (demonstrated)
3. ✅ case-split parser (`or_ind`/`and_ind`/`ex_ind`)
4. ⏳ `eq_ind_r` + type-ascription constructs → higher accept-rate
5. ⏳ base bottom-up climb → unlock genuinely-new-lemma yield
6. ⏳ wire LLM path to an API for full autonomy on the residue
