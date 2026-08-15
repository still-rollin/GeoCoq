# GeoLean — GeoCoq *Elements/OriginalProofs* → Lean 4 (234/234, 100%)

A deterministic, **structure-preserving** translation of GeoCoq's
`Elements/OriginalProofs` library (Euclid's *Elements*, Book I through areas) into
**Lean 4**. The entire library — **234 / 234 lemmas** — compiles under a single clean
rebuild, with **no `sorry`/`admit`/`sorryAx`**, no axioms beyond the source theory's 16,
and a **uniform** `maxHeartbeats = 800000` applied identically to every proof.

> **Honesty invariant:** the per-lemma `proposition_*.lean` / `lemma_*.lean` files are
> **never hand-edited**. They are produced *only* by the transpiler. All engineering lives
> in the transpiler and the tactic library (eight general fix-classes took coverage
> from 84.6 % to 100 %).

## Layout

```
lean/geocoq_translate/          Lean 4 project (lake)
  GeocoqTranslate/
    FreshElements.lean           aggregate module importing all 234 lemmas
    Euclidean/Axioms.lean         16 hand-translated axioms (the trusted base)
    Elements/OriginalProofs/
      euclidean_defs.lean         ~25 hand-translated definitions
      euclidean_tactics.lean      bounded tactic library (conclude, conclude_def, …)
      conclude_bounded.lean       head-indexed bounded search (the eauto port)
      proposition_*.lean          234 TRANSPILER-GENERATED proofs
      Lemmas/lemma_*.lean
theories/Elements/OriginalProofs/ original Coq sources (for faithfulness comparison)
transpiler/
  geolean_transpile.py            the deterministic Coq → Lean 4 transpiler
  audit_true_coverage.py          honest clean-rebuild coverage auditor
```

## Reproduce the 234/234 result

Prerequisites: `elan` / Lean toolchain. The project pins `leanprover/lean4:v4.30.0`
(`lean/geocoq_translate/lean-toolchain`) and a specific Mathlib revision (`lake-manifest.json`).

```bash
cd lean/geocoq_translate
lake exe cache get          # fetch prebuilt Mathlib oleans

# clean rebuild + honest audit (counts ONLY the 234 target oleans)
find .lake/build/lib/lean/GeocoqTranslate/Elements -name '*.olean' -delete
lake build GeocoqTranslate.FreshElements > /tmp/build.log 2>&1
cd ../..
python3 transpiler/audit_true_coverage.py /tmp/build.log
# expected: COMPILED (olean) : 234 (100%), own-error 0, cascade 0
```

## Honesty checks

```bash
# no escape hatches anywhere:
grep -rlE '\bsorry\b|\badmit\b|sorryAx' lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/ ; echo exit=$?
# uniform budget (single value):
grep -rho 'set_option maxHeartbeats [0-9]*' lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/*.lean | sort | uniq -c
```

## No hand-editing (regenerate from Coq and diff)

```bash
python3 transpiler/geolean_transpile.py \
  theories/Elements/OriginalProofs/proposition_30.v proposition_30 \
  | diff - lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/proposition_30.lean
# expected: no differences
```

## Scope

This covers `Elements/OriginalProofs` (the assert-chain proof style), transpiled
deterministically. The larger, goal-directed `Tarski_dev` corpus needs a different
approach — a proof-*term* transliteration pipeline rather than a tactic-script
transpiler — and is now in progress; see **[docs/TARSKI_STATUS.md](docs/TARSKI_STATUS.md)**
for current chapter-by-chapter status. Verified, ready-to-browse copies of both
completed datasets (this 234/234 corpus and the completed `Tarski_dev` foundations,
Ch02–Ch10) live in **[proven/](proven/)**.

Contact: Ayaan Siddiqui — `f20231060@hyderabad.bits-pilani.ac.in`.
