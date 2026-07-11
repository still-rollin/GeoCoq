# Proven datasets — read-only reference copies

This folder exists so the **verified, complete** parts of the GeoLean port can be
browsed directly, without navigating the full working pipeline (`geolean_pipeline/`,
`geolean_oracle/`, the in-progress `Ch11`–`Ch16b` chapters, experiment scripts, etc.).

**These are copies, not the source of truth.** The buildable, canonical project lives
under `lean/geocoq_translate/`. If you change something, change it there — this folder
is regenerated from scratch each time, not hand-edited.

Both datasets below were verified honestly: a **clean rebuild** (caches wiped first,
not a stale `lake build`) followed by a **kernel check** (`#print axioms` on every
lemma) confirming zero `sorryAx` — not just "no literal `sorry` token in the file",
which can hide a `sorry` pulled in transitively through a dependency. See
`GEOLEAN.md` at the repo root for why that distinction matters.

## `tarski_ch02_10/` — Tarski_dev foundations, Ch02–Ch10

**538 lemmas, 0 `sorry`, 0 `sorryAx`, clean rebuild confirmed 2026-07-11.**

The full import closure of `Ch02.lean`..`Ch10.lean` (computed from the actual `import`
graph, not guessed) — this is the base geometry (congruence, betweenness, collinearity,
orthogonality, reflection) that every later chapter (`Ch11` onward) builds on.

| File | Lemmas | | File | Lemmas |
|---|---:|---|---|---:|
| `Ch02.lean` | 34 | | `Ch08.lean` | 94 |
| `Ch03.lean` | 29 | | `Ch09.lean` | 125 |
| `Ch04.lean` | 31 | | `Ch10.lean` | 41 |
| `Ch04Cong.lean` | 7 | | `ColR.lean`, `CongR.lean`, `ColCongInstances.lean`, `CongBase.lean`, `SegmentCone.lean`, `BetweenOutBase.lean` | reflective-tactic support |
| `Ch05.lean` | 66 | | `Tarski/Axioms.lean` | the trusted axiom base |
| `Ch05Bet.lean` | 3 | | `Tarski/Definitions.lean` | derived predicates |
| `Ch06.lean` | 53 | | | |
| `Ch07.lean` | 55 | | | |

Some file names in the live tree (`Ch02_cong.lean`, `Ch03_bet.lean`, `Camp_*.lean`,
`Climb_*.lean`, `Orch_*.lean`, ...) look related but are **not** part of this closure —
they're artifacts from earlier pipeline iterations that `Ch02`–`Ch10` no longer import.
The closure computation excludes them automatically; nothing here was hand-picked.

## `elements_euclid/` — Euclid's *Elements*, Book I–areas

**234/234 lemmas, 0 `sorry`, 0 `sorryAx`.** Full detail, methodology, and the
transpiler that produced this (a genuine deterministic transpiler, not an LLM) are in
`GEOLEAN.md` at the repo root — that document is the primary source, this folder is
just a copy of the corpus it describes, taken from `FreshElements.lean`'s own import
list (the same list the project's own coverage auditor uses).

## Reproducing these numbers

```bash
cd lean/geocoq_translate
lake exe cache get
find .lake/build/lib/lean/GeocoqTranslate/Tarski_dev -name '*.olean' -delete
lake build GeocoqTranslate.Tarski_dev.Ch10        # Ch02-10 closure
lake build GeocoqTranslate.FreshElements          # Elements 234/234
```

No `sorry`/`admit`/`sorryAx` anywhere in either dataset:

```bash
grep -rlE '\bsorry\b|\badmit\b|sorryAx' proven/ ; echo "exit=$?"   # expect exit=1 (no matches)
```
