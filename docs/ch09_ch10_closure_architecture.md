# Architecture: Transpiler + LLM Pipeline to Close the Remaining Ch09/Ch10 Holes

Status: **design + one stage empirically confirmed, not yet run at scale** ·
Companion to [`session_progress.md`](session_progress.md) Item 11 (2026-07-10)
and [`tarski_architecture.md`](tarski_architecture.md) §5.1 (the reconstruction
loop this specializes for one concrete hole set).

---

## 0. Starting point (verified, from Item 11)

- `Tarski_dev/Ch09.lean` + `Ch10.lean`: **69 holes remain** out of 70 at session
  start (1 closed: `ex_sym_c`). Base chain: 527 lemmas, 428 kernel-clean.
- Two harness bugs and one real `translit.py` bug (`ex_intro` match-arity) already
  fixed this session — demonstrated **1/16 → 15/16** leverage on the coplanarity
  family alone.
- All existing tooling this design reuses is already built and working:
  `geolean_pipeline/translit.py` (deterministic transliterator),
  `cascade_llm.py` (kernel-gated LLM cascade, mirror-then-freeform, ledger),
  `llm_path.py` (`verify_one` — the sole correctness gate: isolated `lake env lean`
  + `#print axioms`, no `sorryAx`), `hole_blocks()`/`fold()`/`coq_index()`
  (safe in-place hole editing, position-guarded).

**Non-negotiable, carried over from the standing constraints:** `#print axioms`
is the sole arbiter. No lemma is reported closed unless it compiles with only
`propext`/`Classical.choice`/`Quot.sound` in its axiom list. No git commit
without explicit ask.

---

## 1. The big finding: the ported reflective automation is unwired — confirmed

Julien's original guidance (see `tarski_architecture.md` §0) was: port the
reflective tactics first (`ColR`, `CongR`, `assert_diffs`), then reconstruct
proofs *using that automation*, consulting the Coq proof only for intermediate
statements. That porting happened — `ColR.lean` (400 lines) and `CongR.lean`
(323 lines) are real, mature, verified `elab` tactics (`colr`, `cong_r`), not
stubs.

**But the entire `translit.py`/climb pipeline that produced `Ch02.lean..Ch10.lean`
never calls them.** Grepped all 9 chapter files: zero occurrences of `colr`,
`cong_r`, or `Tfinish`. Instead, `translit.py` transliterates Coq's raw kernel
proof term literally — and when the Coq tactic script called `ColR`/`Col5`/`auto
with col` (41 times in `Ch09_plane.v` alone), what `Show Proof` prints is not "ColR
was called" but the *specific, ground-out chain of primitive lemma applications*
ColR's internal engine happened to construct for that one goal instance — e.g.
`col_permutation_5 D X C (col_permutation_1 C D X H2)`. Transliterating that
literally means porting every individual `col_permutation_N`/`coplanar_perm_N`
the expansion happens to reference, by name — an unbounded, ever-growing tail.
This is almost certainly why the deterministic transpiler doesn't scale: it's
reinventing, lemma by lemma, exactly what the already-verified `colr` reflective
decision procedure could close in one tactic call.

**Confirmed empirically** (`ScratchColRTest.lean`, `lake env lean`, all three
kernel-clean — `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

1. A real `ColTheory Tpoint Col` instance was missing from the climb chain
   entirely. `PilotCh06.lean` built one, but it's an isolated demo file never
   imported by `Ch02.lean..Ch10.lean`, and its `col3` field leaned on an
   explicit `Col3Assumption` placeholder (unproven at the time).
2. That placeholder is no longer necessary — `col3` (GeoCoq's
   `col_transitivity`) is now derivable **unconditionally** from lemmas already
   sitting proven in the climb chain itself: `col_transitivity_1_c`/`l6_16_1_c`
   (`Ch06.lean`) + `col_permutation_2_c`/`col_permutation_3_c` (`Ch04.lean`).
   Full derivation (~12 lines) is in `ScratchColRTest.lean`.
3. With a real instance wired in, `colr` closes:
   - pure-permutation goals (`Col D C X` from `Col C D X`) — **zero**
     individual permutation lemmas referenced, one tactic call.
   - transitivity-shaped goals (`Col P A B` from `Col P Q A`, `Col P Q B`,
     `P≠Q`) — same result.

This changes the priority order of everything below: **Stage 0 is now "wire
the automation," not "triage the holes."** Expect a large fraction of the
`MISSING_BASE` and "dropped N implicit arg(s)" holes from Item 11's log to
vanish once `colr`/`cong_r` are tried before falling back to literal
transliteration — because most of those missing names were col/cong-family
permutation and transitivity lemmas that `colr`/`cong_r` subsume by
construction.

**Not yet done, deliberately left for explicit go-ahead:** promoting
`ScratchColRTest.lean`'s instance from a scratch file into the real chain
(needs a permanent file + import wiring into `Ch02.lean..Ch10.lean`'s early
chapters), and — the actually load-bearing change — teaching `translit.py` to
*try* `colr`/`cong_r` at Col/Cong-typed goals before attempting literal
transliteration.

---

## 2. Stage-by-stage pipeline

```
Stage 0  Wire automation     (CONFIRMED works — do this first, biggest leverage)
   │        a) promote a real ColTheory/CongTheory instance into the chain
   │        b) teach translit.py: at any Col/Cong-typed leaf, try `colr`/
   │           `cong_r` (kernel-verify), fall back to literal transliteration
   │           only if the tactic doesn't close the goal
   ▼
Stage 1  Triage the residue  (deterministic, no proof attempts, ~1 min)
   │        classify whatever Stage 0 didn't already close, by TRUE root cause
   ▼
Stage 2  Base-lemma port     (deterministic, loop-until-dry)
   │        port remaining MISSING_BASE names (non-Col/Cong-family) with
   │        leverage ≥ 2, splice, rebuild, repeat
   ▼
Stage 3  Transpiler fixes    (manual diagnosis, same method as ex_intro)
   │        fix translit.py bugs found in Stage 1's PARSER_GAP/EMIT_BUG bucket
   ▼
Stage 4  Deterministic       (mechanical — same det_only_pass.py loop)
         close-out             re-run translit+verify+fold on everything unlocked
   │
   ├──── loop Stage 0b→4 until 2 consecutive rounds add zero new clean holes
   ▼
Stage 5  LLM cascade         (cascade_llm.py, opt-in, costs API calls)
            run on the TRUE residue only — whatever's left after automation +
            deterministic porting + transpiler fixes are exhausted
```

### Stage 0 — Wire the reflective automation (do this first)

**(a) Promote the instance.** Take `ScratchColRTest.lean`'s `col3_real` +
`realColThy : ColR.ColTheory Tpoint Col` (and the equivalent `CongTheory`
instance — `PilotCh06.lean` already has an unconditional one, just needs
relocating) into a permanent file, e.g. `Tarski_dev/ColCongInstances.lean`,
imported early in the chain (right after `Ch04.lean`/`Ch06.lean`, since that's
where `col3_real`'s dependencies live) so every later chapter can use `colr`/
`cong_r` directly.

**(b) Teach `translit.py` to try automation before literal transliteration.**
This is the actually load-bearing change, and needs care about *where* to hook
it in:
- At any point `emit_tactic`/`emit` is about to emit a term/tactic whose
  Lean-side goal type is `Col _ _ _` or `Cong _ _ _ _` (this is knowable
  either from the Coq lemma being proven having exactly that conclusion type
  at a leaf, or empirically: try `by colr`/`by cong_r` as a candidate FIRST
  for the whole hole, kernel-verify, accept if it closes the goal).
- The empirical/opportunistic version is simpler to build and matches the
  project's existing kernel-gated philosophy: it doesn't need translit.py to
  do real type inference — just try the one-liner, let `verify_one` decide.
  Concretely: before running the existing `try_det`/transliteration path on a
  hole, first attempt `by colr` (if the hole's conclusion, read from its Lean
  stub tail, is a bare `Col A B C`) or `by cong_r` (conclusion `Cong A B C D`)
  as a candidate proof, verify it in isolation, and only fall through to
  literal transliteration if that fails.
- This is a *cheap prefilter*, not a `translit.py` rewrite — implementable as
  a ~15-line addition to whatever drives the hole loop (`det_only_pass.py` /
  `cascade_llm.py`'s deterministic phase), not inside `emit()` itself, since it
  only needs the target statement, not the Coq proof term at all.

**Expected effect:** every hole whose *entire* remaining blocker was a
Col/Cong-family `MISSING_BASE` name (a large fraction of Item 11's 19
`UNRESOLVED head` misses, plus likely several of the 50 candidates that failed
kernel-verify for reasons downstream of a broken permutation chain) should
close for free, without porting a single additional `col_permutation_N`/
`coplanar_perm_N`-style lemma by hand.

### Stage 1 — Triage the residue

Same as before, but run *after* Stage 0, so it classifies only what automation
genuinely couldn't close (not holes that were only "blocked" because nobody
had wired `colr` in yet):

- `MISSING_BASE(name)` — `UNRESOLVED head: <name> (not ported / unknown)`
- `PARSER_GAP(construct)` — `UNRESOLVED: unsupported construct '...'` /
  `UNRESOLVED: unhandled node '...'` / `UNRESOLVED: match in term position`
- `LEAK` — a raw Coq token escaped
- `CANDIDATE_OK` — translit produced a body with zero blocking notes

**Known bug in the current triage tooling**, to fix before this stage runs:
the scratch driver's skip-reason display only prints `notes[0]` — the *first*
note collected — not necessarily the note that caused the actual skip. Several
holes in the Item 11 log show a `"dropped N implicit arg(s)"` note as the
displayed reason, which is likely *not* the true blocker (that note alone
doesn't trigger a skip). Capture and report the full notes list.

Output: a `{hole_name: (bucket, detail)}` map and a `{missing_name: [holes
that need it]}` reverse index, for Stage 2's leverage ordering.

### Stage 2 — Base-lemma porting (loop-until-dry, non-Col/Cong-family only)

Same procedure as this session's coplanarity port, for whatever `MISSING_BASE`
names remain after Stage 0 (expect these to be genuinely new mathematical
content — e.g. `collect_diffs` — not more permutation/transitivity lemmas):

1. Locate the Coq source — **not always in `Tarski_dev/Ch*.v`** (coplanarity
   lived in `theories/Main/Annexes/coplanar.v`); `run_proof()` takes an
   explicit file path, no glob restriction.
2. Hand-write the Lean signature, `translit.py` → `verify_one` → splice →
   **rebuild the whole chain** before trusting any subsequent verify (a stale
   `.olean` produced a false negative this session — always rebuild after
   every splice batch).
3. Recompute the reverse index, repeat until a full pass adds nothing.

### Stage 3 — Transpiler bug fixes

For `PARSER_GAP`/`LEAK` entries, trace one representative instance the way the
`ex_intro` bug was found: fetch the raw `Show Proof` term, walk it against
`emit`/`emit_tactic`/`emit_match`, find the mishandled AST shape, fix in
`translit.py`. **Re-verify only the affected subset**, not the full batch —
this session's main inefficiency was 5 full 69-hole re-runs after each fix.

### Stage 4 — Deterministic close-out

Mechanically identical to `det_only_pass.py` at end of session (correct
base-name seeding, correct multi-name binder extraction, now also trying
Stage 0's automation prefilter) — run once per Stage 0b/2/3 iteration, fold,
rebuild, report real counts.

### Stage 5 — LLM cascade (opt-in, costs money)

Whatever remains goes through the **existing** `cascade_llm.py` unmodified —
rank by Coq proof size, filter to candidates whose deps are already clean,
mirror-first LLM attempt with free-form fallback, `verify_one` gate, ledger
logging:

```
python geolean_pipeline/cascade_llm.py <max_lemmas> <max_coq_lines>
```

Needs explicit go-ahead (API cost) and a budget cap per round.

---

## 3. What this buys vs. this session's ad-hoc approach

- **The single highest-leverage fix identified all session** — wiring
  `colr`/`cong_r` — is empirically confirmed to work and costs nothing (no
  LLM, no new lemma content, just using automation that already exists).
- **No redundant full-batch re-verification.** Stage 1's triage map means
  later re-runs target exactly the holes a given fix could plausibly affect.
- **LLM spend only on the true residue**, after both automation and
  deterministic base-porting are exhausted.
- **Every claimed "closed" hole is still `#print axioms`-verified** — this
  architecture changes ordering and mechanism, not the correctness bar.

## 4. Open questions before running this at scale

1. Should the `colr`/`cong_r` prefilter live in `det_only_pass.py`/
   `cascade_llm.py` (cheap, opportunistic, no `translit.py` changes) or become
   a real code path inside `translit.py` itself (more invasive, but usable by
   every future chapter/pipeline, not just this one)? Leaning toward the
   cheap prefilter first — validate the win, then decide if it's worth
   formalizing into `translit.py`.
2. Stage 5 costs real API money — recommend running Stages 0-4 first
   (deterministic/automation-based, free), reporting the real resulting hole
   count, **then** deciding Stage 5's scope explicitly.
3. `ScratchColRTest.lean` is currently an untracked scratch file — needs a
   decision on promoting it to a permanent, properly-named file before Stage 0
   can actually run against the real chain.
