#!/usr/bin/env python3
"""
geolean_transpile — structure-preserving GeoCoq → Lean 4 proof transpiler.

Reads a GeoCoq `.v` lemma and emits a Lean proof that mirrors the original
line-for-line, using the ported tactic vocabulary in `euclidean_tactics.lean`:

    Coq : assert (OutCirc D K) by (conclude_def OutCirc).
    Lean: have : OutCirc D K := by conclude_def OutCirc

Design rules (from the validation milestone):
  * Translate proof STRUCTURE, not proof terms.
  * Never crash. Anything unrecognized → `sorry -- TODO: <verbatim>` + a logged
    warning, so a whole-chapter run always produces a buildable file and a
    coverage report.

Reuses `coqtoleanbrief.py` (same dir) for Coq extraction and dependency names.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coqtoleanbrief as brief  # noqa: E402

# Root of the Lean `GeocoqTranslate` library being targeted. Used to discover
# which dependency lemmas already exist (→ which imports to emit). Override with
# GEOLEAN_LEAN_ROOT; defaults to the working fork tree, not the standalone repo.
LEAN_ROOT = os.environ.get(
    "GEOLEAN_LEAN_ROOT",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                 "lean/geocoq_translate/GeocoqTranslate"))


# ---------------------------------------------------------------------------
# Type translation:  Coq Prop  →  Lean Prop
# ---------------------------------------------------------------------------

def _strip_comments(s: str) -> str:
    """Remove Coq comments `(* … *)` (nesting-aware) from a proof body."""
    out = []
    depth = 0
    i = 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if s.startswith("*)", i) and depth:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(s[i])
        i += 1
    return "".join(out)


def _strip_outer_parens(s: str) -> str:
    """Drop a single layer of outer parens if they enclose the whole string."""
    s = s.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return s
    depth = 0
    for i, c in enumerate(s):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and i != len(s) - 1:
                return s            # first '(' closes before the end
    return s[1:-1].strip()


def _depth_split_count(s: str, sep: str) -> int:
    """Count occurrences of `sep` at paren-depth 0."""
    depth = 0
    i = 0
    n = 0
    while i < len(s):
        c = s[i]
        if c in "(":
            depth += 1
        elif c in ")":
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            n += 1
            i += len(sep)
            continue
        i += 1
    return n


def _depth_split(s: str, sep: str) -> list[str]:
    """Split `s` on `sep` at paren-depth 0, returning the parts (sep removed)."""
    parts: list[str] = []
    buf: list[str] = []
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            parts.append("".join(buf))
            buf = []
            i += len(sep)
            continue
        buf.append(c)
        i += 1
    parts.append("".join(buf))
    return parts


def translate_type(t: str) -> str:
    """Translate a Coq proposition string to Lean. Predicate names (BetS, Cong,
    Col, …) are preserved verbatim — only logical syntax changes."""
    t = t.strip()
    # Coq sigma/subset types `{C | P}` / `{C : T | P}` (constructive existence
    # witness) — simplified to a plain `exists` for statement-stub purposes.
    t = re.sub(r"\{\s*(\w[\w']*)\s*(?::[^|]+)?\|\s*(.+?)\s*\}", r"exists \1, \2", t)
    # Coq pair/sig projections used point-free in later definitions.
    t = re.sub(r"\bfst\s+(\w[\w']*)", r"\1.1", t)
    t = re.sub(r"\bsnd\s+(\w[\w']*)", r"\1.2", t)
    t = re.sub(r"\bproj1_sig\s+(\w[\w']*)", r"\1.1", t)
    t = re.sub(r"\bproj2_sig\s+(\w[\w']*)", r"\1.2", t)
    # local notations (Ch13_2_length: `l1 =l= l2` := EqL l1 l2)
    t = re.sub(r"(\w[\w']*)\s*=l=\s*(\w[\w']*)", r"EqL \1 \2", t)
    # Ch16_coordinates_with_functions: `l1 =F= l2` (F-field equality) — F's
    # predicate is a Prop, so Lean's proof-irrelevance makes native `=` agree.
    t = re.sub(r"(\S)\s*=F=\s*", r"\1 = ", t)
    # Coq `let (A, B) := E in BODY` -> Lean `let (A, B) := E; BODY` (term-mode
    # `let` uses `;`, not `in`). Non-greedy so consecutive/nested lets each
    # stop at THEIR OWN `in`, chaining correctly left-to-right.
    t = re.sub(r"\blet\b(.+?)\s+\bin\b\s+", r"let\1; ", t)
    # connectives (longest first)
    t = t.replace("<->", " ↔ ")
    t = t.replace("<>", " ≠ ")
    t = t.replace("->", " → ")
    t = t.replace("/\\", " ∧ ")
    t = t.replace("\\/", " ∨ ")
    # neq / eq as infix
    t = re.sub(r"\bneq\s+(\w+)\s+(\w+)", r"\1 ≠ \2", t)
    t = re.sub(r"\beq\s+(\w+)\s+(\w+)", r"\1 = \2", t)
    # quantifiers / negation
    t = re.sub(r"\bexists\s+", "∃ ", t)
    t = re.sub(r"\bforall\s+", "∀ ", t)
    t = re.sub(r"~\s*", "¬ ", t)
    # tidy whitespace
    t = re.sub(r"\s+", " ", t).strip()
    return t


# ---------------------------------------------------------------------------
# Tactic translation:  Coq tactic  →  Lean tactic
# ---------------------------------------------------------------------------

# Tactics that port across with identical syntax (the GeoCoq vocabulary we
# reimplemented as Lean macros in euclidean_tactics.lean).
_PORTED = ("conclude_def", "conclude", "forward_using", "contradict", "close")

# Pure-permutation `have` steps that the perm-aware `conclude` engine makes
# redundant (see the note at the end of `parse_proof`). Only the argument-order
# lemmas whose predicate the matcher covers (Col/nCol/Cong) — NOT derivations
# like `lemma_betweennotequal` (BetS→neq) or `lemma_parallelflip` (Par, uncovered).
_PERM_STEP = re.compile(
    r"^have : .+ := by forward_using "
    r"lemma_(collinearorder|NCorder)\b")

# Per-theorem elaboration budget. GeoCoq proofs translate to LONG bounded-tactic
# chains (some lemmas are 30+ asserts over a 30-fact context); these are genuine,
# `sorry`-free, kernel-checked proofs that simply need more than Lean's default
# 200k heartbeats. Raising the budget is honest (it never makes a wrong proof pass)
# — it only trades build time for headroom. Emitted as a visible `set_option … in`
# before each theorem rather than hidden globally, so the cost is auditable.
# `maxRecDepth` is raised alongside it: the perm-aware `conclude` engine recurses
# deeper (on-demand premise reconstruction adds backtracking depth), and the
# default 512 overflows on dense proofs. Like the heartbeat budget this is honest
# — a deeper recursion limit never makes a wrong proof pass.
_MAXHB = "set_option maxHeartbeats 800000 in set_option maxRecDepth 8000 in"

# Definitions whose body contains positive `nCol` leaf(s). When `conclude_def D`
# BUILDS such a definition, the leaf must be discharged as a positive `nCol`,
# but the surrounding GeoCoq proof only carries it as `¬ Col` (GeoCoq treats the
# two interchangeably). The Lean macro cannot bridge `¬ Col ⟹ nCol` from inside
# itself (the nested `(by assumption)` does not fire under macro hygiene), so the
# transpiler emits the bridge at the call site instead — where it works, and
# survives re-transpile because it is regenerated each run. Each entry maps a def
# to its nCol leaves as argument-index triples into the def's point arguments,
# e.g. `TS P A B Q` has leaf `nCol A B P` = indices (1, 2, 0).
_NCOL_LEAVES = {
    "TS":       [(1, 2, 0)],
    "CongA":    [(0, 1, 2)],
    "Triangle": [(0, 1, 2)],
    "OS":       [(2, 3, 0), (2, 3, 1)],
    "Cut":      [(0, 1, 2), (0, 1, 3)],
}


def _bridge_conclude_def(tac: str, lean_type: str) -> str:
    """If `tac` builds an nCol-leaf definition, materialise the `¬ Col ⟹ nCol`
    bridge BEFORE running `conclude_def`, so its build path discharges the `nCol`
    leaf by `assumption`. Each bridge is wrapped in `try`, making it a no-op on
    the extract/fast path (no `¬ Col` present). A no-op for every other tactic.

    NB: the bridge must run first, NOT as a `first | conclude_def | (bridge; …)`
    fallback — `conclude_def`'s build does not fail cleanly on a missing `nCol`
    leaf (it commits and leaves a residual `¬BetS …` conjunct), so `first` never
    backtracks to the bridge branch."""
    if not tac.startswith("conclude_def "):
        return tac
    defn = tac.split()[1]
    leaves = _NCOL_LEAVES.get(defn)
    if not leaves:
        return tac
    toks = lean_type.split()
    if not toks or toks[0] != defn:
        return tac
    args = toks[1:]
    if any(max(t) >= len(args) for t in leaves):
        return tac
    bridges = "; ".join(
        f"(try (have : nCol {args[a]} {args[b]} {args[c]} := nCol_notCol _ _ _ (by assumption)))"
        for (a, b, c) in leaves
    )
    return f"{bridges}; {tac}"


# A single inline `assert (TYPE) by (TAC)` (or bare `by auto`), as it appears
# INSIDE another assert's proof — e.g. the outer proof of
#   `assert (nCol A B C) by (assert (nCol B C A) by auto; forward_using …)`.
_INLINE_ASSERT = re.compile(
    r"^assert\s*\((?:\s*\w+\s*:)?\s*(?P<type>.*?)\)\s*by\s*"
    r"(?:\(\s*(?P<tac>.*)\s*\)|(?P<tacbare>.+?))$",
    re.DOTALL,
)


def translate_tactic(tac: str) -> tuple[str, bool]:
    """Return (lean_tactic, recognized?). Unrecognized → flagged for fallback."""
    tac = tac.strip().rstrip(".")
    # NESTED inline assert / tactic sequence. GeoCoq sometimes proves an outer
    # assert with a `;`-sequence that itself contains an inline `assert (Y) by (T)`
    # (e.g. `assert (X) by (assert (Y) by auto; forward_using lemma_NCorder)`). The
    # inner assert is a Coq construct with no Lean syntax, so it must be turned into
    # a Lean `have`; the other `;`-parts are translated recursively. Each part is
    # parenthesised so the `;` sequences the OUTER goal (not the `have`'s proof).
    if re.search(r"\bassert\s*\(", tac):
        parts = [p.strip() for p in _depth_split(tac, ";") if p.strip()]
        # Only take this path for a genuine `;`-sequence OR a single inline assert —
        # otherwise fall through to normal handling (a lone unrecognised `assert …`
        # that does NOT match `_INLINE_ASSERT` must NOT re-enter here, else infinite
        # recursion). This guard guarantees progress: the `else` branch below only ever
        # recurses on a `;`-free part, which re-enters with `len(parts) == 1` and either
        # matches `_INLINE_ASSERT` or falls through.
        if parts and (len(parts) > 1 or _INLINE_ASSERT.match(parts[0])):
            out: list[str] = []
            all_ok = True
            for p in parts:
                am = _INLINE_ASSERT.match(p)
                if am:
                    ty = translate_type(am.group("type").strip())
                    sub, ok = translate_tactic(am.group("tac") or am.group("tacbare") or "")
                    out.append(f"(have : {ty} := by {sub})")
                else:
                    sub, ok = translate_tactic(p)
                    out.append(f"({sub})")
                all_ok = all_ok and ok
            return "; ".join(out), all_ok
    for kw in _PORTED:
        if tac == kw or tac.startswith(kw + " "):
            return tac, True
    # `auto using parnotmeet` — GeoCoq's local helper `parnotmeet : Par A B C D
    # -> ~ Meet A B C D`, whose own proof body is `conclude_def Par`. The `~ Meet`
    # goal is the non-meeting conjunct of a `Par` hypothesis, so emit `conclude_def
    # Par` directly. Generic `auto`/`close` whnf-explodes on the (existential,
    # Circle-heavy) `Par` definition and times out.
    if re.match(r"^(?:auto|eauto)\s+using\s+parnotmeet\b", tac):
        return "conclude_def Par", True
    # Coq's manual def-elimination idioms, all equivalent to `conclude_def X`
    # (unfold definition X, expose its existential/conjunction structure, close):
    #   `unfold X in H; decompose [ex and] H; auto`         (prop_44A: ~Meet from Par)
    #   `[remove_double_neg;] unfold X in *; assumption`     (prop_42: CongA body from ¬¬CongA)
    # `conclude_def X` does the unfold, the (double-)negation stripping, and the
    # witness/conjunct extraction in one robust step.
    um = re.match(r"^(?:remove_double_neg\s*;\s*)?unfold\s+(?P<def>\w+)\s+in\s+\S+\s*;\s*"
                  r".*(?:auto|eauto|assumption|tauto|easy)\s*$", tac)
    if um:
        return f"conclude_def {um.group('def')}", True
    # Coq general-purpose closers (`auto`, `eauto 20`, `easy`, …) map to our
    # ported `close` macro — the Lean analog of GeoCoq's eauto-backed finish.
    base = tac.split()[0] if tac else ""
    if base in ("auto", "eauto", "intuition", "easy"):
        return "close", True
    if tac in ("assumption", "tauto"):
        return tac, True
    if tac == "reflexivity":
        return "rfl", True
    # `(e)pose proof (LEM …)[; closer]` — Coq adds `LEM …` to the context and then
    # closes by search. This is exactly `conclude LEM` (apply `LEM`, discharge its
    # premises by head-indexed search), so the explicit hypothesis args are not needed.
    pp = re.match(r"^(?:unshelve\s+)?e?pose\s+(?:proof\s+)?\(\s*@?(?P<lem>[A-Za-z_]\w*)", tac)
    if pp:
        return f"conclude {pp.group('lem')}", True
    # apply-family: `simple eapply L` / `eapply L` / `apply L` → `apply L`. The
    # premises become subgoals for the following statements to discharge.
    m = re.match(r"^(?:simple\s+)?e?apply\s+(?P<lem>.+)$", tac)
    if m:
        lem = m.group("lem").rstrip(".").strip()
        # Peel a trailing `;closer` chain, e.g. `apply (L args);assumption`.
        cm = re.match(r"^(?P<head>.+?);\s*(?P<closer>auto|eauto|assumption|tauto"
                      r"|close|easy|intuition)\s*$", lem)
        closer = cm.group("closer") if cm else None
        if cm:
            lem = cm.group("head").strip()
        # `eapply L with (x:=v)…` / `with a b …`: `with` pins L's unification
        # variables. `conclude` recovers them by head-indexed search, so drop
        # the clause and route to conclude.
        wm = re.match(r"^(?P<base>.+?)\s+with\s+\S", lem)
        if wm:
            return f"conclude {_lemma_head(wm.group('base').strip())}", True
        # `apply (L a1 a2 …);assumption` — explicit positional args. The Coq
        # author pinned the points deliberately so premise discharge is a direct
        # `assumption`, not a search. Preserve that: `apply L a1 a2 … <;> closer`.
        # Bare `conclude` here would re-derive the args by unification over the
        # (often huge) context and blow the heartbeat budget.
        if _has_apply_args(lem):
            args_expr = _strip_outer_parens(lem).strip()
            if closer in (None, "assumption", "auto", "eauto", "tauto"):
                # Try the pinned-args apply first (fast, no search — what the Coq
                # author intended); fall back to `conclude L` when direct apply
                # cannot unify, e.g. L concludes a conjunction and the goal is one
                # conjunct (`conclude` projects it).
                return (f"(first | (apply {args_expr} <;> assumption) "
                        f"| conclude {_lemma_head(lem)})"), True
            return f"apply {args_expr}", True
        # `apply (L);auto` (no args) → conclude L: apply L, discharge premises.
        if closer is not None:
            return f"conclude {_lemma_head(lem)}", True
        # plain `apply L` — leave premises as subgoals for the following steps.
        lem = _strip_outer_parens(lem) if lem.startswith("(") else lem
        return f"apply {lem}", True
    return tac, False


def _lemma_head(expr: str) -> str:
    """First identifier of an applied-lemma expression, peeling a leading `@`
    and parens/whitespace: `( axiom_connectivity) with A F` → `axiom_connectivity`."""
    s = expr.strip().lstrip("@").lstrip("(").strip()
    mm = re.match(r"[A-Za-z_]\w*", s)
    return mm.group(0) if mm else s


def _has_apply_args(expr: str) -> bool:
    """True if the applied expression carries positional args beyond the lemma
    name, e.g. `(proposition_30A _ _ E f)` — vs a lone name `(lemma_foo)`."""
    inner = _strip_outer_parens(expr.strip())
    return len(inner.lstrip("@").split()) > 1


# ---------------------------------------------------------------------------
# Proof parsing
# ---------------------------------------------------------------------------

@dataclass
class Step:
    kind: str           # 'have' | 'obtain' | 'neg_block' | 'close' | 'final' | 'raw'
    lean: str           # emitted Lean (may be multi-line)
    ok: bool = True     # False if it fell back to sorry


def _split_statements(body: str) -> list[str]:
    """Split a Coq proof body into statements. A statement ends at a `.` at
    paren/brace depth 0. `{ … }` focus blocks are kept as single tokens."""
    out: list[str] = []
    buf = []
    depth = 0
    i = 0
    while i < len(body):
        c = body[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        buf.append(c)
        # statement boundary: `.` at depth 0, OR a `}` that closes a focus
        # block back to depth 0 (the block is its own statement).
        boundary = False
        if c == "." and depth == 0:
            nxt = body[i + 1] if i + 1 < len(body) else " "
            boundary = nxt.isspace() or i + 1 == len(body)
        elif c == "}" and depth == 0:
            boundary = True
        if boundary:
            stmt = "".join(buf).strip()
            if stmt:
                out.append(stmt)
            buf = []
        i += 1
    tail = "".join(buf).strip()
    if tail:
        out.append(tail)
    return out


# `[let Tf:=fresh in] assert ( [Tf:] TYPE ) by ( TAC )`  (+ optional destruct)
_ASSERT_BY = re.compile(
    r"^(?:rename_H\s+\w+\s*;\s*)?"            # optional `rename_H h;` prefix
    r"(?:let\s+\w+\s*:=\s*fresh\s+in\s+)?"
    r"assert\s*\((?:\s*\w+\s*:)?\s*(?P<type>.*?)\)\s*by\s*"
    r"(?:\(\s*(?P<tac>.*)\s*\)|(?P<tacbare>[^();]+?))"   # `by (tac)` or bare `by auto`
    r"\s*(?:;.*)?$",            # optional trailing  ;destruct … ;spliter
    re.DOTALL,
)
# `assert ( TYPE ).`  (no `by` — a focus block proof follows separately)
_ASSERT_PLAIN = re.compile(r"^assert\s*\((?P<type>.*)\)\s*$", re.DOTALL)
_DESTRUCT = re.compile(r"destruct\s+\w+\s+as\s+\[(?P<vars>[^\]]*)\]")

_IGNORE = re.compile(
    r"^(Proof|Qed|Defined|Show\s+Proof|Unshelve|intros?|all\s*:|exact\s)", re.IGNORECASE
)


def _obtain_arity(type_str: str) -> tuple[list[str], int]:
    """For an `exists X [Y …], BODY`, return (witness_vars, n_body_conjuncts)."""
    s = _strip_outer_parens(type_str.strip())
    m = re.match(r"^exists\s+(?P<vars>[\w\s]+?)\s*,\s*(?P<body>.*)$", s, re.DOTALL)
    if not m:
        return [], 0
    vs = m.group("vars").split()
    body = _strip_outer_parens(m.group("body").strip())
    conj = _depth_split_count(body, "/\\") + 1
    return vs, conj


def _demorgan_haves(leaves: list[str]) -> list[str]:
    """Given the leaves of `h : ¬(D0 \\/ D1 \\/ … \\/ D_{n-1})` (right-nested
    Or), return `have : ¬ Dᵢ := fun c => h (injᵢ c)` lines — the de Morgan
    decomposition that puts every `¬ Dᵢ` directly in context. injᵢ is the
    right-nested-Or coproduct injection: leaf 0 = `Or.inl c`, leaf i<n-1 =
    `Or.inr (… Or.inl c)` with i `Or.inr`s, last leaf = `Or.inr (… c)`."""
    n = len(leaves)
    out: list[str] = []
    for i, leaf in enumerate(leaves):
        if i == 0:
            inj = "Or.inl c"
        elif i < n - 1:
            inj = "Or.inr (" * i + "Or.inl c" + ")" * i
        else:
            inj = "Or.inr (" * i + "c" + ")" * i
        out.append(f"have : ¬ ({translate_type(leaf)}) := fun c => h ({inj})")
    return out


def _eapply_block_to_conclude(block: str) -> str | None:
    """A `{ … }` focus block proving a POSITIVE goal by `[simple] eapply L`
    followed only by premise-discharging steps (`exact H…`, `assumption`,
    `auto`, …) is exactly `conclude L`: apply the lemma, fill its premises
    from context. The Coq `exact H<n>` reference autogenerated hypothesis
    names that do not exist in Lean, so head-indexed `conclude` search is the
    only faithful rendering. Returns `conclude L` or None if the block is not
    of this shape."""
    parts = [p.strip() for p in _split_statements(block) if p.strip()]
    if not parts:
        return None
    head = re.match(r"^(?:simple\s+)?e?apply\s+@?(?P<lem>[A-Za-z_]\w*)\s*$",
                    parts[0].rstrip("."))
    if not head:
        return None
    for p in parts[1:]:
        if not re.match(r"^(?:exact\s+\w+|assumption|e?auto|tauto|easy"
                        r"|intuition|reflexivity)\s*$", p.rstrip(".")):
            return None
    return f"conclude {head.group('lem')}"


def parse_proof(body: str, warn) -> list[Step]:
    stmts = _split_statements(body)
    steps: list[Step] = []
    i = 0
    while i < len(stmts):
        s = re.sub(r"\s+", " ", stmts[i].strip())
        if _IGNORE.match(s):
            i += 1
            continue

        # standalone closer / final tactic (close, contradict, conclude …)
        low = s.rstrip(".").strip()

        # bare existential introduction: `exists W1 W2 …[; tac].` — provide the
        # witnesses and close the body (default `close`). Lean: `exact ⟨Ws, by t⟩`.
        em = re.match(r"^exists\s+(?P<ws>[A-Za-z0-9_ ]+?)\s*(?:;\s*(?P<tac>.+))?$", low)
        if em:
            ws = em.group("ws").split()
            inner, ok_e = translate_tactic(em.group("tac")) if em.group("tac") else ("close", True)
            steps.append(Step("final",
                              f"exact ⟨{', '.join(ws)}, by {inner}⟩", ok_e))
            i += 1
            continue

        # standalone `destruct H as [w1 w2 …][; spliter]` — names the witnesses of
        # a preceding anonymous existential `have` (Coq's `assert (exists …).` +
        # proof-block idiom binds the result to `this`). Lean: `obtain ⟨ws, _⟩`.
        dm = re.match(r"^destruct\s+\w+\s+as\s+\[(?P<vars>[^\]]*)\]\s*(?:;\s*spliter)?$", low)
        if dm:
            vs = re.findall(r"\w+", dm.group("vars"))
            pat = ", ".join(vs + ["_"]) if vs else "_"
            steps.append(Step("raw", f"obtain ⟨{pat}⟩ := this", True))
            i += 1
            continue

        # `remove_exists[; tac]` — the goal is the lemma's existential conclusion;
        # introduce its witnesses (count unknown here) and close the body. Emit a
        # 0..6 witness ladder, mirroring `conclude_def`'s build: the metavar
        # witnesses are pinned by `close`'s assumption search over the body.
        if re.match(r"^remove_exists\s*(?:;\s*.+)?$", low):
            ladder = " | ".join(
                ["close"] + [f"exact ⟨{', '.join(['_'] * k)}, by close⟩" for k in range(1, 7)]
            )
            steps.append(Step("final", f"first | {ladder}", True))
            i += 1
            continue

        lean_c, ok_c = translate_tactic(low)
        if ok_c and (low in ("close", "contradict", "auto", "eauto", "assumption",
                              "tauto", "intuition", "reflexivity", "easy")
                     or low.startswith("conclude ")
                     or low.startswith("conclude_def ")
                     or low.startswith("forward_using ")
                     or re.match(r"^(?:simple\s+)?e?apply\s", low)):
            steps.append(Step("close" if low == "close" else "final", lean_c, ok_c))
            i += 1
            continue

        m = _ASSERT_BY.match(s.rstrip("."))
        if m:
            typ = m.group("type").strip()
            tac, ok = translate_tactic(m.group("tac") or m.group("tacbare") or "")
            dvars = _DESTRUCT.search(s)
            if "exists" in typ.split(",")[0] or re.match(r"^\(?\s*exists", typ):
                vs, conj = _obtain_arity(typ)
                holes = ", ".join(["_"] * conj)
                names = ", ".join(vs) if vs else "x"
                lean_ty = translate_type(re.sub(r"^\(?\s*exists\s+[\w\s]+?\s*,\s*", "",
                                                 typ).rstrip(")"))
                # rebuild full exists type for the annotation
                full = translate_type(typ)
                pat = f"⟨{names}, {holes}⟩" if conj else f"⟨{names}⟩"
                steps.append(Step("obtain",
                                  f"obtain {pat} : {full} := by {tac}", ok))
            else:
                lean_ty = translate_type(typ)
                steps.append(Step("have",
                                  f"have : {lean_ty} := by {_bridge_conclude_def(tac, lean_ty)}", ok))
            if not ok:
                warn(f"unrecognized tactic in assert: {m.group('tac')!r}")
            i += 1
            continue

        # ---- `by cases on (D).` + one `{ … }` block per disjunct ------------
        # `emit_cases` parses the disjunction + its case blocks beginning at
        # `start`, returning (lean_lines, next_index, ok) or (None, start, False).
        def emit_cases(disj: str, start: int):
            n = _depth_split_count(disj, "\\/") + 1     # number of disjuncts
            cases = []
            j = start
            while j < len(stmts) and len(cases) < n and stmts[j].lstrip().startswith("{"):
                block = stmts[j].strip().lstrip("{").rstrip("}").strip()
                cases.append(parse_proof(block, warn))
                j += 1
            if len(cases) != n:
                return None, start, False
            pat = " | ".join(f"c{k+1}" for k in range(n))
            prove = ("first | assumption | exact nCol_or_Col _ _ _ "
                     "| exact Col_or_nCol _ _ _ | exact Classical.em _ | tauto | aesop")
            lines = [f"rcases (show {translate_type(disj)} by {prove}) with {pat}"]
            ok_all = True
            for cb in cases:
                blines = [ln for st in cb for ln in st.lean.splitlines()] or ["skip"]
                ok_all = ok_all and all(st.ok for st in cb)
                lines.append("· " + blines[0])
                lines += ["  " + bl for bl in blines[1:]]
            return lines, j, ok_all

        # standalone `by cases on` (case split that proves the current goal)
        m = re.match(r"^by cases on\s*\((?P<disj>.*)\)$", s.rstrip("."), re.DOTALL)
        if m:
            disj = m.group("disj").strip()
            lines, j, ok = emit_cases(disj, i + 1)
            if lines is not None:
                steps.append(Step("cases", "\n".join(lines), ok))
                i = j
                continue
            warn(f"by cases on: case-blocks did not parse for ({disj})")
            steps.append(Step("raw", f"sorry -- TODO: by cases on ({disj})", False))
            i += 1
            continue

        # `assert (TYPE).` followed by `by cases on (D).` + blocks  → a `have`
        # whose proof is the case split. This is the dominant GeoCoq idiom for
        # case-analysed sub-results.
        m = _ASSERT_PLAIN.match(s.rstrip("."))
        if m and i + 1 < len(stmts):
            cm = re.match(r"^by cases on\s*\((?P<disj>.*)\)$",
                          stmts[i + 1].strip().rstrip("."), re.DOTALL)
            if cm:
                typ = translate_type(m.group("type"))
                lines, j, ok = emit_cases(cm.group("disj").strip(), i + 2)
                if lines is not None:
                    inner = "\n".join("    " + ln for ln in lines)
                    steps.append(Step("cases_have",
                                      f"have : {typ} := by\n{inner}", ok))
                    i = j
                    continue
            # `assert (TYPE).` followed by a `{ … }` focus block. Two shapes:
            #  - TYPE a negation (`~ …`): proved by assuming the predicate and
            #    deriving a contradiction → `intro h; <block>`.
            #  - TYPE positive: a direct sub-proof. The dominant case is an
            #    `[simple] eapply L. exact …` chain, which is `conclude L`.
            if stmts[i + 1].lstrip().startswith("{"):
                typ_raw = m.group("type").strip()
                typ = translate_type(typ_raw)
                block = stmts[i + 1].strip().lstrip("{").rstrip("}").strip()
                if typ_raw.lstrip().startswith("~"):
                    sub = parse_proof(block, warn)
                    inner = ["    " + ln for st in sub for ln in st.lean.splitlines()]
                    # `~ ~ (D1 \/ D2 \/ …)`: after `intro h`, h : ¬(disjunction).
                    # Expose each `¬ Dᵢ` by de Morgan so the body's `conclude L` /
                    # `contradict` match them as direct hypotheses instead of
                    # re-deriving `h ∘ Or.inˣ` under premise search — which blows
                    # the heartbeat budget on the large contexts these blocks sit in.
                    dm = re.match(r"^~\s*~\s*(?P<d>.+)$", typ_raw.strip(), re.DOTALL)
                    demorgan: list[str] = []
                    if dm:
                        d = _strip_outer_parens(dm.group("d").strip())
                        leaves = [l.strip() for l in _depth_split(d, "\\/") if l.strip()]
                        if len(leaves) >= 2:
                            demorgan = ["    " + hv for hv in _demorgan_haves(leaves)]
                    body = "\n".join(["    intro h"] + demorgan + inner)
                    lean = f"have : {typ} := by\n{body}"
                    steps.append(Step("neg_block", lean, all(st.ok for st in sub)))
                else:
                    concl = _eapply_block_to_conclude(block)
                    if concl is not None:
                        steps.append(Step("have", f"have : {typ} := by {concl}", True))
                    else:
                        sub = parse_proof(block, warn)
                        inner = "\n".join("    " + ln for st in sub
                                          for ln in st.lean.splitlines()) or "    sorry"
                        steps.append(Step("have", f"have : {typ} := by\n{inner}",
                                          bool(sub) and all(st.ok for st in sub)))
                i += 2
                continue

        # fallback — never crash
        warn(f"unhandled statement: {s!r}")
        steps.append(Step("raw", f"sorry -- TODO: {s}", False))
        i += 1

    # Permutation-step elimination. The bounded `conclude` engine now discharges
    # Col / nCol / BetS / Cong premises MODULO argument permutation (perm_core's
    # `*_perm` lemmas + `conclude_bounded`'s `permProof`), and every consumer
    # (`conclude` / `close` / `conclude_def` / `contradict` / `forward_using`)
    # routes through that perm-aware matcher. So an explicit
    #   `have : X := by forward_using lemma_(collinearorder|NCorder|
    #                                        congruenceflip|congruencesymmetric)`
    # that only REORIENTS an already-derived fact is redundant — the matcher
    # reconstructs X from the original orientation wherever it is needed. Drop
    # these pure-permutation steps (applies at every nesting level, since
    # `parse_proof` recurses into focus blocks).
    #
    # EXCEPTION — substitution feeders. A perm-`have` whose fact is consumed by a
    # later `conclude cn_equalitysub` (equals-for-equals substitution) must STAY:
    # `cn_equalitysub`'s `apply` does higher-order unification, and with the
    # ready-oriented fact removed from context it spins in `whnf` instead of
    # reconstructing (the matcher never gets to run — the blow-up is in the apply,
    # not premise discharge). The feed is recognised structurally: the substitution
    # target shares all-but-one point with the perm fact (one point substituted).
    # This is GeoCoq-faithful — GeoCoq itself keeps explicit steps where its own
    # automation doesn't reach — and general (a uniform structural rule, no
    # per-file logic). Over-approximates slightly (keeps a few safe haves), which
    # is the safe direction.
    steps = [st for st in steps
             if not (_PERM_STEP.match(st.lean.strip())
                     and not _feeds_cn_equalitysub(st.lean.strip(), steps))]
    return steps


# Substitution-target `have`s: `conclude cn_equalitysub` proving a Col/nCol atom.
_SUBST_TARGET = re.compile(
    r"have : (Col|nCol) (.+?) := by conclude cn_equalitysub\b")
# The perm-`have`'s own predicate + points (to compare against substitution targets).
_PERM_FACT = re.compile(
    r"^have : (Col|nCol) (.+?) := by forward_using "
    r"lemma_(?:collinearorder|NCorder)\b")


def _feeds_cn_equalitysub(perm_line: str, steps: list[Step]) -> bool:
    """True if `perm_line`'s Col/nCol fact is consumed by SOME later
    `conclude cn_equalitysub` in the proof (its target shares all-but-one point
    — the substitution replaces exactly one point). Scans every step's emitted
    Lean, including nested focus/neg-block sub-steps."""
    m = _PERM_FACT.match(perm_line)
    if not m:
        return False
    head, pts = m.group(1), set(m.group(2).split())
    for st in steps:
        for ln in st.lean.splitlines():
            t = _SUBST_TARGET.search(ln.strip())
            if not t:
                continue
            if t.group(1) != head:
                continue
            tp = t.group(2).split()
            if len(tp) == len(pts) and len(pts & set(tp)) == len(pts) - 1:
                return True
    return False


# ---------------------------------------------------------------------------
# Statement + file emission
# ---------------------------------------------------------------------------

def parse_context_class(coq_text: str) -> str:
    m = re.search(r"Context\s*`\{[^:]*:\s*(\w+)\s*\}", coq_text)
    return m.group(1) if m else "euclidean_neutral_ruler_compass"


# Known predicates whose arguments are themselves congruence-classes ("line" =
# Tpoint -> Tpoint -> Prop, "angle" = Tpoint -> Tpoint -> Tpoint -> Prop)
# rather than bare Points, keyed to the 0-indexed argument positions that are
# class-typed. Used to infer a quantified variable's type when it only ever
# appears as an ARGUMENT (e.g. `Ang A B C a1`), never applied directly as its
# own predicate (`a1 X Y Z`).
_CLASS_ARG_POSITIONS = {
    "Q_Cong": {0: 2}, "Q_Cong_Null": {0: 2}, "Len": {2: 2}, "EqL": {0: 2, 1: 2},
    "Q_CongA": {0: 3}, "Ang": {3: 3}, "Ang_Flat": {0: 3}, "EqA": {0: 3, 1: 3},
    "Q_CongA_Acute": {0: 3}, "Ang_Acute": {3: 3}, "Q_CongA_nNull": {0: 3},
    "Q_CongA_nFlat": {0: 3}, "Q_CongA_Null": {0: 3}, "Q_CongA_Null_Acute": {0: 3},
    "is_null_anga'": {0: 3}, "Q_CongA_nNull_Acute": {0: 3},
    "Lcos": {0: 2, 1: 2, 2: 3}, "Eq_Lcos": {0: 2, 1: 3, 2: 2, 3: 3},
    "Lcos2": {0: 2, 1: 2, 2: 3, 3: 3}, "Eq_Lcos2": {0: 2, 1: 3, 2: 3, 3: 2, 4: 3, 5: 3},
    "Lcos3": {0: 2, 1: 2, 2: 3, 3: 3, 4: 3},
    "Eq_Lcos3": {0: 2, 1: 3, 2: 3, 3: 3, 4: 2, 5: 3, 6: 3, 7: 3},
}


def _rest_fragments(rest: str) -> list[list[str]]:
    """Split a proposition body (Coq OR already-Lean-translated syntax) at its
    top-level connectives/punctuation into fragments, each tokenized — so
    `head arg1 arg2 …` applications can be read off positionally without being
    confused by neighbouring clauses."""
    frags = re.split(r"/\\|\\/|<->|->|~|[(),]|∧|∨|↔|→|¬|∀|∃", rest)
    return [f.split() for f in frags if f.split()]


def _infer_var_type(var: str, rest: str) -> str:
    """Most GeoCoq-quantified variables are Points, but Ch13+ also quantifies
    over *congruence classes* — a "line" (segment-length class) applied to 2
    points, or an "angle" applied to 3 points. Two detection passes:
    (1) the variable is itself applied as a predicate (`l A B`, `a X Y Z`);
    (2) the variable only appears as an argument of a KNOWN class-typed
    predicate (`Ang A B C a1`) — looked up via `_CLASS_ARG_POSITIONS`."""
    for toks in _rest_fragments(rest):
        if toks[0] == var:
            n = 0
            for t in toks[1:]:
                if re.match(r"^[A-Z]\w*'?$", t):
                    n += 1
                else:
                    break
            if n >= 3:
                return "Tpoint → Tpoint → Tpoint → Prop"
            if n >= 2:
                return "Tpoint → Tpoint → Prop"
        elif toks[0] in _CLASS_ARG_POSITIONS:
            for i, t in enumerate(toks[1:]):
                if t == var and i in _CLASS_ARG_POSITIONS[toks[0]]:
                    arity = _CLASS_ARG_POSITIONS[toks[0]][i]
                    return ("Tpoint → Tpoint → Tpoint → Prop" if arity == 3
                            else "Tpoint → Tpoint → Prop")
    return "Tpoint"


def _statement_text(coq_lemma: str) -> str:
    """Isolate the `Lemma foo : <statement>.` text, ending at the first
    paren-depth-0 period after the `:` — NOT `.split("Proof")` followed by a
    greedy regex to the LAST period, which silently swallows the whole proof
    body into "the statement" for lemmas that omit the `Proof.` keyword and
    go straight into tactics (a real, occurring GeoCoq style)."""
    ci = coq_lemma.find(":")
    if ci < 0:
        return coq_lemma
    depth = 0
    for i in range(ci + 1, len(coq_lemma)):
        c = coq_lemma[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "." and depth <= 0:
            return coq_lemma[ci + 1:i]
    return coq_lemma[ci + 1:]


def translate_statement(coq_lemma: str) -> tuple[str, str]:
    """Return (lean_signature_after_colon, intro_line). Splits the leading
    `forall …,` binders and `->` hypotheses to build an `intro` line."""
    stmt = _statement_text(coq_lemma).strip()
    # leading binders
    # leading binders — accept an optional explicit type annotation
    # (`forall A B C : Point, …`), not just the bare `forall A B C, …` form.
    fm = re.match(r"^forall\s+(?P<vars>[\w\s']+?)\s*(?::\s*\w+\s*)?,\s*(?P<rest>.*)$",
                  stmt, re.DOTALL)
    intro_names: list[str] = []
    if fm:
        vs = fm.group("vars").split()
        rest = fm.group("rest")
        intro_names += vs
        # GeoCoq quantified variables are usually Points, but some (Ch13+)
        # are line/angle congruence-classes — infer per-variable arity from
        # how each is actually applied in the body, and group same-type vars
        # into one binder each so mixed foralls type-check.
        groups: list[tuple[str, list[str]]] = []
        for v in vs:
            ty = _infer_var_type(v, rest)
            if groups and groups[-1][0] == ty:
                groups[-1][1].append(v)
            else:
                groups.append((ty, [v]))
        binders = " ".join(f"({' '.join(names)} : {ty})" for ty, names in groups)
        lean_stmt = f"∀ {binders}, " + translate_type(rest)
    else:
        rest = stmt
        lean_stmt = translate_type(stmt)
    n_hyp = _depth_split_count(rest, "->")
    intro_names += [f"h{k+1}" for k in range(n_hyp)]
    intro = "intro " + " ".join(intro_names) if intro_names else ""
    # Any OTHER bare `∀ v1 v2 …,` left over — nested inside an `↔`/`∧`/deeper
    # scope, or the top-level one when the statement doesn't start with a bare
    # `forall` (e.g. `(forall …) <-> (forall …)`) — needs its own type
    # annotation too, or Lean's elaborator gets stuck on an unconstrained
    # metavariable. All such GeoCoq-quantified variables are bare Points; the
    # line/angle cases are only ever the outermost per-lemma binder, already
    # handled above.
    def _annotate_bare(m: re.Match) -> str:
        kind, vars_str = m.group(1), m.group(2)
        vs = vars_str.split()
        body = lean_stmt[m.end():]           # best-effort lookahead scope
        groups: list[tuple[str, list[str]]] = []
        for v in vs:
            ty = _infer_var_type(v, body)
            if groups and groups[-1][0] == ty:
                groups[-1][1].append(v)
            else:
                groups.append((ty, [v]))
        binders = " ".join(f"({' '.join(names)} : {ty})" for ty, names in groups)
        return f"{kind} {binders},"
    lean_stmt = re.sub(r"(∀|∃) ((?:[A-Za-z][\w']*\s+)*[A-Za-z][\w']*),",
                        _annotate_bare, lean_stmt)
    return lean_stmt, intro


_SECONDARY_INDEX_CACHE: dict[str, dict[str, str]] = {}

def _build_secondary_index(coq_dir: str) -> dict[str, str]:
    """Map every lemma that is NOT the primary (filename-stem) lemma of its `.v`
    file to that file's stem — e.g. `proposition_15a -> proposition_15`. Lets the
    importer route a dependency on a secondary lemma to the module that defines it.
    Cached per directory (the `.v` set is stable across a transpile run)."""
    if coq_dir in _SECONDARY_INDEX_CACHE:
        return _SECONDARY_INDEX_CACHE[coq_dir]
    idx: dict[str, str] = {}
    if os.path.isdir(coq_dir):
        for fn in os.listdir(coq_dir):
            if not fn.endswith(".v"):
                continue
            stem = fn[:-2]
            with open(os.path.join(coq_dir, fn)) as f:
                names = re.findall(r"^[ \t]*(?:Lemma|Theorem)[ \t]+(\w+)", f.read(), re.M)
            for nm in names:
                if nm != stem:
                    idx[nm] = stem
    _SECONDARY_INDEX_CACHE[coq_dir] = idx
    return idx


def transpile(coq_path: str, lemma: str) -> tuple[str, list[str]]:
    warnings: list[str] = []
    coq_lemma = brief.extract_coq_lemma(coq_path, lemma)
    if not coq_lemma:
        raise SystemExit(f"lemma {lemma!r} not found in {coq_path}")
    with open(coq_path) as f:
        full = f.read()
    cls = parse_context_class(full)

    proof = coq_lemma.split("Proof.", 1)[1] if "Proof." in coq_lemma else ""
    proof = re.split(r"\bQed\b|\bDefined\b", proof)[0]
    proof = _strip_comments(proof)

    lean_stmt, intro = translate_statement(coq_lemma)
    steps = parse_proof(proof, warnings.append)

    deps = brief.extract_deps(proof)
    imports = ["import GeocoqTranslate.Elements.OriginalProofs.euclidean_tactics"]
    lemdir = os.path.join(LEAN_ROOT, "Elements/OriginalProofs/Lemmas")
    propdir = os.path.join(LEAN_ROOT, "Elements/OriginalProofs")
    have_lemfiles = set(os.listdir(lemdir)) if os.path.isdir(lemdir) else set()
    have_propfiles = ({f for f in os.listdir(propdir) if f.endswith(".lean")}
                      if os.path.isdir(propdir) else set())

    # A `.v` file may define SEVERAL lemmas (e.g. `proposition_15.v` defines
    # `proposition_15`, `proposition_15a`, `proposition_15b`). Coq's `Require Export
    # <file>` makes ALL of them visible to dependents. So a dependency like
    # `proposition_15a` is NOT its own module — it lives in `proposition_15.lean`.
    # Build `secondary_lemma_name -> file_stem` so we can import the RIGHT module.
    secondary_index = _build_secondary_index(os.path.dirname(coq_path))

    def _resolve_import(d):
        """The `import` line that brings dependency `d` into scope, or None.
        Returns None for a LOCAL reference (the main lemma or one of the secondary
        lemmas emitted into THIS same module) — importing it would be a self-import."""
        if d == lemma or secondary_index.get(d) == lemma:
            return None
        if f"{d}.lean" in have_lemfiles:
            return f"import GeocoqTranslate.Elements.OriginalProofs.Lemmas.{d}"
        if f"{d}.lean" in have_propfiles:
            return f"import GeocoqTranslate.Elements.OriginalProofs.{d}"
        stem = secondary_index.get(d)              # d is a secondary lemma of `stem`.v
        if stem and stem != lemma:
            if f"{stem}.lean" in have_propfiles:
                return f"import GeocoqTranslate.Elements.OriginalProofs.{stem}"
            if f"{stem}.lean" in have_lemfiles:
                return f"import GeocoqTranslate.Elements.OriginalProofs.Lemmas.{stem}"
        return None

    def _emit_body(intro_str, step_list):
        bl = [f"  {intro_str}"] if intro_str else []
        for st in step_list:
            for ln in st.lean.splitlines():
                bl.append("  " + ln)
        return bl

    # In-file HELPER lemmas: a dependency may be defined in THIS .v file (before the
    # target) rather than in its own file — e.g. `lemma_togethera` inside
    # `proposition_22.v`. There is no separate module to import, so translate the
    # helper inline and emit it before the main lemma (in the same namespace). Its
    # OWN external dependencies are added to the import list.
    inline_helpers: list[list[str]] = []
    for d in deps:
        imp = _resolve_import(d)
        if imp:
            imports.append(imp)
        else:
            helper_text = brief.extract_coq_lemma(coq_path, d)
            if not helper_text:
                continue                            # genuinely unresolved (left as-is)
            h_stmt, h_intro = translate_statement(helper_text)
            h_proof = helper_text.split("Proof.", 1)[1] if "Proof." in helper_text else ""
            h_proof = re.split(r"\bQed\b|\bDefined\b", h_proof)[0]
            h_proof = _strip_comments(h_proof)
            h_steps = parse_proof(h_proof, warnings.append)
            inline_helpers.append([_MAXHB, f"theorem {d} :", f"    {h_stmt} := by",
                                   *_emit_body(h_intro, h_steps), ""])
            for hd in brief.extract_deps(h_proof):  # helper's own external imports
                imp_h = _resolve_import(hd)
                if imp_h:
                    imports.append(imp_h)

    # SECONDARY lemmas defined AFTER the main lemma in this same .v file
    # (e.g. `proposition_15a`, `proposition_15b` after `proposition_15`). They are
    # exported by Coq's `Require Export` and referenced by OTHER files, so emit them
    # as top-level theorems in THIS module. (Helpers defined BEFORE the main lemma —
    # `lemma_togethera` in `proposition_22.v` — are handled by the inline path above.)
    main_pos = max(full.find(f"Lemma {lemma}"), full.find(f"Theorem {lemma}"))
    secondary_lemmas: list[list[str]] = []
    for m in re.finditer(r"^[ \t]*(?:Lemma|Theorem)[ \t]+(\w+)", full, re.M):
        nm = m.group(1)
        if nm == lemma or m.start() <= main_pos:
            continue
        sec_text = brief.extract_coq_lemma(coq_path, nm)
        if not sec_text:
            continue
        s_stmt, s_intro = translate_statement(sec_text)
        s_proof = sec_text.split("Proof.", 1)[1] if "Proof." in sec_text else ""
        s_proof = re.split(r"\bQed\b|\bDefined\b", s_proof)[0]
        s_proof = _strip_comments(s_proof)
        s_steps = parse_proof(s_proof, warnings.append)
        secondary_lemmas.append([_MAXHB, f"theorem {nm} :", f"    {s_stmt} := by",
                                 *_emit_body(s_intro, s_steps), ""])
        for sd in brief.extract_deps(s_proof):      # secondary's own external imports
            imp_s = _resolve_import(sd)
            if imp_s:
                imports.append(imp_s)

    body_lines = _emit_body(intro, steps)

    out = []
    out.append(f"/- Transpiled from {os.path.relpath(coq_path)} :: {lemma}")
    out.append("   Structure-preserving; generated by geolean_transpile. -/")
    out += list(dict.fromkeys(imports))           # preserve order, drop duplicates
    out.append("")
    out.append("namespace GeocoqTranslate.Elements")
    # open the full class hierarchy up to and including the detected class, so
    # every inherited predicate field is in scope — not just the leaf class's.
    # The chain is linear: basis ⊂ neutral ⊂ ruler_compass ⊂ euclidean ⊂ area.
    # A proof under `area` still uses `postulate_Euclid5` (a `euclidean_euclidean`
    # field), so that intermediate class must be opened too.
    _HIER = ["euclidean_neutral_basis", "euclidean_neutral",
             "euclidean_neutral_ruler_compass", "euclidean_euclidean", "area"]
    if cls in _HIER:
        opens = _HIER[: _HIER.index(cls) + 1]
    else:
        opens = _HIER[:3] + [cls]
    out.append("open " + " ".join(opens))
    out.append(f"variable {{Point : Type}} [{cls} Point]")
    out.append("")
    for helper in inline_helpers:                 # in-file helper lemmas, emitted first
        out += helper
    out.append(_MAXHB)
    out.append(f"theorem {lemma} :")
    out.append(f"    {lean_stmt} := by")
    out += body_lines
    out.append("")
    for sec in secondary_lemmas:                  # extra lemmas from the same .v file
        out += sec
    out.append("end GeocoqTranslate.Elements")
    return "\n".join(out) + "\n", warnings


def main():
    ap = argparse.ArgumentParser(description="GeoCoq → Lean structure-preserving transpiler")
    ap.add_argument("coq_file")
    ap.add_argument("lemma")
    ap.add_argument("-o", "--output", help="write Lean to this path (default: stdout)")
    args = ap.parse_args()
    lean, warnings = transpile(args.coq_file, args.lemma)
    if args.output:
        with open(args.output, "w") as f:
            f.write(lean)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(lean)
    for w in warnings:
        print(f"  [warn] {w}", file=sys.stderr)
    print(f"  {len(warnings)} fallback(s)", file=sys.stderr)


if __name__ == "__main__":
    main()
