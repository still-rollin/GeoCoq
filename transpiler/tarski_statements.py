#!/usr/bin/env python3
"""tarski_statements — emit Lean theorem *stubs* for a Tarski_dev chapter.

Layer 2 of the reconstruction pipeline (see docs/tarski_architecture.md §5.1):
translate every `Lemma`/`Theorem` STATEMENT of a Tarski `.v` chapter into a Lean
`theorem <name> : <stmt> := by sorry`. Deterministic — no proof content. Reuses
`geolean_transpile.translate_statement` (which already handles `forall`, `->`,
connectives, `~`, `neq`/`eq`); adds Tarski-specific surface fixes (`<>` ≠, point
type `Tpoint`).

The emitted file is the reconstruction *target*: the oracle-guided loop then fills
each `sorry` using the ported automation (col_refl/cong_refl/assert_diffs/…) and the
Rocq proof as a hint source.

Usage:
    python3 transpiler/tarski_statements.py theories/Main/Tarski_dev/Ch06_out_lines.v \
        -o /tmp/Ch06_stubs.lean
"""
from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geolean_transpile as gt  # noqa: E402
import coqtoleanbrief as brief   # noqa: E402

POINT = "Tpoint"
_MAXHB = "set_option maxHeartbeats 400000 in"

# Coq Context class → the Lean typeclass to open/require. The chain mirrors the
# Lean base in GeocoqTranslate/Tarski/Axioms.lean.
_DEFAULT_CLASS = "Tarski_neutral_dimensionless_with_decidable_point_equality"


def list_lemmas(coq_text: str) -> list[str]:
    """All lemma/theorem names declared in a chapter, in source order."""
    return re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w+)",
                      coq_text, re.M)


def detect_class(coq_text: str) -> str:
    """The section `Context` typeclass, e.g. `Tarski_neutral_dimensionless…`."""
    m = re.search(r"Context\s*`?\{[^:}]*:\s*(\w+)", coq_text)
    return m.group(1) if m else _DEFAULT_CLASS


def _tarski_fixups(lean_stmt: str) -> str:
    """Surface fixes beyond the shared translator: Coq `<>` (disequality) → `≠`,
    and the point type `Point` → `Tpoint` (matching the Lean Tarski base)."""
    s = lean_stmt.replace("<>", "≠")
    s = re.sub(r":\s*Point\)", f": {POINT})", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def translate_one(coq_lemma: str) -> str | None:
    """`Lemma L : STMT.` → the Lean signature after the colon, or None on failure.

    Unlike the shared `geolean_transpile.translate_statement`, the leading-`forall`
    binder regex accepts primes and digits (`A'`, `C'`, `A0`, `D0`) — pervasive in
    Tarski point names — so every quantified point gets its `: Tpoint` annotation
    (without which the geometry predicates cannot resolve their instance)."""
    try:
        m = re.search(r":\s*(?P<stmt>.*?)\.\s*$",
                      coq_lemma.split("Proof")[0], re.DOTALL)
        stmt = m.group("stmt").strip() if m else coq_lemma
        fm = re.match(r"^forall\s+(?P<vars>[\w\s']+?)\s*(?::\s*[\w']+\s*)?,\s*(?P<rest>.*)$",
                      stmt, re.DOTALL)
        if fm:
            vs = fm.group("vars").split()
            lean_stmt = f"∀ ({' '.join(vs)} : {POINT}), " + gt.translate_type(fm.group("rest"))
        else:
            lean_stmt = gt.translate_type(stmt)
    except Exception:
        return None
    return _tarski_fixups(lean_stmt)


def emit(coq_path: str) -> tuple[str, int, int]:
    with open(coq_path) as f:
        full = f.read()
    names = list_lemmas(full)
    cls = detect_class(full)
    stem = os.path.basename(coq_path)[:-2]

    out: list[str] = []
    out.append(f"/- Statement stubs transpiled from {os.path.relpath(coq_path)}")
    out.append("   Layer-2 (statements only); proofs are `sorry` pending reconstruction. -/")
    out.append("import GeocoqTranslate.Tarski.Axioms")
    out.append("import GeocoqTranslate.Tarski.Definitions")
    out.append("")
    out.append("namespace GeocoqTranslate.Tarski")
    out.append("open Tarski_neutral_dimensionless "
               "Tarski_neutral_dimensionless_with_decidable_point_equality")
    out.append(f"variable {{{POINT} : Type}} [{cls} {POINT}]")
    out.append("")

    ok = 0
    total = 0
    for nm in names:
        src = brief.extract_coq_lemma(coq_path, nm)
        if not src:
            continue
        total += 1
        stmt = translate_one(src)
        if stmt is None:
            out.append(f"-- SKIPPED (statement did not translate): {nm}")
            continue
        ok += 1
        out.append(_MAXHB)
        out.append(f"theorem {nm} :")
        out.append(f"    {stmt} := by sorry")
        out.append("")

    out.append("end GeocoqTranslate.Tarski")
    return "\n".join(out) + "\n", ok, total


def main() -> None:
    ap = argparse.ArgumentParser(description="Emit Lean statement stubs for a Tarski chapter")
    ap.add_argument("coq_file")
    ap.add_argument("-o", "--output", help="write Lean to this path (default stdout)")
    args = ap.parse_args()
    lean, ok, total = emit(args.coq_file)
    if args.output:
        with open(args.output, "w") as f:
            f.write(lean)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(lean)
    print(f"  {ok}/{total} statements translated", file=sys.stderr)


if __name__ == "__main__":
    main()
