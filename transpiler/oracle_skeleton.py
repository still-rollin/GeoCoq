#!/usr/bin/env python3
"""oracle_skeleton — extract a proof SKELETON from a GeoCoq lemma (Layer-3 oracle).

Julien's method (Coghetto's for Isabelle): the Rocq proof is NOT translated
line-by-line. It is used as an ORACLE for the *intermediate statements* a
reconstruction needs — above all the ones that CREATE NEW POINTS
(`segment_construction` / `prolong` / `assert (exists …)`), per his heuristic
"keep the intermediate statements that introduce new points". The final Lean
proof is kernel-checked, so the oracle may be wrong or incomplete without
affecting soundness.

This script parses ONE lemma's Ltac proof and emits a structured skeleton:
  · NEW-POINT steps   — existential/construction asserts (kept; become `obtain`),
  · HAVE steps        — other intermediate `assert` statements (become `have`),
  · the justifying lemma names (`apply`/`eapply`) — the base the reconstruction
    must be able to call (closure tactics, or already-ported lemmas).

Each intermediate statement is also run through the shared type translator so the
skeleton is directly usable as Lean `have`/`obtain` goals. Deliberately heuristic
— a prototype oracle, not a full Ltac interpreter.

Usage:
    python3 transpiler/oracle_skeleton.py theories/Main/Tarski_dev/Ch06_out_lines.v l6_3_1
    python3 transpiler/oracle_skeleton.py <file.v> --all       # every lemma
"""
from __future__ import annotations
import argparse, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import geolean_transpile as gt        # noqa: E402
import coqtoleanbrief as brief        # noqa: E402

# Ltac idioms that construct a fresh point (Julien's "keep new-point steps").
POINT_CREATORS = (r"segment_construction|point_construction_different|prolong|"
                  r"l6_11|symmetric_point_construction|mid_")


def _translate(stmt: str) -> str:
    """Best-effort Lean rendering of an intermediate Coq statement (may be partial)."""
    try:
        s = stmt.strip()
        # `exists C, P` → `∃ C, <P>`  (keep the witness binder, translate the body)
        m = re.match(r"exists\s+(?P<v>[\w\s']+?)\s*,\s*(?P<body>.*)$", s, re.DOTALL)
        if m:
            return f"∃ {m.group('v').strip()}, " + gt.translate_type(m.group("body"))
        return gt.translate_type(s)
    except Exception:
        return f"<untranslated: {stmt.strip()}>"


def skeleton(coq_path: str, name: str):
    src = brief.extract_coq_lemma(coq_path, name)
    if not src:
        return None
    body = src.split("Proof.", 1)[1] if "Proof." in src else src
    body = re.split(r"\bQed\b|\bDefined\b", body)[0]

    steps = []
    # `assert (STMT)` or `assert (STMT) by (tac)` — capture STMT up to the closing
    # paren that precedes ` by` or ` .`  (non-greedy; good enough for Ch06 asserts).
    for m in re.finditer(r"assert\s*\(\s*(?P<stmt>.+?)\)\s*(?:by\b|\.)", body, re.DOTALL):
        stmt = re.sub(r"\s+", " ", m.group("stmt")).strip()
        kind = "NEW-POINT" if re.search(r"\bexists\b", stmt) else "HAVE"
        steps.append((kind, stmt, _translate(stmt)))

    lemmas = sorted(set(re.findall(r"(?:apply|eapply)\s+\(?(\w+)", body)))
    point_ops = sorted(set(re.findall(POINT_CREATORS, body)))
    return steps, lemmas, point_ops


def report(coq_path: str, name: str) -> None:
    res = skeleton(coq_path, name)
    if res is None:
        print(f"  {name}: (not found)")
        return
    steps, lemmas, point_ops = res
    npt = sum(1 for k, *_ in steps if k == "NEW-POINT")
    print(f"── {name}  ({len(steps)} intermediate stmt(s), {npt} new-point, "
          f"{len(lemmas)} justifying lemma(s)) ──")
    if point_ops:
        print(f"   point-creation ops (KEEP, per heuristic): {', '.join(point_ops)}")
    for kind, raw, lean in steps:
        tag = "◆ NEW-POINT" if kind == "NEW-POINT" else "• have     "
        print(f"   {tag}  {raw}")
        print(f"                 ⇢ Lean:  {lean}")
    if lemmas:
        print(f"   justification base needed: {', '.join(lemmas)}")
    print()


def main() -> None:
    ap = argparse.ArgumentParser(description="Extract a GeoCoq proof skeleton (Layer-3 oracle)")
    ap.add_argument("coq_file")
    ap.add_argument("lemma", nargs="?", help="lemma name (omit with --all)")
    ap.add_argument("--all", action="store_true", help="every lemma in the file")
    args = ap.parse_args()
    if args.all:
        with open(args.coq_file) as f:
            names = re.findall(r"^[ \t]*(?:Lemma|Theorem|Corollary|Proposition)[ \t]+(\w+)",
                               f.read(), re.M)
        for nm in names:
            report(args.coq_file, nm)
    elif args.lemma:
        report(args.coq_file, args.lemma)
    else:
        ap.error("give a lemma name or --all")


if __name__ == "__main__":
    main()
