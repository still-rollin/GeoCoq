"""
port_map — the Lean-side half of the translation oracle.

Given a GeoCoq (Coq) lemma name, return the ported Lean lemma(s): name,
file:line, and the verbatim Lean signature (binders + `: type`). The
translator uses this to emit `exact`/`apply` with the correct Lean argument
shape — implicit `{}` vs instance `[]` vs explicit `()` and the right order —
instead of blindly copying Coq's positional args (the #1 translation error).

Where the Coq-side oracle (`oracle.py`) answers *"what did Coq do"*, this
answers *"what does Lean have"*. Together they make a call-node mechanical.

Data source: the ported Lean corpus (`*.lean` text). NO Coq / sertop / build
dependency — this module imports nothing from `oracle.py`, so it keeps working
even when the Coq toolchain is broken.
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass


@dataclass
class PortedLemma:
    """One ported Lean declaration matching a queried name."""
    name: str          # Lean name (== the Coq name; the port keeps names verbatim)
    file: str          # absolute path of the .lean file
    line: int          # 1-indexed line of the declaration
    signature: str     # verbatim header: `theorem NAME <binders> : <type>`


# ---------------------------------------------------------------------------
# Lean source scanning
# ---------------------------------------------------------------------------

def _blank_comments(text: str) -> str:
    """Replace comment characters with spaces, PRESERVING every offset (and
    thus line numbers). Handles block `/- ... -/` and line `-- ...` comments."""
    text = re.sub(
        r"/-.*?-/",
        lambda m: re.sub(r"[^\n]", " ", m.group(0)),
        text,
        flags=re.DOTALL,
    )
    text = re.sub(r"--[^\n]*", lambda m: " " * len(m.group(0)), text)
    return text


# A declaration header: optional attribute + modifiers, then the keyword, the
# name, then everything (binders + `: type`) up to the body separator `:=`
# (or `where`). `(?!:=)` lets the type contain lone `:` and `=` (e.g. `C = D`)
# without stopping early; DOTALL lets a signature span multiple lines.
_DECL_RE = re.compile(
    r"(?ms)^[ \t]*"
    r"(?:@\[[^\]]*\][ \t]*)?"                                   # @[simp] etc.
    r"(?:(?:private|protected|noncomputable|scoped|local)[ \t]+)*"
    r"(theorem|lemma|def|instance|abbrev)[ \t]+"               # (1) kind
    r"([A-Za-z_][A-Za-z0-9_'.]*)"                              # (2) name
    r"((?:(?!:=|\bwhere\b).)*?)"                               # (3) binders + `: type`
    r"(?::=|\bwhere\b)"                                        # body separator
)


def _iter_lean_files(root: str):
    for dirpath, _dirs, files in os.walk(root):
        for fn in files:
            if fn.endswith(".lean"):
                yield os.path.join(dirpath, fn)


def build_index(root: str) -> dict[str, list[PortedLemma]]:
    """Scan every `.lean` file under `root`, indexing declarations by name.

    A name maps to a *list* because the same lemma can be ported in more than
    one file with different binder styles (e.g. `between_symmetry` exists with
    explicit `()` binders and with implicit `{}` binders) — the caller
    disambiguates by file.
    """
    index: dict[str, list[PortedLemma]] = {}
    for path in _iter_lean_files(root):
        try:
            with open(path) as f:
                raw = f.read()
        except OSError:
            continue
        text = _blank_comments(raw)
        for m in _DECL_RE.finditer(text):
            kind, name, mid = m.group(1), m.group(2), m.group(3)
            signature = re.sub(r"\s+", " ", f"{kind} {name}{mid}").strip()
            line = text[: m.start(2)].count("\n") + 1
            index.setdefault(name, []).append(
                PortedLemma(name=name, file=path, line=line, signature=signature)
            )
    return index


# ---------------------------------------------------------------------------
# Cached lookup
# ---------------------------------------------------------------------------

_CACHE: dict[str, dict[str, list[PortedLemma]]] = {}


def get_index(root: str) -> dict[str, list[PortedLemma]]:
    if root not in _CACHE:
        _CACHE[root] = build_index(root)
    return _CACHE[root]


def default_lean_root() -> str:
    """Where the ported Lean corpus lives. `$GEOLEAN_LEAN_ROOT` wins; else
    derive from `$GEOCOQ_DIR` (already set for the MCP server); else cwd."""
    root = os.environ.get("GEOLEAN_LEAN_ROOT")
    if root:
        return root
    geocoq = os.environ.get("GEOCOQ_DIR") or os.getcwd()
    return os.path.join(geocoq, "lean/geocoq_translate/GeocoqTranslate")


def lookup(coq_name: str, root: str | None = None) -> list[PortedLemma]:
    """All ported Lean declarations whose name equals `coq_name` (verbatim)."""
    return get_index(root or default_lean_root()).get(coq_name, [])


def get_lean_signature(coq_name: str, root: str | None = None) -> dict:
    """MCP-facing result: `{coq_name, ported, matches:[{lean_name,file,line,signature}]}`."""
    hits = lookup(coq_name, root)
    return {
        "coq_name": coq_name,
        "ported": bool(hits),
        "matches": [
            {"lean_name": h.name, "file": h.file, "line": h.line, "signature": h.signature}
            for h in hits
        ],
    }
