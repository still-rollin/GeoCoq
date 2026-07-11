"""
Ground-truth signature index for the canonical Tarski_dev Lean chain.

Problem this solves: `mcp__geolean-oracle__get_lean_signature` searches ALL
`.lean` files under `Tarski_dev/`, including stale non-authoritative scaffold
duplicates (e.g. `Ch09_plane.lean`, `Ch07_midpoint.lean`) that sit right next
to the real, canonical files and are NOT part of the active import chain.
Wrong-argument-order bugs from trusting one of those (or from re-deriving a
signature by memory/grep) were the single largest source of wasted
fix-iterations in manual proof reconstruction sessions.

This script parses ONLY the files reachable by following `import` statements
transitively from the final chapter (`Ch10`), i.e. exactly the files whose
declarations a proof written in that chain can actually call. It extracts the
full signature (everything from `theorem`/`lemma` up to the top-level `:=`)
for every declaration, plus whether its body is a literal `sorry` (so a caller
knows the signature is real but the fact isn't yet proven).

Usage:
    python geolean_pipeline/signature_index.py            # regenerate the JSON
    python geolean_pipeline/signature_index.py NAME [...]  # look up one/more names

Output: geolean_pipeline/signature_index.json
    {
      "two_sides_dec_c": {
        "file": "Ch09.lean",
        "line": 1931,
        "sorry": false,
        "signature": "theorem two_sides_dec_c (A B C D : Tpoint) :\n    TS A B C D ∨ ¬ TS A B C D"
      },
      ...
    }

Regenerate this after every edit that adds/removes/renames a declaration in
the canonical chain — it is a static snapshot, not live-queried. Cheap enough
(~1s over the whole chain) to run before every agent dispatch.
"""
import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_ROOT = os.path.join(REPO, "lean", "geocoq_translate", "GeocoqTranslate")
OUT_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "signature_index.json")

ENTRY_CHAPTER = "GeocoqTranslate.Tarski_dev.Ch10"  # the final chapter; imports the whole chain

IMPORT_RE = re.compile(r"^import\s+(GeocoqTranslate\.[A-Za-z0-9_.]+)\s*$", re.MULTILINE)
# top-level `theorem`/`lemma` declarations only (column 0 — excludes anything
# nested inside a proof body, a `section`, or a comment block)
DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!]*)", re.MULTILINE)


def module_to_path(mod: str) -> str:
    """`GeocoqTranslate.Tarski_dev.Ch10` -> absolute path of Ch10.lean"""
    parts = mod.split(".")
    assert parts[0] == "GeocoqTranslate"
    return os.path.join(LEAN_ROOT, *parts[1:]) + ".lean"


def transitive_imports(entry_mod: str) -> list[str]:
    """BFS over `import` statements starting from entry_mod. Returns module
    names in an order where each module appears after all its dependencies
    (topological-ish via visit order; exact order doesn't matter here since
    we only need the *set* of reachable files)."""
    seen: set[str] = set()
    order: list[str] = []
    stack = [entry_mod]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_to_path(mod)
        if not os.path.isfile(path):
            continue
        order.append(mod)
        src = open(path, encoding="utf-8").read()
        for m in IMPORT_RE.finditer(src):
            dep = m.group(1)
            if dep not in seen:
                stack.append(dep)
    return order


def find_decl_end(src: str, start: int) -> int:
    """Given the index of the `theorem`/`lemma` keyword, scan forward
    tracking bracket depth and return the index of the top-level `:=` that
    terminates the signature (the point where all binders have closed and the
    return type is complete). Binder types can themselves contain `:=`
    (default values) but only inside brackets, so depth-0 `:=` is unambiguous."""
    depth = 0
    i = start
    n = len(src)
    while i < n:
        c = src[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and src[i:i + 2] == ":=":
            return i
        i += 1
    return n  # malformed / no body found — take the rest (shouldn't happen)


def parse_file(path: str, rel_name: str) -> dict:
    src = open(path, encoding="utf-8").read()
    out = {}
    for m in DECL_RE.finditer(src):
        name = m.group(2)
        start = m.start()
        end = find_decl_end(src, start)
        signature = src[start:end].rstrip()
        # strip trailing colon-less whitespace artifacts, normalize
        line_no = src.count("\n", 0, start) + 1
        body_start = end + 2  # skip ":="
        body_tail = src[body_start:body_start + 40].strip()
        is_sorry = body_tail.split()[:1] == ["sorry"] if body_tail else False
        out[name] = {
            "file": rel_name,
            "line": line_no,
            "sorry": is_sorry,
            "signature": signature,
        }
    return out


def build_index() -> dict:
    modules = transitive_imports(ENTRY_CHAPTER)
    index = {}
    files_scanned = []
    for mod in modules:
        path = module_to_path(mod)
        rel_name = os.path.relpath(path, LEAN_ROOT)
        files_scanned.append(rel_name)
        decls = parse_file(path, rel_name)
        for name, entry in decls.items():
            if name in index:
                # a name defined in two canonical files is a real ambiguity —
                # keep both file locations visible rather than silently
                # picking one
                prev = index[name]
                if not isinstance(prev, list):
                    index[name] = [prev]
                index[name].append(entry)
            else:
                index[name] = entry
    return index, files_scanned


def main():
    index, files_scanned = build_index()
    with open(OUT_PATH, "w", encoding="utf-8") as f:
        json.dump(index, f, indent=2, ensure_ascii=False, sort_keys=True)
    n_sorry = sum(1 for e in index.values() if isinstance(e, dict) and e["sorry"])
    print(f"Indexed {len(index)} declarations across {len(files_scanned)} canonical files "
          f"({n_sorry} still `sorry`).")
    print(f"Wrote {OUT_PATH}")
    dupes = {k: v for k, v in index.items() if isinstance(v, list)}
    if dupes:
        print(f"WARNING: {len(dupes)} name(s) declared in more than one canonical file:")
        for k in dupes:
            print(f"  - {k}")


def lookup(names: list[str]):
    with open(OUT_PATH, encoding="utf-8") as f:
        index = json.load(f)
    for name in names:
        entry = index.get(name)
        if entry is None:
            print(f"{name}: NOT FOUND in canonical index")
            continue
        entries = entry if isinstance(entry, list) else [entry]
        for e in entries:
            tag = " [SORRY]" if e["sorry"] else ""
            print(f"# {name}  ({e['file']}:{e['line']}){tag}")
            print(e["signature"])
            print()


if __name__ == "__main__":
    if len(sys.argv) > 1:
        lookup(sys.argv[1:])
    else:
        main()
