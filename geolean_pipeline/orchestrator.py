"""
Orchestrator v0 — autonomous batch driver over one Coq file.

For each lemma:  oracle proof-term -> classify (linear vs case-split) ->
transliterate (port_map, cone-strict) -> emit into ONE output .lean ->
compile with `lake env lean` + `#print axioms` -> ledger.

Original files are NOT touched. Accepted lemmas are guaranteed cone-only
(strict), so a clean compile => axiom-clean. Everything else is queued with a
reason: unsupported (case-split / parse), blocked (non-cone dep), verify-failed.
"""
import os, sys
REPO=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO,"geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)
import re, subprocess
import translit as T
from src.oracle import run_proof, find_all_lemma_names, default_q_paths, _ensure_known_names

CASE=re.compile(r'\b(match|[A-Za-z_]+_(ind|rec|rect))\b')
LEAN_ROOT="lean/geocoq_translate"

def parse_stubs(lean_file):
    """{name: (header_tail_up_to_':=', [binder_names_in_order])} from a .lean file."""
    text=open(lean_file).read()
    text=re.sub(r'/-.*?-/','',text,flags=re.S); text=re.sub(r'--[^\n]*','',text)
    stubs={}
    for m in re.finditer(r'(?ms)^theorem\s+([A-Za-z0-9_\']+)\s*(.*?):=', text):
        name, tail=m.group(1), m.group(2).strip()
        names=[]
        for g in re.finditer(r'[\(\{\[]\s*([^:(){}\[\]]+?)\s*:', tail):
            names+=g.group(1).split()
        stubs[name]=(tail, names)
    return stubs

def transliterate_pt(pt, lean_binders):
    """Reuse translit machinery on an already-fetched proof term.
    Emits a term, or a `by` tactic block when the proof has case-splits."""
    ast=T.parse_term(T.P(T.tok(pt)), stop={None})
    while ast[0]=="paren": ast=ast[1]
    if ast[0]!="fun": raise ValueError(f"top not fun: {ast[0]}")
    subst={c:l for c,l in zip(ast[1], lean_binders)}
    notes=[]
    return T.emit_body(ast[2], subst, notes), notes

def run(coq_file, lean_file, out_module):
    _ensure_known_names()
    stubs=parse_stubs(lean_file)
    ledger={'accepted':[], 'unsupported':[], 'blocked':[], 'no_stub':[]}
    emitted=[]
    for name in find_all_lemma_names(coq_file):
        if name not in stubs: ledger['no_stub'].append(name); continue
        tail, binders=stubs[name]
        try: pt=run_proof(coq_file, name, default_q_paths())
        except Exception as e: ledger['unsupported'].append((name,f'oracle:{str(e)[:40]}')); continue
        try: body, notes=transliterate_pt(pt, binders)
        except Exception as e: ledger['unsupported'].append((name,f'parse:{str(e)[:40]}')); continue
        blk=[n for n in notes if 'UNRESOLVED' in n or 'NON-LEMMA' in n]
        if blk: ledger['blocked'].append((name, blk[0])); continue
        emitted.append((name, tail, body)); ledger['accepted'].append(name)
    out_path=write_output(out_module, emitted)
    return ledger, emitted, out_path

def write_output(out_module, emitted):
    path=os.path.join(LEAN_ROOT, "GeocoqTranslate/Tarski_dev", out_module+".lean")
    lines=["import GeocoqTranslate.Tarski_dev.Ch05Bet",       # top of cone: pulls Ch04Cong,
           "import GeocoqTranslate.Tarski_dev.Ch04Cong","",   # SegmentCone, CongBase, BetweenOutBase
           "namespace GeocoqTranslate.Tarski.Base",
           "open Tarski_neutral_dimensionless",
           "open Tarski_neutral_dimensionless_with_decidable_point_equality","",
           "variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]",""]
    for name, tail, body in emitted:
        if body.startswith("by\n"):
            lines.append(f"theorem {name}_ax {tail} := by")
            lines.append(body[3:])
        else:
            lines.append(f"theorem {name}_ax {tail} :=")
            lines.append(f"  {body}")
        lines.append("")
    for name,_,_ in emitted:
        lines.append(f"#print axioms GeocoqTranslate.Tarski.Base.{name}_ax")
    lines.append(""); lines.append("end GeocoqTranslate.Tarski.Base")
    open(path,"w").write("\n".join(lines))
    return path

def verify(out_path):
    r=subprocess.run(["lake","env","lean",out_path.replace(LEAN_ROOT+"/","")],
        cwd=LEAN_ROOT, capture_output=True, text=True, timeout=600)
    out=r.stdout+r.stderr
    clean=re.findall(r"'GeocoqTranslate\.Tarski\.Base\.(\w+)_ax' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out)
    errors=re.findall(r"\.lean:\d+:\d+: error:.*", out)
    return clean, errors, out

if __name__=="__main__":
    coq="theories/Main/Tarski_dev/Ch03_bet.v"
    lean=os.path.join(LEAN_ROOT,"GeocoqTranslate/Tarski_dev/Ch03_bet.lean")
    ledger, emitted, out_path=run(coq, lean, "OrchOutCh03")
    print("=== ORCHESTRATOR LEDGER (Ch03_bet.v) ===")
    print(f"accepted (transliterated) : {len(ledger['accepted'])}  {ledger['accepted']}")
    print(f"unsupported (case-split..): {len(ledger['unsupported'])}")
    for n,r in ledger['unsupported'][:6]: print(f"     - {n}: {r}")
    print(f"blocked (non-cone dep)    : {len(ledger['blocked'])}")
    for n,r in ledger['blocked'][:6]: print(f"     - {n}: {r}")
    print(f"no lean stub              : {len(ledger['no_stub'])}")
    print(f"\noutput file: {out_path}")
    print("=== VERIFY GATE (lake env lean + #print axioms) ===")
    clean, errors, out=verify(out_path)
    ok=[n for n,ax in clean if 'sorryAx' not in ax]
    dirty=[n for n,ax in clean if 'sorryAx' in ax]
    print(f"axiom-clean confirmed: {len(ok)}  {ok}")
    if dirty: print(f"sorryAx (bad)        : {dirty}")
    if errors:
        print(f"compile errors       : {len(errors)}")
        for e in errors[:6]: print("     ", e[:120])
