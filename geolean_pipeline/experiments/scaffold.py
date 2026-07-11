"""
Scaffold generator (LLM path). For a case-split lemma the transliterator can't
do, bundle everything an LLM needs to write the Lean proof:
  statement + Coq proof term + resolved calls + port_map (cone) signatures +
  Coq->Lean binder map. The LLM fills the proof; the SAME verify gate accepts
  it only if it compiles axiom-clean.
"""
import os, sys
REPO=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO,"geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)
import re
os.environ.setdefault("GEOCOQ_DIR","/Users/ayaansiddiqui/GeoCoq"); os.chdir("/Users/ayaansiddiqui/GeoCoq")
import translit as T
from src.oracle import run_proof, extract_lemma_source, find_all_lemma_names, default_q_paths, collect_geocoq_lemma_names
from src.port_map import get_lean_signature
from orchestrator import parse_stubs, CASE

CONE_FILES=T.CONE_FILES
ID=re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
PRIM={"not_eq_sym"}; AX=T.ALLOW_AXIOMS
KNOWN=collect_geocoq_lemma_names(os.path.join(os.getcwd(),"theories"))   # live known-lemma set

def cone_sig(name):
    ms=get_lean_signature(name)["matches"]
    cm=[m for m in ms if any(cf in m["file"] for cf in CONE_FILES)]
    if cm: return cm[0]["signature"]
    if name in PRIM: return "Ne.symm  (Coq not_eq_sym)"
    if name in AX: return f"{name}  (Tarski axiom / class field — in scope)"
    return None

def find_cone_only_casesplits(coq_file, lean_file):
    stubs=parse_stubs(lean_file); out=[]
    for name in find_all_lemma_names(coq_file):
        if name not in stubs: continue
        try: pt=run_proof(coq_file,name,default_q_paths())
        except Exception: continue
        if not CASE.search(pt): continue                 # want case-splits only
        names={t for t in ID.findall(pt) if t in KNOWN}
        if all(cone_sig(n) is not None for n in names):   # every dep clean-able
            out.append((name, sorted(names)))
    return out, stubs

def scaffold(coq_file, name, stubs):
    tail, binders=stubs[name]
    pt=run_proof(coq_file,name,default_q_paths())
    coq_src=extract_lemma_source(coq_file,name)
    ast=T.parse_term(T.P(T.tok(pt)), stop={None})
    while ast[0]=="paren": ast=ast[1]
    coqb=ast[1] if ast[0]=="fun" else []
    used=sorted({t for t in ID.findall(pt) if t in KNOWN})
    print(f"================ SCAFFOLD: {name} ================")
    print("LEAN STATEMENT:\n  theorem "+name+" "+tail+" := ...")
    print("\nCOQ SOURCE:\n"+coq_src)
    print("\nCOQ PROOF TERM:\n"+pt)
    print("\nCoq->Lean BINDER MAP:", dict(zip(coqb, binders)))
    print("\nPORT_MAP (cone Lean signatures of lemmas used):")
    for n in used:
        print(f"  {n}:  {cone_sig(n)}")

if __name__=="__main__":
    coq="theories/Main/Tarski_dev/Ch03_bet.v"
    lean="lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch03_bet.lean"
    cands, stubs=find_cone_only_casesplits(coq, lean)
    print("cone-only CASE-SPLIT candidates in Ch03_bet.v:", [c[0] for c in cands])
    # generate a scaffold for a small, illustrative one
    for pick in ["Bet_cases","between_exchange3","between_symmetry","l3_9_1"]:
        if any(c[0]==pick for c in cands):
            print(); scaffold(coq, pick, stubs); break
