"""
Transliterator v0 — oracle proof-term + port_map -> Lean `exact` body.

Scope: proofs whose term is a `fun … => <application/let tree>` (no match).
Demonstrates the deterministic core: parse Coq's Show-Proof term, remap
hypothesis names, map primitives, and — using port_map — pick the right Lean
lemma variant (by explicit-arg count) and drop implicit args. Zero LLM.
"""
import os, sys
REPO=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO,"geolean_oracle"))
os.environ.setdefault("GEOCOQ_DIR", REPO)
os.chdir(REPO)
import re
from src.oracle import run_proof, default_q_paths, collect_geocoq_lemma_names
from src.port_map import get_lean_signature

# The set of real GeoCoq lemma names. A head that ISN'T one of these (and isn't a
# special form / primitive) is a LOCAL hypothesis applied as a function (H, H0,
# HC', x…), not a missing lemma — so emit it verbatim instead of flagging it.
try:
    KNOWN_LEMMAS = collect_geocoq_lemma_names(os.path.join(os.getcwd(), "theories"))
except Exception:
    KNOWN_LEMMAS = set()

# --------------------------------------------------------------------------
# 1. Tokenize + parse the Gallina subset (fun / let / app / atom)
# --------------------------------------------------------------------------
_TOK = re.compile(r"""[A-Za-z_][A-Za-z0-9_'.]*|:=|=>|<>|/\\|\\/|~|[()]|:|\S""", re.X)

def tok(s): return _TOK.findall(s)

class P:
    def __init__(self, toks): self.t=toks; self.i=0
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        v=self.peek()
        if x is not None and v!=x: raise SyntaxError(f"want {x!r} got {v!r} at {self.i}")
        self.i+=1; return v

# AST nodes as tuples: ('fun',[binders],body) ('let',name,val,body)
#                      ('app',head,[args]) ('var',name) ('paren',term)

def parse_term(p, stop):
    if p.peek()=="fun": return parse_fun(p)
    if p.peek()=="let": return parse_let(p, stop)
    if p.peek()=="match": return parse_match(p, stop)
    if p.peek()=="fix" or p.peek()=="cofix": return parse_fix(p, stop)
    return parse_app(p, stop)

def _skip_type_to(p, stops, opens="([{", closes=")]}"):
    depth=0
    while p.peek() is not None:
        v=p.peek()
        if depth==0 and v in stops: return
        if v in opens: depth+=1
        elif v in closes: depth-=1
        p.eat()

def parse_fun(p):
    p.eat("fun"); binders=[]
    while p.peek()!="=>":
        if p.peek()=="(":
            p.eat("(")
            names=[]
            while p.peek() not in (":", ")"):
                names.append(p.eat())
            if p.peek()==":":
                p.eat(":"); _skip_type_to(p, {")"})
            p.eat(")"); binders+=names
        elif p.peek()==":":                 # un-parenthesized `fun x : T => …`
            p.eat(":"); _skip_type_to(p, {"=>"})
        else:
            binders.append(p.eat())
    p.eat("=>")
    body=parse_term(p, stop={None, ")"})
    return ("fun", binders, body)

def parse_let(p, stop):
    p.eat("let"); name=p.eat()
    if p.peek()==":":
        p.eat(":"); _skip_type_to(p, {":="})
    p.eat(":=")
    val=parse_term(p, stop={"in"})
    if p.peek()==":":                 # value-level cast: `:= t : T in …` (Show Proof cast printing)
        p.eat(":"); _skip_type_to(p, {"in"})
    p.eat("in")
    body=parse_term(p, stop)
    return ("let", name, val, body)

def parse_match(p, stop):
    """`match S [as x] [in T] [return T] with | ctor v.. => body .. end`."""
    p.eat("match")
    scrut=parse_app(p, stop={"with","as","in","return","end"})
    while p.peek() not in ("with", None):          # skip as/in/return clauses
        p.eat()
    p.eat("with")
    if p.peek()=="|": p.eat("|")
    branches=[]
    while p.peek() not in ("end", None):
        pat=[]
        while p.peek() not in ("=>", None):
            pat.append(p.eat())
        p.eat("=>")
        body=parse_term(p, stop={"|","end"})
        branches.append((pat[0] if pat else "_", pat[1:], body))   # (ctor, [vars], body)
        if p.peek()=="|": p.eat("|")
    p.eat("end")
    return ("match", scrut, branches)

def parse_fix(p, stop):
    """`fix`/`cofix` has no delimiter — consume the whole expression (tracking
    paren depth) and mark it unsupported so the lemma becomes a clean hole."""
    p.eat()                                         # 'fix' / 'cofix'
    depth=0
    while p.peek() is not None:
        v=p.peek()
        if depth==0 and (v in stop or v in (")","]","}","in","end","|")): break
        if v in "([{": depth+=1
        elif v in ")]}": depth-=1
        p.eat()
    return ("unsupported","fix")

_NONATOM={")","in","=>",":=",":",None}
def parse_app(p, stop):
    head=parse_atom(p)
    args=[]
    while p.peek() not in _NONATOM and p.peek() not in stop:
        args.append(parse_atom(p))
    return ("app", head, args) if args else head

def parse_atom(p):
    if p.peek()=="(":
        p.eat("("); t=parse_term(p, stop={")"})
        if p.peek()==":":                    # type ascription `(e : T)` — keep term, drop annotation
            p.eat(":"); _skip_type_to(p, {")"})
        p.eat(")")
        return ("paren", t)
    if p.peek()=="match": return parse_match(p, stop={")","in","end","|"})
    if p.peek() in ("fix","cofix"): return parse_fix(p, stop={")","in","end","|"})
    return ("var", p.eat())

# --------------------------------------------------------------------------
# 2. Parse a Lean signature into ordered binder groups (explicit/implicit)
# --------------------------------------------------------------------------
def _binder_groups(rest, stop_chars):
    """Scan leading `(...)`/`{...}`/`[...]` binder groups, one 'E'/'I' per
    name inside. Stops at the first char in `stop_chars` seen outside a
    group. Returns (kinds, index_just_past_the_last_group)."""
    kinds=[]; i=0; n=len(rest)
    while i<n and rest[i] in "({[":
        c=rest[i]
        close={"(":")","{":"}","[":"]"}[c]
        j=i+1; depth=1
        while j<n and depth>0:
            if rest[j]==c: depth+=1
            elif rest[j]==close: depth-=1
            j+=1
        inner=rest[i+1:j-1]
        names=inner.split(":")[0].split()
        k = "E" if c=="(" else "I"
        kinds+= [k]*len(names)
        i=j
        while i<n and rest[i] in " \t\n": i+=1
    return kinds, i


def lean_binder_kinds(sig):
    """Return list of 'E'/'I' per binder, in order, up to the conclusion.
    Handles TWO signature shapes:
    (a) Ch02-10 style: `theorem NAME (A B : T) (h : P) : Result` -- binders
        as parenthesized groups directly in the signature, before a final
        bare ':'.
    (b) Ch11+ style (climb_upper.py / gen_stubs.py stubs): `theorem NAME :
        forall (A B : T), P1 -> P2 -> Result` -- the whole Pi-type as one
        Coq-translated expression after a bare ':', named binders in a
        leading `forall (...)` group, then UNNAMED hypotheses chained by
        '->' -- each of those arrows is still one explicit positional arg,
        even though the text has no '(h : P)' group for it."""
    m=re.match(r"\s*(?:theorem|lemma|def|instance|abbrev)\s+\S+\s*(.*)$", sig, re.S)
    rest=m.group(1) if m else sig
    stripped=rest.lstrip()
    m2=re.match(r":\s*(?:∀|forall)\s*", stripped)
    if m2:                                    # style (b)
        rest=stripped[m2.end():]
        kinds, i = _binder_groups(rest, stop_chars=",")
        n=len(rest)
        if i<n and rest[i]==",":
            i+=1
        depth=0
        while i<n:
            c=rest[i]
            if c in "([{": depth+=1; i+=1
            elif c in ")]}": depth-=1; i+=1
            elif depth==0 and rest[i:i+2]=="->":
                kinds.append("E"); i+=2
            elif depth==0 and c=="→":
                kinds.append("E"); i+=1
            else:
                i+=1
        return kinds
    # style (a)
    kinds=[]; i=0; n=len(rest)
    while i<n:
        c=rest[i]
        if c in "({[":
            close={"(":")","{":"}","[":"]"}[c]
            j=i+1; depth=1
            while j<n and depth>0:
                if rest[j]==c: depth+=1
                elif rest[j]==close: depth-=1
                j+=1
            inner=rest[i+1:j-1]
            names=inner.split(":")[0].split()
            k = "E" if c=="(" else "I"
            kinds+= [k]*len(names)
            i=j
        elif c==":":
            break   # conclusion
        else:
            i+=1
    return kinds

# --------------------------------------------------------------------------
# 3. Emit Lean from the AST
# --------------------------------------------------------------------------
PRIM={"not_eq_sym":("Ne.symm",1),
      "eq_sym":("Eq.symm",1), "eq_trans":("Eq.trans",2), "eq_refl":("rfl",0)}

# The proven, axiom-clean cone (implicit-signature). Preferring these makes the
# emitter target the clean base AND exercises implicit-arg dropping.
CONE_FILES=["CongBase.lean","BetweenOutBase.lean","SegmentCone.lean","Ch04Cong.lean","Ch05Bet.lean"]

# Tarski class fields / primitives that are clean (no port needed) — emitted
# verbatim; the kernel gate catches any arg-shape mismatch.
ALLOW_AXIOMS={"segment_construction","cong_identity","five_segment",
    "cong_pseudo_reflexivity","cong_inner_transitivity","between_identity",
    "inner_pasch","lower_dim","point_equality_decidability"}

# Coq name -> Lean name where they differ (class fields renamed in the port).
NAME_MAP={"eq_dec_points":"point_equality_decidability"}

# Col/Cong permutation-and-transitivity closure family: Coq's tactic automation
# (ColR/Col5/auto with col, CongR-equivalent) expands to a ground, instance-specific
# chain of calls into exactly this vocabulary (confirmed by inspection this session
# -- see docs/session_progress.md Item 11 addendum). Rather than resolve each call by
# name (needs col_permutation_N/coplanar_perm_N ported one at a time, an unbounded
# tail), swap the WHOLE subterm for the already-verified reflective tactic -- it
# re-derives the same Col/Cong fact from whatever's in the local context, so the
# call's own (possibly still-unresolved) arguments never need to be transliterated.
# Positive Col goals only -- `colr` does not handle negated `¬ Col _ _ _` goals
# (confirmed empirically), so `not_col_permutation_*` is deliberately excluded.
COL_FAMILY={"col_permutation_1","col_permutation_2","col_permutation_3",
    "col_permutation_4","col_permutation_5",
    "col_trivial_1","col_trivial_2","col_trivial_3",
    "col_transitivity_1","col_transitivity_2","l6_16_1","colx",
    # ColR's own internal reflective machinery (ColR.v: collect_diffs/collect_cols
    # build up the SS/SP witness sets, test_col_ok consumes them) -- these leak into
    # Show Proof verbatim whenever a proof used `ColR` for a non-trivial derivation
    # (not just a named permutation lemma). Same rationale as the rest of COL_FAMILY:
    # whatever Col fact this subterm proves, `colr` re-derives it from context, args unneeded.
    "collect_diffs","collect_cols","ss_ok_empty","sp_ok_empty","test_col_ok"}
CONG_FAMILY={"cong_reflexivity","cong_symmetry","cong_transitivity",
    "cong_left_commutativity","cong_right_commutativity","cong_commutativity"}

# Coq eliminators / recursors / stdlib globals that are NOT local hypotheses and
# that we don't (yet) emit. If one reaches the app-head fallback it must be FLAGGED
# (-> hole), never emitted verbatim as a local hyp — else it and its Prop motive
# (`~`, `<>`, `->`) leak invalid tokens into the Lean and break parsing.
COQ_NONLOCAL={
    "eq_ind","eq_ind_r","eq_rect","eq_rec","eq_rec_r","eq_sind","eq_rect_r",
    "False_ind","False_rect","False_rec","True_ind","True_rect",
    "and_ind","and_rec","and_rect","or_ind","or_rec","or_rect",
    "ex_ind","ex_rec","ex_rect","ex_intro","sig_ind","sig_rec","sig_rect",
    "sumbool_ind","sumbool_rec","sumbool_rect","sumor_rec","sum_rec","sum_rect",
    "nat_ind","nat_rec","nat_rect","list_ind","list_rec","bool_ind","bool_rec",
    "prod_rec","prod_rect","proj1","proj2","proj1_sig","proj2_sig",
    "f_equal","f_equal2","f_equal3","conj","or_introl","or_intror",
}

# Growing pool of same-chapter lemmas (the "climb"): name -> binder kinds. When a
# dep isn't in the cone but IS a lemma emitted earlier in this chapter, reference
# it as `<name>_c` (the suffix used by the climb engine's output).
LOCAL_SIGS={}

def choose_variant(name, ncoq, prefer_cone=True):
    """port_map -> pick the Lean variant. With prefer_cone, restrict STRICTLY to
    the proven cone files; else fall back to the same-chapter pool (LOCAL_SIGS);
    else return None so the dep is flagged (blocked), never silently emitted
    against a possibly-`sorry` transpiler lemma. Returns (lean_name, kinds) or None."""
    matches=get_lean_signature(name)["matches"]
    if prefer_cone:
        cone_m=[m for m in matches if any(cf in m["file"] for cf in CONE_FILES)]
        if not cone_m:
            if name in LOCAL_SIGS:
                return (name+"_c", LOCAL_SIGS[name])   # grow-pool: same-chapter lemma
            return None          # strict: no clean cone / local variant -> block
        matches=cone_m
    best=None
    for m in matches:
        kinds=lean_binder_kinds(m["signature"])
        nexp=kinds.count("E")
        score=(nexp==ncoq, nexp if nexp<=ncoq else -1)
        if best is None or score>best[0]:
            best=(score, m["lean_name"], kinds)
    return (best[1], best[2]) if best else None

BARE={"eq_refl":"rfl"}       # Coq constants with a Lean name when they appear UN-applied

def emit(node, subst, notes):
    k=node[0]
    if k=="var":
        if node[1] in subst: return subst[node[1]]
        return BARE.get(node[1], node[1])
    if k=="paren":
        return "(" + emit(node[1], subst, notes) + ")"
    if k=="let":
        _,name,val,body=node
        return f"(let {name} := {emit(val,subst,notes)}; {emit(body,subst,notes)})"
    if k=="fun":                                     # S2: lambda in term position
        _,bs,bd=node                                 # e.g. negation proof `fun H0 => H (…)`
        ns=dict(subst)
        for b in bs: ns.pop(b, None)                 # inner binder shadows any outer name
        return "fun " + " ".join(bs) + " => " + emit(bd, ns, notes)
    if k=="unsupported":                             # fix/cofix etc. -> flag (-> hole)
        notes.append(f"UNRESOLVED: unsupported construct '{node[1]}'")
        return "sorry"
    if k=="match":                                   # match in TERM position (e.g. nested inside a
        return "(by\n" + "\n".join(emit_match(node,subst,notes,1)) + ")"  # let-val) -> nested tactic block
    if k=="app":
        head=node[1]; args=node[2]
        if head[0]=="var":
            f=head[1]
            if f in TACTIC_HEADS:               # elim reached in term position (e.g. inside a
                return "(by\n" + "\n".join(emit_tactic(node,subst,notes,1)) + ")"  # let-val or conj arg) -> nested tactic block
            if f=="conj" and len(args)>=2:      # And.intro -> anonymous constructor
                return "⟨" + ", ".join(emit(a,subst,notes) for a in args) + "⟩"
            if f=="ex_intro" and len(args)>=3:  # ex_intro P witness proof -> ⟨witness, proof⟩
                return "⟨" + emit(args[1],subst,notes) + ", " + emit(args[2],subst,notes) + "⟩"
            if f in ("or_introl","or_intror") and args:  # Or.inl / Or.inr (proof is last arg)
                lean="Or.inl" if f=="or_introl" else "Or.inr"
                return lean + " " + emit(args[-1],subst,notes)
            if f in ("False_ind","False_rect","False_rec") and len(args)>=2:  # anything from False
                core="(" + emit(args[1],subst,notes) + ").elim"               # False_ind P h -> h.elim
                rest=args[2:]
                return core + (" " + " ".join(emit(a,subst,notes) for a in rest) if rest else "")
            if f in ("proj1","proj2") and args:          # And-projection: proj1 … H -> (H).1
                return "(" + emit(args[-1],subst,notes) + ")." + ("1" if f=="proj1" else "2")
            if f in COL_FAMILY:                 # Col/Cong closure family -> the reflective
                return "(by colr)"              # tactic re-derives it from context; args unneeded
            if f in CONG_FAMILY:
                return "(by cong_r)"
            if f in PRIM:                       # S3: drop leading implicit args by arity
                lean,k=PRIM[f]
                kept = args[-k:] if (k and len(args)>=k) else ([] if k==0 else args)
                return lean + (" " + " ".join(emit(a,subst,notes) for a in kept) if kept else "")
            if f in NAME_MAP:                    # Coq name -> different Lean name (class field)
                g=NAME_MAP[f]
                return g + (" " + " ".join(emit(a,subst,notes) for a in args) if args else "")
            if f in ALLOW_AXIOMS:                # clean Tarski primitive, emit verbatim
                return f + (" " + " ".join(emit(a,subst,notes) for a in args) if args else "")
            var=choose_variant(f, len(args))
            if var:
                lean, kinds=var
                # keep args at explicit positions; if fewer kinds than args,
                # assume leading extras are implicit points -> drop them.
                if len(kinds)==len(args):
                    kept=[a for a,kd in zip(args,kinds) if kd=="E"]
                else:
                    nexp=kinds.count("E")
                    kept=args[len(args)-nexp:] if nexp<=len(args) else args
                if len(kept)!=len(args):
                    notes.append(f"{f}->{lean}: dropped {len(args)-len(kept)} implicit arg(s)")
                return lean + (" " + " ".join(emit(a,subst,notes) for a in kept) if kept else "")
            if f in KNOWN_LEMMAS or f in COQ_NONLOCAL:   # real lemma OR Coq builtin we don't emit -> flag (-> hole)
                notes.append(f"UNRESOLVED head: {f} (not ported / unknown)")
                return f + " " + " ".join(emit(a,subst,notes) for a in args)
            # not a lemma / builtin -> a local hypothesis / bound var applied as a function
            return subst.get(f, f) + (" " + " ".join(emit(a,subst,notes) for a in args) if args else "")
        h=_unparen(head)                             # (fun x.. => body) a b.. -> beta-reduce in place
        if h[0]=="fun":
            n=min(len(args), len(h[1]))              # under- OR over-applied lambda: consume what
            ns=dict(subst)                            # we can, then handle leftover binders/args
            for b,a in zip(h[1][:n], args[:n]): ns[b]=emit(a,subst,notes)
            core=emit(h[2], ns, notes)
            rem_binders=h[1][n:]; rem_args=args[n:]
            if rem_binders:
                return "fun " + " ".join(rem_binders) + " => " + core
            if rem_args:
                return "(" + core + ") " + " ".join(emit(a,subst,notes) for a in rem_args)
            return core
        # other non-var, non-fun head (let/match/app etc.) -> emit the head as a term and
        # apply the remaining args after; Lean accepts applying a let/match value directly.
        return "(" + emit(head, subst, notes) + ")" + (
            " " + " ".join(emit(a,subst,notes) for a in args) if args else "")
    notes.append(f"UNRESOLVED: unhandled node '{k}'")     # totality: emit never throws
    return "sorry"

# --------------------------------------------------------------------------
# 3b. Tactic-mode emitter — case-splits (ex_ind/and_ind/or_ind) -> obtain/rcases
# --------------------------------------------------------------------------
ELIMS={"ex_ind","and_ind","or_ind"}
TACTIC_HEADS=ELIMS|{"eq_ind_r","eq_ind"}  # any of these -> emit a `by` tactic block

def _unparen(n):
    while n[0]=="paren": n=n[1]
    return n

def contains_elim(node):
    node=_unparen(node)
    if node[0] in ("match","unsupported"): return True
    if node[0]=="app":
        h=node[1]
        if h[0]=="var" and h[1] in TACTIC_HEADS: return True
        return contains_elim(h) or any(contains_elim(a) for a in node[2])
    if node[0]=="let": return contains_elim(node[2]) or contains_elim(node[3])
    if node[0]=="fun": return contains_elim(node[2])
    return False

def emit_tactic(node, subst, notes, ind=1):
    """Return a list of Lean tactic lines for a term with case-splits."""
    pad="  "*ind
    node=_unparen(node)
    if node[0]=="unsupported":                           # fix/cofix -> flag (-> hole)
        notes.append(f"UNRESOLVED: unsupported construct '{node[1]}'")
        return [f"{pad}exact sorry"]
    if node[0]=="match":                                 # S7: match -> obtain / rcases
        return emit_match(node, subst, notes, ind)
    if node[0]=="fun":                                   # lambda in tactic position -> `intro` its binders
        ns=dict(subst)                                   # (lets a case-split UNDER a lambda be reached, e.g.
        for b in node[1]: ns.pop(b, None)                #  the `fun H => match H …` body of an eq_ind rewrite)
        return [f"{pad}intro {' '.join(node[1])}"] + emit_tactic(node[2], ns, notes, ind)
    if node[0]=="let":                                   # let H := e in body -> have H := e
        _,name,val,body=node
        return [f"{pad}have {name} := {emit(val,subst,notes)}"] + emit_tactic(body,subst,notes,ind)
    if node[0]=="app" and _unparen(node[1])[0]=="fun" and 1<=len(node[2])<=len(_unparen(node[1])[1]):
        fn=_unparen(node[1]); args=node[2]                # beta-redex (fun x y.. => body) a b.. (N args)
        if len(args)==len(fn[1]):
            ns=dict(subst)
            for b,a in zip(fn[1], args): ns[b]=emit(a,subst,notes)
            return emit_tactic(fn[2],ns,notes,ind)
    if node[0]=="app" and node[1][0]=="var" and node[1][1]=="eq_ind_r" and len(node[2])>=3:
        args=node[2]                                      # [motive(type,skip), proof, eq, *rest]
        eq_s=emit(args[2],subst,notes)                    # the equality hyp, e.g. `H5 : C = x`
        prf=_unparen(args[1]); rest=args[3:]              # proof `fun b… => CORE` applied to *rest
        ns=dict(subst)
        if prf[0]=="fun":
            for b,a in zip(prf[1], rest): ns[b]=emit(a,subst,notes)   # beta: binders -> rest args
            body=prf[2]
        else:
            body=prf
        return [f"{pad}subst {eq_s}"] + emit_tactic(body,ns,notes,ind)
    if node[0]=="app" and node[1][0]=="var" and node[1][1]=="eq_ind" and len(node[2])>=5:
        args=node[2]                                      # [x, motive, px, y, eq, *rest] (forward rewrite)
        eq_s=emit(args[4],subst,notes)                    # the equality hyp `x = y`
        prf=_unparen(args[2]); rest=args[5:]              # proof px, applied to *rest
        ns=dict(subst)
        if prf[0]=="fun":
            for b,a in zip(prf[1], rest): ns[b]=emit(a,subst,notes)
            body=prf[2]
        else:
            body=prf
        return [f"{pad}subst {eq_s}"] + emit_tactic(body,ns,notes,ind)
    if node[0]=="app" and node[1][0]=="var" and node[1][1] in ELIMS:
        f=node[1][1]; args=node[2]; scrut=emit(args[-1],subst,notes)
        if f in ("ex_ind","and_ind"):
            fn=_unparen(args[0])
            if fn[0]=="fun":
                names=", ".join(fn[1])
                return [f"{pad}obtain ⟨{names}⟩ := {scrut}"] + emit_tactic(fn[2],subst,notes,ind)
        if f=="or_ind":
            f1,f2=_unparen(args[0]),_unparen(args[1])
            h1=f1[1][0] if f1[0]=="fun" else "h"
            h2=f2[1][0] if f2[0]=="fun" else "h"
            b1=f1[2] if f1[0]=="fun" else f1
            b2=f2[2] if f2[0]=="fun" else f2
            out=[f"{pad}rcases {scrut} with {h1} | {h2}"]
            out+=_branch(b1,subst,notes,ind)
            out+=_branch(b2,subst,notes,ind)
            return out
    return [f"{pad}exact {emit(node,subst,notes)}"]        # terminal

def _branch(body, subst, notes, ind):
    """Render one rcases branch under a `·`, indented past it."""
    inner=emit_tactic(body,subst,notes,ind+1)
    pad="  "*ind
    first=inner[0].lstrip()
    return [f"{pad}· {first}"] + inner[1:]

def emit_match(node, subst, notes, ind):
    """S7: `match S with |ctor v..=> body..` -> obtain (1 branch) / rcases (many).
    Mirrors the and_ind/or_ind/ex_ind handling — match is just their syntax form."""
    pad="  "*ind
    scrut=emit(node[1],subst,notes)
    branches=node[2]
    if len(branches)==1:                                  # single constructor -> destructure
        _ctor,vars,body=branches[0]
        if _ctor=="ex_intro" and len(vars)>2:             # Coq's raw ex_intro pattern carries an
            vars=vars[-2:]                                # extra leading motive placeholder ('_')
            # that Lean's `Exists`/⟨⟩ has no slot for -- mirrors the `f=="ex_intro"` special
            # case in emit() (term mode), which already drops args[0] the same way.
        if vars:
            return [f"{pad}obtain ⟨{', '.join(vars)}⟩ := {scrut}"] + emit_tactic(body,subst,notes,ind)
        return [f"{pad}cases {scrut}"] + emit_tactic(body,subst,notes,ind)
    pats=[]                                                # many branches -> rcases pattern per branch
    for _ctor,vars,_body in branches:
        pats.append("⟨"+", ".join(vars)+"⟩" if len(vars)>1 else (vars[0] if vars else "_"))
    out=[f"{pad}rcases {scrut} with " + " | ".join(pats)]
    for _ctor,_vars,body in branches:
        out+=_branch(body,subst,notes,ind)
    return out

# Belt-and-suspenders: a raw Coq token that must NEVER reach Lean. If the emitted
# body contains one, the transliteration leaked — flag it so the lemma becomes a
# clean hole instead of a Lean parse error.
_LEAK=re.compile(r"(?<![\w'])(?:match|fix|cofix|eq_ind|eq_ind_r|eq_rect|eq_rec)(?![\w'])"
                 r"|<>|/\\|\\/|->|(?<![-<>=!:~])~(?!=)")

def emit_body(body, subst, notes):
    """RHS after ':=' — tactic block if case-splits present, else a term."""
    if contains_elim(body):
        s="by\n" + "\n".join(emit_tactic(body,subst,notes,1))
    else:
        s=emit(body,subst,notes)
    if _LEAK.search(s):                                   # a raw Coq token leaked -> force a hole
        notes.append("LEAK: raw Coq token in emitted Lean")
    return s

# --------------------------------------------------------------------------
# 4. Drive: one lemma
# --------------------------------------------------------------------------
def transliterate(coq_file, name, lean_binders):
    pt=run_proof(coq_file, name, default_q_paths())
    ast=parse_term(P(tok(pt)), stop={None})
    while ast[0]=="paren": ast=ast[1]      # unwrap `(fun … => …)`
    assert ast[0]=="fun", f"top not fun: {ast[0]}"
    coq_binders=ast[1]
    subst={c:l for c,l in zip(coq_binders, lean_binders)}
    notes=[]
    body=emit(ast[2], subst, notes)
    return body, notes, coq_binders

if __name__=="__main__":
    # NEW clean lemma target: between_exchange4, transliterated against the
    # PROVEN cone (implicit versions) -> should be axiom-clean.
    f="theories/Main/Tarski_dev/Ch03_bet.v"
    lean_binders=["A","B","C","h"]                # Bet A B C  (genuinely NEW lemma)
    body, notes, coqb=transliterate(f, "Bet_perm", lean_binders)
    print("Coq binders :", coqb)
    print("cone-targeted Lean proof body (implicit args dropped):\n")
    print("  " + body)
    print("\nnotes:")
    for n in notes: print("  -", n)
