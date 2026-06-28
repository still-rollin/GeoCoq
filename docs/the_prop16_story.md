# Proposition 16 ki Kahani

### Do chhupe bugs, ek "joint constraint" paheli, aur ek tactic jise backtrack karna nahi aata tha

---

## Prologue: prop_16 kya hai aur itna important kyun

`proposition_16` = Euclid ki Book I, Proposition 16 — **Exterior Angle Theorem**:

> "Kisi tribhuj ki ek bhuja badhao, to jo bahari (exterior) kona banta hai, woh dono andaruni (interior) opposite konon se bada hota hai."

Yeh GeoCoq Elements ka sabse **bada** proof hai — **~330 lines**. Aur yeh ek **keystone** hai: iske upar **props 17 se 48 tak** ka ek bada cascade khada hai. prop_16 nahi banta, to woh ~30 propositions bhi nahi banenge.

Is ek lemma ne **do alag-alag bugs** bahar nikaale — pehla import ka, doosra ek gehra tactic-engine ka. Yeh dono ki kahani hai.

---

## Part 1: Pehla bug — "Gayab lemma" (`proposition_15a`)

### Kaise pakda gaya

Ayaan (project owner) ne ek tez observation ki: prop_16 ke proof mein teen jagah `conclude proposition_15a` likha hai — **par imports mein `proposition_15` hai hi nahi!**

```lean
have : CongA B E A C E F := by conclude proposition_15a   -- line 67
...                                                         -- aur 187, 294 pe bhi
```

Build error confirm kar gaya:
```
proposition_16.lean:67:42: Unknown identifier `proposition_15a`
```

`proposition_15a` ek **unknown naam** tha — Lean ko pata hi nahi tha woh kya hai.

### Asli wajah — ek `.v` file mein KAI lemmas

Coq ki `proposition_15.v` file kholi, to dekha usme **teen** lemmas hain:

```coq
Lemma proposition_15  : ...   (* line 9   *)
Lemma proposition_15a : ...   (* line 106 *)
Lemma proposition_15b : ...   (* line 115 *)
```

Lekin hamara transpiler (jo Coq → Lean karta hai) **sirf pehla** lemma (`proposition_15`) translate karta tha. `15a` aur `15b` ko bilkul chhod deta tha. Isliye `proposition_15.lean` mein sirf `proposition_15` tha, aur `proposition_15a` kahin define hi nahi hua.

Coq mein `Require Export proposition_15` likhne se teeno lemmas dikh jaate the — par Lean translation mein woh teeno emit hi nahi hue the.

### Fix — teen hisson mein

**(1) Secondary lemmas emit karo.** Transpiler ko bola: jab `proposition_15.v` translate karo, to main lemma ke **baad** wale lemmas (`15a`, `15b`) ko bhi usi `proposition_15.lean` module mein emit karo. (Jo helper main lemma se *pehle* aate hain — jaise `proposition_22.v` mein — woh pehle se inline ho rahe the, unhe nahi chheda.)

**(2) Lemma → file index.** Ek nakshा (map) banaya: `proposition_15a → proposition_15`, `proposition_15b → proposition_15`. Taaki jab koi file `proposition_15a` use kare, transpiler samajh jaaye ki "yeh `proposition_15.lean` se aata hai" aur sahi `import proposition_15` daal de.

**(3) Self-import guard.** Ek chhota bug aaya: `15a` apne proof mein `proposition_15` use karta hai (same file). Index ne bola "`proposition_15` import karo" — par woh to **wahi file** thi! `proposition_15.lean` apne aap ko import karne laga → "module imports itself" error. Fix: local references (same-file lemmas) ke liye koi import nahi.

**Result:** `proposition_15.lean` ab teeno lemmas deta hai, prop_16 sahi import karta hai, `Unknown identifier` **gaya**. Aur yeh general fix tha — `prop_28A`, `prop_29`, `prop_39A`, `pointreflectionisometry` sabko `proposition_15a` chahiye tha. **141 → 146.**

---

## Part 2: Doosra bug — "LtA" paheli (gehra wala)

`proposition_15a` theek hone ke baad, prop_16 ek **alag** jagah ruk gaya — line 285:

```lean
have : LtA A B C B C G := by conclude_def LtA
```

800,000 heartbeats khatam → timeout. Yeh asli gehri problem thi.

### LtA kya hai

`LtA` = "Less-Than-Angle" (ek kona doosre se chhota). Iski definition ek **existential** hai (CongA jaisi):

```
LtA A B C B C G  :=  ∃ U X V,   BetS U X V  ∧  Out C B U  ∧  Out C G V  ∧  CongA A B C B C X
                     └witnesses┘  └─conj1─┘     └─conj2─┘     └─conj3─┘     └──── conj4 ────┘
```

Padho: "**Teen points U, X, V exist karte hain** jaise ki: X, U aur V ke beech hai; U ray CB pe hai; V ray CG pe hai; aur kona ABC = kona BCX."

Maine context dekh ke **sahi jawab nikaala**: `U=e, X=h, V=G`. Saare 4 facts pehle se context mein the:
- `BetS e h G` ✓
- `Out C B e` ✓
- `Out C G G` ✓
- `CongA A B C B C h` ✓

Aur prove bhi kiya — `exact ⟨e, h, G, by assumption ×4⟩` 42 second mein compile. **Toh proof exist karta hai. Problem sirf witnesses DHOONDHNE ki hai.**

### Yeh CongA se HARD kyun (asli core)

Pichle hafte `build_struct` (deferred-unification) ne CongA ko solve kiya tha. Wahi tareeka LtA pe **kyun fail hua?**

**CongA mein witnesses UNIQUE the:**
```
Out B A ?U   →  context mein sirf EK match (Out B A A)  →  ?U = A pakka, koi confusion nahi
```

**LtA mein witnesses AMBIGUOUS hain:**
```
Out C B ?U   →  DO matches: Out C B B (U=B) aur Out C B e (U=e)   ← kaunsa? pata nahi
BetS ?U ?X ?V →  ~20 alag BetS facts!                            ← bahut saare options
```

`build_struct` ka tareeka tha: `exact ⟨_, _, _, by assumption ×4⟩` — conjuncts baayein-se-daayein solve karo. Pehla conjunct `BetS ?U ?X ?V` aaya, aur `by assumption` ne **lalach mein pehla** BetS fact pakad liya (galat), U/X/V galat pin kar diye.

Ab killer baat:

> **`exact ⟨...⟩` ek choice ko COMMIT kar deta hai — peeche nahi mudta (no backtracking).** Galat BetS pakad ke aage badh gaya, phir conjunct 4 (CongA) galat X pe fail hua — par ab wapas jaake doosra BetS try nahi kar sakta. Poora fail.

Yaani: **CongA = no ambiguity (commit chal gaya). LtA = ambiguity (genuine backtracking chahiye, jo `exact` karta hi nahi).**

### Attempts ka safar (har ek ne kuch sikhaya)

| # | Tareeka | Result | Seekh |
|---|---|---|---|
| 1 | `exact ⟨e,h,G, by assumption×4⟩` (witnesses haath se) | ✅ 42s | Answer sahi hai, sirf search ka issue |
| 2 | two-phase `build_struct` (cheap `exact` phir full `exact`) | ❌ timeout | Dono `exact` → dono commit-without-backtrack |
| 3 | `refine ⟨?U,?X,?V, ?_×4⟩; solve_by_elim*` | ❌ timeout | Witnesses **goal** ban gaye → solve_by_elim har Point ko ?U mein plug karke explode |
| 4 | `refine ⟨_,_,_, ?_×4⟩` (witnesses `_`) | ❌ error | `_` witness **synthesize** nahi hota (witness pata nahi to Exists ka type infer nahi) |
| 5 | `unfold LtA; prove_struct` (mera engine) | ❌ "not ∨/∧" | **mdata bug!** (neeche) |
| 6 | **`apply Exists.intro ×3; refine ⟨?_×4⟩; solve_by_elim*`** | ✅ **26s** | **Yahi jeeta!** |

### Do bade discoveries

**Discovery 1 — `mdata` ka lifafa, phir se.**

`unfold LtA; prove_struct` ne bola "goal is not a ∨/∧-combination" — yaani `prove_struct` ne goal ko existential **pehchaana hi nahi**. Wajah wahi `mdata noImplicitLambda` ka invisible lifafa jo `unfold` chadha deta hai (prop_04 wali kahani mein bhi yeh aaya tha). `build_struct` mein maine yeh strip kiya tha, par `prove_struct` mein **nahi** kiya tha. Isliye `prove_struct` har unfolded-existential pe bail kar raha tha. Maine `consumeMData` add kiya — par yeh akela LtA ke liye kaafi nahi tha (uska alag def-atom issue tha).

**Discovery 2 — jeetne wala formula.**

Attempt 6 ne kaam kiya, aur usne theek woh teen cheezein milaayi jo chahiye thi:

```
apply Exists.intro  (×3)   →  witnesses ko DEFERRED METAVARIABLE banao
                              (na goal — to solve_by_elim Points plug nahi karega;
                               na `_` — to synthesize-error nahi aayega)

refine ⟨?_, ?_, ?_, ?_⟩    →  4 conjuncts ko GOALS banao

solve_by_elim*             →  saare goals JOINTLY solve karo, BACKTRACKING ke saath
```

 Kaise chalta hai: `solve_by_elim*` jab `BetS _ _ _` ko context ke `BetS e h G` se match karta hai, teeno witnesses (U,X,V) **ek saath** bhar jaate hain (joint constraint). Aur agar woh galat BetS pakde aur aage `Out C B U` fail ho, to woh **undo karke** doosra BetS try karta hai — yeh `exact` nahi kar sakta tha. Witnesses goal na hone ki wajah se woh Points pe time waste bhi nahi karta.

Ayaan ne sahi diagnose kiya tha ("witnesses ko goal mat banne do") — bas `refine _` ke bajaye **`apply Exists.intro`** se defer karna asli chaabi thi.

### Fix — `build_struct` mein "Phase C"

`build_struct` ab teen phases mein chalta hai:

```
Phase A (sasta):  exact ⟨_×k, by assumption ×n⟩
                  → CongA-jaise UNIQUE-witness builds (fast, no backtracking needed)

Phase B (full):   exact ⟨_×k, by (assumption|prove_struct|nCol-bridge) ×n⟩
                  → OS/Col-jaise builds jahan koi conjunct disjunction ho

Phase C (search): apply Exists.intro ×k; refine ⟨?_×n⟩; solve_by_elim* (maxDepth 8)
                  → LtA-jaise AMBIGUOUS-witness builds (genuine joint backtracking)
```

`first | A | B | C` — sasta pehle, mehenga sirf zaroorat par. CongA Phase A se nikalta hai, OS Phase B se, LtA Phase C se. Sab ek hi general tactic, koi witness hardcode nahi.

**Result:** `proposition_16` ab **88 second mein compile** hota hai (olean 667 KB) — pehle 800k-timeout tha. ✅

---

## Epilogue: Do bugs, ek philosophy

prop_16 ne do bilkul alag layers ke bugs nikaale:

1. **Transpiler-level** — ek `.v` file mein kai lemmas, jinme se sirf pehla translate ho raha tha (import bug). *Ayaan ne pakda.*
2. **Engine-level** — ambiguous-witness existential build, jise `exact` ka commit-without-backtrack solve nahi kar sakta tha; `apply Exists.intro + solve_by_elim*` ke joint-backtracking ne kiya.

Dono fixes **general** hain — koi prop_16-specific hardcode nahi:
- Multi-lemma emission har aise `.v` file pe chalega.
- Phase-C har ambiguous-witness existential-build pe chalega.

Aur dono ek hi underlying theme se jude hain — wahi jo poore project ka core hai:

> **`auto` vs `eauto` — eager solve mat karo, defer karo. Aur jab choices ambiguous hon, COMMIT mat karo — backtrack karo.**

CongA ne sikhaya "defer karo." LtA ne agla sabak diya: "**defer kaafi nahi — backtrack bhi karo.**"

prop_16 ek keystone hai. Yeh green hone se props 17–48 ka pura cascade khulta hai — toh yeh ek lemma, asal mein, Elements ka ek bada hissa hai.

---

*Likha gaya: prop_16 ke 800k-timeout (do alag jagah) se 88s-compile tak ke safar ke baad.*
*Fixes: `geolean_transpile.py` (multi-lemma + import index), `conclude_bounded.lean` (mdata strip), `euclidean_tactics.lean` (build_struct Phase C). Koi individual lemma file haath se nahi chhui — sab transpiler + engine se.*
