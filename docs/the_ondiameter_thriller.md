# Circle ka Khoon — ondiameter ki Thriller

### Ek lemma jo teen baar zinda hua aur teen baar mara, jab tak ek line ne case suljhaya

---

## Raat 1 — Laash

Audit ka log aaya. 170 lemmas green. Do laashein bachi thीं — own-error, koi dependency nahi blame karne ko, apni hi galti se mari hui:

```
proposition_27
lemma_ondiameter
```

`proposition_27` ke baare mein sab jaante the — keystone, props 28 se 48 tak ka darwaza. Par `lemma_ondiameter`? Iska naam HANDMADE list mein tha — "protected, transpiler ko chhune mat do." File ke notes mein likha tha *"stale transpiler-output, galti se protect ho gaya."*

Detective (main) ne case file kholi. Pehla shaque: **"Yeh laash purani hai. Bas dobara transpile kar do, naya engine ise sambhal lega."**

Galat. Bilkul galat. Aur yeh galti hi poori kahani ka pehla mod thा.

---

## Khoji — header bolti hai

File ka header padha. Aur woh "stale output" wali theory wahीं dam tod gayi:

```
TIER-2 (transpiler) ATTEMPT FAILED — statement type error
Reason: transpiler har variable ko `Point` banata hai, par `K` ek `Circle` hai.
TIER-3 (hand) COMPLETION — `K` ka binder `Circle` retype kiya.
```

Dekho line 22:
```lean
∀ (D F : Point) (K : Circle Point) (M N P Q : Point), ...
```

Yeh `K : Circle` **kisi insaan ne haath se likha tha.** Transpiler yeh likh hi nahi sakta — woh `K` ko bhi `Point` bana deta aur statement type-check fail hota. Matlab yeh laash "stale" nahi thी — yeh **genuinely hand-finished** thी, sahi se protected.

Detective ne apni hi pehli theory phaad ke phenk di. *"Re-transpile? Agar maine yeh kiya, toh `Circle` fix mit jaata aur statement hi toot jaata. Main khud hi saboot mita raha tha."*

Asli sawaal ab badla: **agar statement sahi hai, toh maut kaise hui?**

---

## Maut ka waqt — `whnf` pe 200,000 dhadkanein

Diagnostic chala. Error ek nahi, **chaar**:

```
line 41:33  timeout at `whnf`             (200000 heartbeats)
line 42:9   timeout at `tactic execution`
line 43:7   timeout
line 21:1   timeout at `whnf`             (poora theorem)
```

`maxHeartbeats` — Lean ka stopwatch. 200,000 dhadkanein, uske baad maut. Par yeh limit **poore theorem ke liye ek hi hai**, har tactic ke liye alag nahi.

Line 41-43 ne ek `rcases` branch ki taraf ishaara kiya:
```lean
· have : InCirc N K := by conclude_def InCirc   -- line 41
  close                                          -- line 42
```

`InCirc` ki definition kholi — aur khooni ka chehra saamne aaya:
```lean
InCirc P J := ∃ X Y U V W, CI J U V W ∧ (P = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U P U Y))
```

**Paanch existential witnesses. Ek conjunction. Andar ek disjunction.** Geometry ka sabse bhaari shape. Aur theorem ise **teen baar** build karta tha — teen `rcases` branches mein.

---

## Pehla Reconstruction — laash bolti hai

Detective ne ek experiment kiya. Teen mein se **sirf ek** branch ka `conclude_def InCirc` hataya, uski jagah haath se jawab likha:
```lean
exact ⟨_, _, _, _, _, h1, Or.inr ⟨by assumption, by assumption, by assumption⟩⟩
```

Aur... **poora theorem turant zinda ho gaya.** ✔

Yeh do baatein chilla-chilla ke bata gaya:
1. **Saare saboot maujood the.** Jawab trivial tha — ek `CI` fact aur teen assumptions. Koi missing lemma nahi.
2. Maut **search ki keemat** se hui thi. Engine ka prover har `conclude_def InCirc` pe ~85,000 dhadkanein khaata tha. Do calls (170k) bach jaati, teesri (255k) — maut.

Murder weapon mila: **`apply Exists.intro` × 5.** Engine har witness ke liye ek baar yeh chalata, aur har baar `Circle` ki structure ko `whnf` se normalize karta — yahi 85k ka sink. Jabki anonymous constructor `⟨...⟩` paanchon existentials ko **ek hi pass** mein nipta deta — turant.

*"Toh engine ko `⟨...⟩` se build karwao. Khatam,"* detective ne socha. Woh nahi jaanta tha ki abhi laash do baar aur uthegi.

---

## Zinda 1, Mara 1 — "typeclass stuck"

Engine ko `⟨...⟩` se build karwaya. Build chalaya. Teen branches:

```
Branch 1 (c1): ✔ zinda
Branch 2 (c2): ✖ "typeclass instance problem is stuck"
Branch 3:      — abhi tak pahuncha hi nahi
```

Ek branch zinda, doosra mara — **same code se!** Detective sakte mein aa gaya. Ek hi tactic, do alag nateeje?

Branch 2 (c2: `BetS F N M`) ko microscope ke neeche rakha. Disjunction ka Or.inr side:
```
BetS F ?Y ?X ∧ Cong F ?X P Q ∧ Cong F N F ?Y
```

Aur tab **ambiguity** dikhi — do alibi, ek hi naam:
- `Cong F ?X P Q` ko **do** hyps match karte the: `Cong F D P Q` (kehta `?X = D`) aur `Cong F M P Q` (kehta `?X = M`).
- Sahi jawab `?X = M` tha — par yeh sirf `BetS F N M` ke **joint-constraint** se pata chalta.

Engine ka prover "sabse-kam-metavariable-pehle" niyam se chalta tha. `Cong` (1 unknown) ko `BetS` (2 unknowns) se **pehle** solve karta → galat alibi `?X = D` pakad leta → aur phir **wapas nahi mud sakta** (backtrack nahi). Galat aadmi ko phaansi, asli katil bhaag gaya.

Branch 1 bach gaya kyunki uska witness unambiguous tha. Branch 2 phasa kyunki uska witness do jagah fit hota tha. **Same code, alag context — alag maut.**

---

## Zinda 2, Mara 1 — "synthesize placeholder w"

Detective ne ek niyam badla: `BetS` pehle solve karo (left-to-right), `Cong` baad mein. Branch 2 zinda. Build chalaya:

```
Branch 1: ✔
Branch 2: ✔
Branch 3: ✖ "don't know how to synthesize placeholder w"
```

Teesra mod. Branch 3 (c3: `F = N`) ka raaz alag tha. Yahan `N = F` **sach** tha — toh disjunction ka **Or.inl** side lena tha (`P = U`).

Par dekho — `X` aur `Y` to **sirf Or.inr side mein** the. Or.inl chuno, toh `X, Y` ka **koi zikr hi nahi** — woh bilkul unconstrained reh gaye. Anonymous constructor ke `_` holes the woh, aur jo tactic disjunction prove kar raha tha uski **pahunch hi nahi thी** un holes tak. Do gawah, jinki kabhi gawahi hi nahi li gayi. → "synthesize placeholder w."

Ab teen alag rahasya the, teen alag branches:

| Branch | Maut | Asli wajah |
|---|---|---|
| 1 | (bach gaya) | unambiguous witness |
| 2 | typeclass stuck | **ambiguous** witness — galat alibi pakda |
| 3 | placeholder w | **dangling** witness — Or.inl gawah chhod gaya |

Detective hताsh — *"Ek method teeno ko sambhal hi nahi pa raha. Branch 2 ko left-to-right chahiye, Branch 3 ko witness-fill chahiye, aur dono ek doosre se ladte hain."*

Yahीं case rukа. Detective ne professor ko phone lagaya.

---

## Professor ka Insight — "case ko pehle commit karo"

Professor ne ek line mein gutth suljha di:

> *"Galti yeh maan lena hai ki ek hi method teeno branches sambhale. Woh method exist hi nahi karta — aur uski zaroorat nahi. **OR ko pehle commit karo** (`Or.inl` ya `Or.inr`). Uske baad har side ka problem alag aur aasaan ho jaata hai."*

Aur jaise hi yeh suna, sab kuchh saaf ho gaya:

- **`Or.inl` side**: yahan `X, Y` ka zikr nahi. Toh "dangling witness" ab dikkat nahi — pata hai yeh side unhe use nahi karta, koi bhi point de do, khatam. (Branch 3 solved.)
- **`Or.inr` side**: yahan ambiguity hai, jiska ilaaj pata hai — left-to-right, `BetS` pehle, `?X` pin. Yeh side kabhi dangling nahi deta. (Branch 2 solved.)

**Branch 2 ki dikkat sirf `Or.inr` pe thी, Branch 3 ki sirf `Or.inl` pe.** Jab tak OR commit nahi hua tha, dono dikkatein ek saath ladti thीं aur koi single method dono nahi sambhal pata tha. OR commit karte hi woh **alag** ho gayीं — aur har ek ka ilaaj pehle se haath mein tha.

---

## Aakhri Raat — phaansi sahi gardan pe

Detective ne professor ka structure likha:

```lean
refine ⟨_, _, _, _, _, ?ci, ?disj⟩   -- ek pass: paanchon witness + dono conjunct, no Circle whnf
rotate_left 5                          -- conjunct goals ko aage lao (taaki witness pehle pin ho)
-- ci  : assumption                    → CI K U V W se U,V,W pin
-- disj: OR ko COMMIT karo —
--   left  ; assumption                → Or.inl: P=U; X,Y bachे, neeche fill honge
--   right ; (repeat' apply And.intro); all_goals assumption
--                                      → Or.inr: BetS pehle → ?X sahi pin
all_goals assumption                   -- bache dangling witness (Branch 3) ko koi point do
```

Build chalaya. Teen branches. Saans roki.

```
Branch 1: ✔
Branch 2: ✔
Branch 3: ✔
Build completed successfully.
```

**Teeno zinda. Ek saath. Pehli baar.** Aur teeno milke 200k dhadkanon ke andar — kyunki `refine ⟨⟩` ne `apply Exists.intro × 5` wala Circle-whnf sink hata diya tha. Murder weapon gayab, gawah sahi, case band.

---

## Epilogue — engine mein, file mein nahi

Ek aakhri baat thी. Yeh jeet `lemma_ondiameter.lean` mein haath se nahi likhi ja sakti — woh **protected** hai, regenerate honi chahiye. Toh detective ne yeh poora OR-commit logic **engine** mein daala — `euclidean_tactics.lean` ke `build_struct` mein, us purane "phase C" ki jagah jo `Circle` pe explode karta tha.

Ab `lemma_ondiameter` apne saaf-suthre `conclude_def InCirc` se hi compile hota hai — bina kisi hand-hack ke. Aur kyunki fix engine mein hai, woh **general** hai: `InCirc`, `OnCirc`, `OutCirc` — har "Circle ke andar existential + disjunction" wala build ab isse zinda rahega.

> **Case ka sabaq:** Jab ek hi sawaal ke do hisse aapas mein ladein, unhe ek saath mat suljhao. **Pehle ek choice commit karo** (yahan: OR ka side) — uske baad har hissa apne aap alag aur aasaan ho jaata hai. Jo paheli "kisi ek chaabi se nahi khulti thी", woh asal mein **do alag taale** thी, ek darwaze ke peeche chhupe.

Aur detective ki sabse pehli theory — *"bas re-transpile kar do"* — agar woh sahi maan li jaati, toh `Circle` fix mit jaata, statement toot jaata, aur asli bug — engine ka 85k Circle-sink — **kabhi pakda hi nahi jaata.** Kabhi-kabhi sabse khatarnaak galti pehla shaque hota hai.

---

*Likha gaya: ondiameter ke `whnf`-timeout ko teen branches ke teen alag root cause (ambiguous / dangling witness, Circle-whnf sink) mein todne aur J. Narboux ke OR-commit insight se ek hi engine-fix mein suljhane ke baad.*
*Fix: `euclidean_tactics.lean` ke `build_struct` mein (folded-def OR-commit build). Koi individual lemma file haath se nahi chhui.*
