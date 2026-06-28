# Proposition 04 ki Kahani

### Ek lemma ne kaise teen chhupe bugs bahar nikaale — aur engine ko general bana diya

---

## Prologue: Yeh sab ho kya raha hai

Hum **GeoCoq** ko **Lean 4** mein translate kar rahe hain.

GeoCoq ek geometry library hai — Euclid ki *Elements* ke theorems, formally proved, **Coq** language mein. Hamara kaam: in proofs ko Lean 4 mein le aana — **honestly**. Honest ka matlab: koi `sorry` nahi (jo "yeh maan lo, prove nahi karunga" bolta hai), koi fake axiom nahi, koi heartbeat-cheating nahi.

234 lemmas hain *Elements* mein. Inme se ek hai **`proposition_04`** — Euclid ki Book I ki Proposition 4. Isko maths mein **SAS** kehte hain: *Side-Angle-Side*. "Agar do tribhujon ki do bhujayein aur unke beech ka kona barabar ho, to tribhuj congruent (poori tarah barabar) hain."

Yeh lemma **bahut important** hai — kyunki iske upar **50+ aur propositions** khade hain. Agar prop_04 nahi banta, woh saare bhi nahi banenge (cascade). Toh yeh ek **keystone** hai.

Aur yahi lemma **800,000 heartbeats** (Lean ka time-budget) khatam karke **timeout** ho raha tha. Compile hi nahi hota tha.

Yeh us ek lemma ko theek karne ki kahani hai — jisne raaste mein teen alag-alag chhupe hue bugs bahar nikaal diye.

---

## Chapter 1: Mulzim ki pehchaan

Sabse pehle ek tareeka chahiye tha yeh jaanne ka ki *prop_04 timeout kahan hota hai*. Poori file ko chalane do — 800k tak ghoom ke marr jaati thi, error aata:

```
proposition_04.lean:183:97: timeout at `whnf` (800000 heartbeats)
```

Line **183**. Wahan dekha to ek line thi:

```lean
have : CongA A B C a b c := by
  (try (have : nCol A B C := nCol_notCol _ _ _ (by assumption)));
  conclude_def CongA
```

Mulzim mil gaya: **`conclude_def CongA`**.

`conclude_def X` ek tactic hai jiska kaam: "ek fact `X` ko uski definition kholke prove karo." Yahan `X = CongA` — angle congruence.

Par ek doubt tha: kya yahi *ek* line poora 800k kha rahi hai, ya kahin aur se aa raha hai? Confirm karne ke liye maine ek **chhota experiment** kiya — prop_04 ki copy banayi, sirf is line ki jagah `sorry` (yaani "is step ko skip kar do") daal diya:

```lean
have : CongA A B C a b c := by sorry
```

Result: **baaki poora prop_04 8 second mein compile ho gaya.** 

Iska matlab saaf tha — **poora 800k ka kharcha sirf in `conclude_def CongA` steps mein** tha (prop_04 mein aise teen steps the). Baaki sab bilkul theek.

---

## Chapter 2: CongA ko samajhna — "ek paheli jisme 4 khaali dabbe hain"

`CongA A B C a b c` ka matlab: "angle ABC, angle abc ke barabar hai." Iski definition aisi hai:

```
CongA A B C a b c  :=  ∃ U V u v,
       Out B A U  ∧  Out B C V  ∧  Out b a u  ∧  Out b c v
     ∧ Cong B U b u  ∧  Cong B V b v  ∧  Cong U V u v  ∧  nCol A B C
```

Ise insaani bhasha mein padho:

> "**Chaar points U, V, u, v aise exist karte hain** ki yeh 8 sharten sach hon."

Toh `conclude_def CongA` ko do kaam karne hain:
1. **4 witnesses (U, V, u, v) dhoondho** — yeh points kya hain.
2. **8 conjuncts (sharten) prove karo.**

Sahi jawab dekhne mein trivial tha: `U=A, V=C, u=a, v=c`. Aur saare 8 facts context mein **pehle se maujood the**. Phir bhi engine 800k kha raha tha. Kyun?

Iska jawab teen layers mein chhupa tha.

---

## Chapter 3: Problem #1 — "Eager" engine jo galat sawaal pehle poochta hai

Hamara solver `prove_struct` ek strategy use karta tha jise hum **eager search** kehte hain. Soch yeh thi:

> "Conjuncts ko ek-ek karke prove karo. Jis conjunct mein witness aaye, usse turant pin (fix) kar do."

Toh woh pehla conjunct uthata hai:

```
Out B A ?U
```

Yahan `?U` ek **khaali dabba** hai (metavariable). Engine sochta hai: "is conjunct ko match karke `?U` pata chal jaayega."

**Lekin yahan hi woh phisal jaata hai.** `Out B A ?U` ka matlab hai "U, ray B→A par hai." Par ek ray par to **infinite points** hote hain! Yeh akela conjunct `?U` ko **pin nahi karta** — bahut saare U chal sakte hain. Engine ke paas koi unique cheez nahi jisse woh ?U decide kare. Atak jaata hai.

Yeh **conversation ke pehle din wala `auto` vs `eauto`** distinction hai (jo advisor Julien ne bataya tha):

| | |
|---|---|
| **Eager search (`auto`)** | "Abhi ke abhi har dabba bhar do." → Yahan **fail**, kyunki koi single conjunct akela witness fix nahi karta. |
| **Deferred unification (`eauto`)** | "Dabbe khaali chhodo. Baad mein ek conjunct saare 4 ko **ek saath** bhar dega." |

Asli jaadu kahan tha? **Ek alag conjunct** mein:

```
Cong U V u v      ←→ context ka      Cong A C a c
```

Yeh ek hi match mein **chaaron** witnesses pin kar deta hai: `U=A, V=C, u=a, v=c` — sab ek shot mein. Uske baad baaki 7 conjuncts khud-ba-khud "bhar" jaate hain aur simple `assumption` se band ho jaate hain.

Maine yeh empirically prove bhi kiya — witnesses haath se de diye:

```lean
exact ⟨A, C, a, c, by assumption, by assumption, ... (×8)⟩
```

→ **8 second mein compile.** Matlab proof bilkul trivial hai. Engine ki **strategy** galat thi, proof nahi.

> **Seekh:** Engine eager tha (har cheez abhi solve karo). Yahan deferred chahiye tha (witnesses ko baad ke liye chhodo).

---

## Chapter 4: Problem #2 — Fail hone par "mehenga fallback" jo 800k khaata hai

`conclude_def` ek **ladder** hai — kai tactics ka sequence: `first | A | B | C | ...` (pehla try karo, fail ho to agla). Iska aakhri step ek bahut mehenga fallback tha:

```
unfold CongA at *  ;  ... ;  aesop
```

- `unfold ... at *` — definition ko **poore context** mein khol deta hai (60+ hypotheses).
- `aesop` — ek powerful par **unbounded** automatic prover, jo `CongA`/`nCol`/`Out` sab khol ke ghoomta rehta hai.

Yahi cheez **800k heartbeats kha ke timeout** kar rahi thi.

Maine isolate karke confirm kiya: `prove_struct` to **turant fail** ho jaata hai (Problem #1 ke kaaran) — woh spin nahi karta. Spin to **uske baad** wala aesop-fallback karta hai.

Yahan ek **important honesty point** hai:

> Ye timeout isliye **nahi** tha ki "proof lamba hai, time chahiye." Ye isliye tha ki engine sahi-aur-trivial proof **miss karke** ek bekaar mehenge raaste pe gir jaata hai. **Isliye sirf `maxHeartbeats` badha dena (800k → 2M) CHEATING hota** — woh ek fixable bug ko chhupa deta, theek nahi karta. (Main 2M pe test karke dekh chuka tha — woh sirf line 116 tak pahunchta, har step ~25,000 heartbeats kha raha tha, jabki ek normal step sirf *sau* heartbeats leta hai. Yaani 100x slowness — clearly ek bug, lambai nahi.)

**Fix:** Problem #1 ka solution (deferred unification) ko ek naye tactic **`build_struct`** mein daala, aur ladder mein `prove_struct` ke **theek baad, mehenge fallback se PEHLE** lagaya:

```
first | done | assumption | prove_struct | build_struct | (mehenga fallback)
```

Ab `prove_struct` fail hote hi `build_struct` chalta hai — aesop tak baat pahunchti hi nahi.

**`build_struct` general hai** (koi overfit nahi):
1. Goal dekho — kitne existentials hain (`k`) aur kitne conjuncts (`n`).
2. Banao: `exact ⟨_ ×k, (by assumption / prove_struct / ...) ×n⟩`
3. `_` witnesses ko **deferred** chhodo (kyunki `exact` ke paas poora expected type hai), conjunct-proofs unhe khud pin kar denge.

Crucial detail: **`exact`, na ki `refine`.** `refine` ke andar `_` witnesses **goal** ban jaate hain, aur `assumption` unhe kisi *galat* Point se bhar deta hai. `exact` mein woh metavariable rehte hain jo unification se sahi value pakad lete hain. (Maine dono test kiye — `refine` wala fail hua exactly is wajah se; advisor ne bhi yahi warning di thi.)

---

## Chapter 5: Problem #3 — Ek invisible "lifafa" jisne build_struct ko andha kar diya

`build_struct` likh diya, ladder mein laga diya... aur prop_04 **phir bhi timeout** hua. 

Debug kiya to `build_struct` ne ajeeb error diya:

```
build_struct: goal has no leading existential to build
```

Yaani engine bol raha tha: "Is goal mein to koi `∃` hai hi nahi!" — **jabki goal saaf-saaf `∃ U V u v, ...` tha.**

Maine ek diagnostic trace lagaya, jisne asli goal dikhaya:

```
[mdata noImplicitLambda:1   Exists ... (fun U => Exists ... (fun V => ...))]
```

Dekho dhyaan se — asli `Exists` ke **upar ek `mdata` wrapper** chadha hua hai.

Yeh `mdata` (metadata) ek **invisible lifafa** hai jo Lean ka `unfold` tactic goal ke upar laga deta hai — ek internal flag (`noImplicitLambda`). Yeh sirf Lean ki andaruni book-keeping hai, **maths bilkul nahi badalti.**

Par mera counting code aise tha:

```
goal ka head dekho  →  kya woh `Exists` hai?
```

Head pe to **`mdata` lifafa** baitha tha, `Exists` nahi. Toh code ne dekha "head = kuch aur" → `k = 0` count kiya → "no existential" bolke bail kar diya.

(Mazedaar baat: `exact ⟨...⟩` is lifafe ke andar **automatically** dekh leta hai — isliye Chapter 3 ka manual test chal gaya tha. Par mera raw expression-matching code lifafe pe atak gaya.)

**Fix — ek line:** count karne se pehle lifafa utaar do:

```lean
e.consumeMData.getAppFnArgs    -- mdata strip karke phir head dekho
```

`consumeMData` woh wrapper hata deta hai. Ab `Exists` dikhta hai, `k = 4` count hota hai, aur `build_struct` sahi engage hota hai.

---

## Chapter 6: Teeno ko ek saath dekho — "failure ki zanjeer"

```
Problem #1:  prove_struct EAGER hai
             → ∃-witnesses ko isolation mein pin nahi kar paata
             → FAIL
                  │
                  ▼  (fail hone par)
Problem #2:  ladder mehenge aesop-fallback pe girta hai
             → 800,000 heartbeats kha ke TIMEOUT
                  │
                  ▼  (iska ilaaj:)
             build_struct banaya (DEFERRED unification),
             fallback se pehle ladder mein laga diya
                  │
                  ▼  (par ek aur rukawat:)
Problem #3:  build_struct ko `mdata` lifafe ki wajah se
             goal `∃` jaisa DIKHA hi nahi → bail kar gaya
                  │
                  ▼  (iska ilaaj:)
             consumeMData se lifafa strip → ab sahi engage hota hai
                  │
                  ▼
          ✅  prop_04 ab 4.8 second mein compile hota hai
```

Pehle: **800,000 heartbeats → timeout.**
Ab: **4.8 second.**

---

## Epilogue: Sabse zaroori baat — yeh sab GENERAL fixes the

Is poori kahani ka asli point yeh hai: **in teeno mein se kisi mein bhi maine "answer hardcode" ya "heartbeats badhao" nahi kiya.** Sab **general engine improvements** hain:

- **Deferred unification (`build_struct`)** — har bade existential-build pe chalega (CongA, OS, InCirc, jo bhi). prop_04 ke witnesses kahin likhe nahi.
- **mdata strip** — har `unfold` ke baad chalega, har lemma mein.
- **Ladder ordering** — har `conclude_def` call ke liye behtar.

Yahi hamara **motto** tha shuru se:

> *General fixes, no overfitting, honest measurement. Aur agar kuch cases ke liye insaan chahiye, toh woh bhi theek hai — par cheating karke green dikhana nahi.*

prop_04 ek **keystone** hai — SAS theorem. Iske theek hone se 50+ aur propositions ka cascade khulta hai. Isliye yeh ek lemma theek karna, asal mein, poore *Elements* ka ek bada hissa kholne jaisa hai.

Aur sabse khoobsoorat baat — yeh tinon bugs alag-alag **layers** mein the (strategy, fallback-ordering, ek invisible metadata wrapper), par teeno ek hi *root philosophy* se jude the: **`auto` vs `eauto` — eager solve mat karo, defer karo.** Wahi cheez jo advisor Julien ne pehle din kahi thi.

---

*Likha gaya: prop_04 ke 800k-timeout se 4.8s-compile tak ke safar ke baad.*
*Engine files: `conclude_bounded.lean`, `euclidean_tactics.lean`. Koi individual lemma file haath se nahi chhui gayi — sab transpiler + engine se.*
