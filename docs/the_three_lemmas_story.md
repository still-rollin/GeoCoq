# Teen Lemmas ki Kahani

### "Yeh teen to easy honge na?" — aur har ek nikla bilkul alag bug

---

## Prologue: ek bhul-bhulaiya jisme har darwaza alag

prop_16 green hone ke baad, audit ne **chaar** own-errors dikhaye. Inme se ek (`ondiameter`) HANDMADE tha — usko transpiler se nahi chhu sakte. Bache **teen**:

- `proposition_17`
- `lemma_angleordertransitive`
- `lemma_angleaddition`

Ayaan ne kaha: *"Teen lemmas hain own-error ke saath — yeh easy honge na, ig?"*

Lagta to easy tha. Lekin jab khola, to **teeno ka root cause bilkul alag** nikla. Yeh teen alag-alag chhoti paheliyon ki kahani hai — jinme se har ek ne engine ko thoda aur general banaya.

Pehle errors dekhe:

```
proposition_17.lean:128         maximum recursion depth has been reached
lemma_angleordertransitive:59   maximum recursion depth has been reached
lemma_angleaddition:68          timeout at isDefEq (800000 heartbeats)
```

Do "max recursion", ek "timeout". Dekhne mein do same lagte the — par andar se teeno judaa the.

---

## Lemma 1: `angleordertransitive` — "Sahi jawab, par ulte order mein"

### Error
Line 59, `conclude_def LtA`, **max recursion depth**.

### Khodaai

Line 59 aisa tha:
```lean
obtain ⟨H, S, T, _, _, _, _⟩ : ∃ H S T, (BetS S H T ∧ Out Q U S ∧ Out Q W T ∧ CongA A B C U Q H) := by conclude_def LtA
```

Maine context dekha aur ek **chaunkaane wali baat** mili — `this : LtA A B C U Q W` **pehle se context mein maujood tha.** Aur jo goal banaana tha (`∃ H S T, ...`), woh asal mein **isi `this` ka unfolded roop tha.**

Yaani jawab "banaana" nahi tha — already mil chuka tha. Yeh ek **EXTRACT** case tha (hyp se nikaalo), **BUILD** nahi.

### Asli problem — "binder order" ka jhagda

`LtA A B C U Q W` aise unfold hoti hai:
```
∃ U₀ X₀ V₀, ...    order: (ray, ANGLE, ray)
```
Par transpiler ne goal aise likha:
```
∃ H  S  T,  ...    order: (ANGLE, ray, ray)
```

**Dono bilkul barabar hain** — bas variables ka **likhne ka order alag**. Aur Lean ke liye, existentials jinke binders ka order alag ho, woh **definitionally equal nahi** maane jaate. Isliye seedha `assumption` (ya `exact this`) match nahi karta — chahe fact bilkul wahi ho.

### Crash kyun

`conclude_def LtA` ne pehle `unfold LtA` try kiya — par goal mein `LtA` head tha hi nahi (woh explicit `∃` tha) → unfold fail → fir aakhri fallback `aesop` chala → bade goal pe deep recurse karke **"max recursion depth" crash.**

### Fix — match mat karo, REBUILD karo

```
extract_def LtA   →  context ke `this : LtA ...` ko todo, andar ke atoms
                     (BetS, Out, Out, CongA) ko alag-alag hypotheses bana do
build_struct      →  ab goal ko UNKE apne order mein dobara assemble karo
```

Idea: order match karne ka jhagda chhodo. Hyp ko **atoms mein todo**, phir goal ko **apne order mein naye sire se banao**. Order ka masla khatam.

Engine mein: `conclude_def` ke EXTRACT branch mein sirf `prove_struct` tha, **`build_struct` nahi**. Bas wahi add kar diya.

**General kyun:** Koi bhi existential fact (LtA/CongA/OS) jo hyp se extract hota hai par binder-order alag hai — sab clear honge. Yeh corpus mein bahut common pattern hai.

✅ `angleordertransitive` compile.

---

## Lemma 2: `proposition_17` — "Aakhri kadam pe ladkhadaya"

### Error
Line 128, `close`, **max recursion depth**.

### Khodaai

prop_17 (Euclid I.17) ka conclusion:
```lean
∀ A B C, Triangle A B C → ∃ X Y Z, SumA A B C B C A X Y Z
```

Proof ke **bilkul aakhir** mein, line se theek pehle:
```lean
have : SumA A B C B C A E C B := by conclude_def SumA   -- line 127
close                                                    -- line 128
```

Toh `close` ko final goal `∃ X Y Z, SumA A B C B C A X Y Z` prove karna tha — aur ek line pehle `SumA A B C B C A E C B` ban chuka tha. Yaani witnesses `X=E, Y=C, Z=B` aur woh SumA fact — bas assemble karna tha.

### Asli problem — `close` existential bana nahi sakta tha

`close` macro ka ladder tha:
```
assumption | by_contra | solve_by_elim | (And.intro...) | tauto | aesop
```

Dekho — isme **existential ko build karne wala koi tactic nahi** (`prove_struct`/`build_struct` nahi the). Toh `∃ X Y Z, SumA...` koi handle nahi kar paaya, aur aakhir mein `aesop` is bade existential pe **deep recurse karke crash** kar gaya.

Yeh ek **andha-dhabba** tha: hum `conclude_def`/`conclude` ko to mehnat se bounded banaye the, par `close` (jo aksar proof ka aakhri existential conclusion discharge karta hai) abhi bhi `aesop` pe atak jaata tha.

### Fix — `close` ko existential banana sikhao

`close` ke ladder mein `prove_struct | build_struct` add kiya (aesop se pehle):
```
assumption | by_contra | prove_struct | build_struct | solve_by_elim | ... | aesop
```

Maine pehle test kiya — `build_struct` akela prop_17 ka goal **6 second** mein close karta hai. Phir engine mein daala.

**General kyun:** Bahut saare proofs `close` pe khatam hote hain jisme theorem ka existential conclusion (`∃ ..., <fact>`) discharge karna hota hai. Yeh fix un sabko help karega — aur max-recursion crash bhi gaya.

✅ `proposition_17` compile. (Aur yeh **keystone** hai — props 18-48 ka cascade kholta hai.)

---

## Lemma 3: `angleaddition` — "Fact tha, par ek dabbe ke andar chhupa"

### Error
Line 68, `conclude_def RT`, **isDefEq timeout** (max recursion nahi — alag symptom).

### Khodaai

`RT` ("right-together") ki definition sabse **badi** existential thi:
```
RT A B C D E F  :=  ∃ X Y Z U V,  Supp X Y U V Z ∧ CongA A B C X Y U ∧ CongA D E F V Y Z
```
**Paanch witnesses, teen conjuncts.** Goal: `RT G H q q H K`.

Witnesses dhoondhe:
- `Supp P S Q Q R` ✓ (line 67)
- `CongA G H q P S Q` ✓ (line 34)
- `CongA q H K Q S R` — **yeh kahan hai?**

Pehli nazar mein teesra conjunct context mein nahi dikha. Phase-C (joint backtracking) bhi **clean fail** ho gaya — matlab fact sach mein nahi mil raha tha.

Phir poori file scan ki, aur **line 62** mili:
```lean
have : (Cong H K S R ∧ CongA q H K Q S R ∧ CongA q K H Q R S) := by conclude proposition_04
```

Dekho — `CongA q H K Q S R` **maujood hai!** Par ek **conjunction ke ANDAR** (teen-ka-bundle ka beech wala). Yeh `this : Cong ∧ CongA ∧ CongA` ek single bundled hypothesis tha — alag standalone fact nahi.

`assumption` aur `solve_by_elim` ek conjunction-hyp ke **andar** dabe fact tak nahi pahunch sakte — unhe pehle bundle todna padta hai (`And.right.left` jaise project karna).

### Asli problem — `conclude_def` bundle nahi todta tha

`conclude` macro ke preamble mein `(try spliter)` hai — jo context ki saari conjunctions ko alag-alag hyps mein **tod deta hai**. Par **`conclude_def` mein yeh spliter tha hi nahi.** Isliye conclude_def-builds bundle ke andar ke facts nahi dekh paate the. Aur 5 witnesses + buried fact ke chakkar mein `exact` ka isDefEq spin karke **800k timeout**.

### Fix — build se pehle bundle todo

`conclude_def` ke BUILD branch mein `(try spliter)` add kiya:
```
| (unfold $t; (try remove_double_neg); (try spliter);
   first | done | assumption | prove_struct | build_struct)
```

`spliter` = `casesm* _ ∧ _` — saari conjunction-hyps ko tod deta hai. Ab `this : A ∧ B ∧ C` teen alag facts ban jaata hai, aur build_struct beech wale `CongA q H K Q S R` ko dhoondh leta hai.

Aur yeh **safe** hai — spliter sirf us ek `have` ke **local** proof-state mein chalta hai; baahar ke context ko nahi badalta.

**General kyun:** GeoCoq mein bahut facts `conclude proposition_04` jaise se aate hain jo **conjunctions conclude** karte hain. Unke andar ke facts ab har conclude_def-build ko milenge.

✅ `angleaddition` compile.

---

## Epilogue: Teen darwaze, teen alag chaabiyan

| Lemma | Dikha tha | Asli root cause | Fix |
|---|---|---|---|
| `angleordertransitive` | max recursion | existential **binder-order** mismatch (extract case) | extract_def + build_struct |
| `proposition_17` | max recursion | `close` **existential** assemble nahi kar pata | prove_struct/build_struct in close |
| `angleaddition` | isDefEq timeout | fact ek **conjunction ke andar** dabba | spliter in conclude_def |

Do errors "max recursion" dikhe, ek "timeout" — par teeno bilkul alag bugs the. Yahi is kaam ki asliyat hai: **error message symptom hota hai, root cause nahi.** Har ek ko alag se khodna padta hai.

Aur teeno fixes — **ek bhi hardcode nahi, ek bhi heartbeat-bump nahi.** Sab general:
- Reordered-existential extract → har LtA/CongA/OS extract pe.
- close ko existential-build → har final-existential conclusion pe.
- conclude_def mein spliter → har conjunction-buried fact pe.

Teeno ek hi gehre theme ke alag-alag chehre the — wahi jo poore project ka dil hai:

> **Goal ko match karne ki zid mat karo. Todo, defer karo, rebuild karo, backtrack karo — par hamesha BOUNDED rehkar, taaki aesop ka anant search kabhi na chale.**

`angleordertransitive` ne sikhaya "reorder ko rebuild se haraao." `prop_17` ne "aakhri kadam mat bhoolo." `angleaddition` ne "bundle todna mat bhoolo."

Aur prop_17 ek keystone tha — uske green hone se props 18 se 48 tak ka cascade khulta hai. Toh yeh "teen easy lemmas" asal mein Elements ka ek aur bada darwaza thi.

---

*Likha gaya: teen own-errors (do max-recursion, ek timeout) ke teen alag root causes nikaalne aur fix karne ke baad.*
*Fixes: sab `euclidean_tactics.lean` mein (extract branch, close ladder, conclude_def preamble). Koi individual lemma file haath se nahi chhui.*
