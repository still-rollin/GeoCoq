# The Proposition 30 Thriller
### *Ek transpiler, paanch jurm, aur 215 se 223 tak ka safar*

> Hinglish mein. Yeh kahani hai do "boss-level" lemmas — **proposition_30** aur
> **proposition_35A** — ki, jinhone hamare auto-translator (transpiler) ki
> har chhupi galti ek-ek karke bahar nikaal di. Koi proof file haath se nahi
> badli gayi — **saari ladai transpiler ke andar ladi gayi.**

---

## Cast of characters

- **Transpiler** (`geolean_transpile.py`) — hamara auto-translator. Coq proof
  uthata hai, Lean proof banata hai. Deterministic, bottom-up.
- **prop_30** — Euclid Book I, Prop 30: *"do lines jo ek teesri ke parallel
  hain, woh aapas mein bhi parallel hain."* Elements ka sabse bada, sabse
  tedha parallel-line proof. ~160 hypotheses tak pahunch jaata hai.
- **prop_35A** — parallelogram area cluster ka ek helper.
- **conclude / conclude_def / close** — hamari ported tactic-vocabulary. Yeh
  GeoCoq ke "lemma lagao aur premises khud dhoondh lo" wale idioms hain.
- **heartbeat** — Lean ka "kitni mehnat" counter. 800,000 ki limit. Cross
  kiya = timeout = maut.

---

## Pehla scene: 199 ka plateau

prop_29C green hua. Audit: **199/234 compiled.** Char own-errors khade the —
`proposition_30`, `proposition_30B`, `proposition_34`, aur unke peeche 30+
cascade lemmas (poora prop_35→48 ka area/Pythagoras cluster) atke hue.

Inme sabse khatarnak: **prop_30.** Khologe toh ek hi proof mein paanch alag
jurm chhupe mile. Ek-ek karke.

---

## Jurm #1 — *"Adha vaakya kaat dena"* (nested-paren apply)

Coq mein line thi:

```coq
assert (Par A b C d) by (apply (proposition_30A _ _ _ _ E f G H K);assumption).
```

Transpiler ka regex jo `by (...)` ke andar ka tactic uthata tha, woh **non-greedy**
tha — yaani pehle `)` pe hi ruk jaata. Par yahaan toh bracket ke *andar* bhi
bracket tha! Toh usne uthaya:

```lean
have : Par A b C d := by apply (proposition_30A _ _ _ _ E f G H K   ← yahin kat gaya
              close                                                  ← orphan
```

`;assumption)` gayab. Closing bracket gayab. Toota Lean.

**Fix (1 line):** regex ko **greedy** banaya — "aakhri `)` tak jao, beech wale
pe mat ruko." Ab poora `apply (...);assumption` saaf-saaf capture hota hai.

```python
# pehle:  (?:\(\s*(?P<tac>.*?)\s*\)| ...     ← .*?  non-greedy
# baad:   (?:\(\s*(?P<tac>.*)\s*\)|  ...      ← .*   greedy
```

---

## Jurm #2 — *"Har box ko 'NOT' samajhna"* (block = negation)

GeoCoq proofs mein `{ ... }` focus-blocks hote hain. Transpiler **har** aise
block ko maan leta tha ki yeh kisi negation ka proof hai, aur aage `intro h`
chipka deta tha.

Par prop_30 mein block tha:

```coq
assert (Par A b d C).
{ simple eapply proposition_30A. exact H40. exact H171. ... exact H173. }
```

Yeh **seedha** `Par A b d C` sabit kar raha tha — koi negation nahi. Transpiler
ka output:

```lean
have : Par A b d C := by
    intro h               ← bilkul bogus (Par koi function nahi, intro fail)
    apply proposition_30A  ← aur woh saare exact H40… gayab
```

Aur woh `exact H40, H171` — yeh **Coq ke khud ke auto-generate kiye naam** hain.
Lean mein inka koi wajood hi nahi. Inhe copy karna impossible tha.

**Insight:** `simple eapply L` + sirf `exact …`/`assumption` steps ka matlab hi
hai — *"lemma L lagao, premises context se bhar do."* Yeh toh hamara
**`conclude L`** hai!

**Fix (do hisse):**
- `intro h` ab **sirf** jab type sach mein `~` (negation) se shuru ho.
- Naya helper `_eapply_block_to_conclude`: aisa block dekhe toh seedha
  `conclude L` likhe.

```lean
have : Par A b d C := by conclude proposition_30A   ← clean, faithful
```

> 💥 **Jurm #1 aur #2 ne milke**: prop_30B, prop_43B, prop_34 + unka pura
> cascade khol diya. **199 → 215.** Aath lemmas ek jhatke mein.

---

## Jurm #3 — *"Zaroori hint phenk dena"* (explicit args)

prop_30 green hone ke kareeb thi, par ek line pe phir timeout:

```lean
have : Par A b C d := by conclude proposition_30A   ← line 167, 800k timeout
```

Yeh wahi site thi jahaan Coq author ne **jaanboojh kar** likha tha:

```coq
apply (proposition_30A _ _ _ _ E f G H K);assumption
```

Usne points `E f G H K` **haath se diye** — kyunki bina diye, search bahut
slow hoti. Maine (Jurm #1/#2 fix karte hue) galti se yeh saare arguments
**phenk diye** the aur `conclude` bana diya. Natija: Lean ko 160 hypotheses
mein se khud yeh points guess karne pade → **explode → timeout.**

**Insight:** jab args explicitly diye hon, unhe **rakho**. Author ne speed ke
liye hi diye the.

**Fix:** apply-handler ko smart banaya —
- explicit positional args (`(L a b c)`) → `apply L a b c <;> assumption`
  (fast, koi search nahi)
- `with`-clause / no-arg / eapply-block → `conclude L`

```lean
have : Par A b C d := by apply proposition_30A _ _ _ _ E f G H K <;> assumption
```

---

## Jurm #4 — *"NOT (A ya B) ko khud todna"* (de Morgan)

prop_30 mein block:

```coq
assert (~ ~ (CR A f G H \/ CR A E G H)).
{ intro. assert (CR A E G H) by (conclude lemma_30helper). contradict. }
```

`intro h` ke baad context mein aata hai:

```
h : ¬ (CR A f G H ∨ CR A E G H)        ← "na pehla, na doosra"
```

Aage `conclude lemma_30helper` ko chahiye tha: **`¬ CR A f G H`** (pehle disjunct
ka negation). Yeh `h` ke andar chhupa tha — `fun c => h (Or.inl c)` se nikalta
hai. Par `conclude` ne yeh khud synthesize karne ki koshish ki, 160 hypotheses
chhaane → **800k heartbeat → timeout.**

**School ka de Morgan:** `¬(A ∨ B)` ka matlab hi hai `¬A ∧ ¬B`. Toh inhe pehle
hi alag-alag likh do!

**Fix:** transpiler ab `¬¬(disjunction)` block dekhe toh `intro h` ke turant
baad har leaf ka negation emit karta hai:

```lean
have : ¬ ¬ (CR A f G H ∨ CR A E G H) := by
    intro h
    have : ¬ (CR A f G H) := fun c => h (Or.inl c)        ← ready
    have : ¬ (CR A E G H) := fun c => h (Or.inr (c))       ← ready
    have : CR A E G H := by conclude lemma_30helper        ← ab O(1) match
    contradict
```

n-ary disjunction ke liye bhi general: leaf `i` ke liye sahi `Or.inr (… Or.inl)`
injection banata hai.

---

## Jurm #5 — *"Chhupa hua local helper"* (parnotmeet)

Aakhri timeout:

```lean
have : ¬ Meet f E C d := by close   ← line 184, simp timeout
```

Coq mein yeh tha `auto using parnotmeet`. `parnotmeet` ek **mini-lemma** hai jo
prop_30.v ke top pe locally defined hai:

```coq
Lemma parnotmeet: forall A B C D, Par A B C D -> ~ Meet A B C D.
Proof. intros. conclude_def Par. Qed.    ← poora proof EK line
```

Matlab: *"parallel lines kabhi milti nahi."* Transpiler ko yeh local helper
pata nahi tha, toh usne `auto using parnotmeet` ko generic `close` (simp/aesop)
bana diya → `Par` ki bhaari existential definition pe whnf-explode → timeout.

**Insight:** parnotmeet ka asli proof hi `conclude_def Par` hai! Aur `Par` ki
Lean definition ke andar already `¬ Meet A B C D` ek conjunct hai:

```lean
def Par (A B C D) := ∃ ..., ... ∧ ¬ Meet A B C D ∧ ...
```

`conclude_def Par` us conjunct ko seedha nikaal leta hai. Maine MCP se test bhi
kiya — `conclude_def Par` ne goal turant close kiya, **zero timeout.**

**Fix:** transpiler ab `auto using parnotmeet` → `conclude_def Par`.

```lean
have : ¬ Meet f E C d := by conclude_def Par   ← fast
```

---

## Climax: 223

Paanchon jurm theek. Build:

```
Build completed successfully (3074 jobs).   ← prop_30 GREEN
```

Clean audit:

```
COMPILED (olean) : 223  (95%)
```

prop_30 aur prop_35A green hue, aur unke peeche atka pura **prop_35→47 area/
Pythagoras cluster** khul gaya.

**Din ka safar:  198 → 199 → 215 → 223.**  (+25 lemmas)

---

## Moral of the story

Har bug ek **general transpiler galti** thi, kisi ek file ki nahi:

| # | Jurm | Fix | Kahaan |
|---|------|-----|--------|
| 1 | Nested-paren apply kat-na | greedy capture | `_ASSERT_BY` regex |
| 2 | Block = negation maan-na | `intro h` sirf `~` pe; eapply-block → conclude | block handler + helper |
| 3 | Explicit args phenk-na | args rakho → `apply … <;> assumption` | apply-head |
| 4 | `¬(A∨B)` khud todna | de Morgan leaves pre-emit | neg-block handler |
| 5 | Local helper na pehchaan-na | `auto using parnotmeet` → `conclude_def Par` | `auto`-mapping |

Ek bhi proof file haath se nahi chhui. Sab `geolean_transpile.py` mein.
**Faithful. General. Honest.**

> Agla target: prop_36, prop_39A, prop_44A, prop_48 — aur unke peeche 7 cascade.
> 11 lemmas door, 4 root-causes. 234/234 saamne hai.
