-- The `List` type, `List.length` function, and `List.append` operator (++)
-- are part of Lean's core library, so no external imports like Mathlib are needed.

-- We open the `List` namespace to allow using `length`, `nil`, `cons`, and `append`
-- directly without the `List.` prefix.
open List

theorem length_app {A : Type} (l l' : List A) : length (l ++ l') = length l + length l' := by
  -- The proof proceeds by induction on the first list `l`.
  induction l with
  | nil =>
    -- Base case: `l` is the empty list `[]`.
    -- The goal is `length ([] ++ l') = length [] + length l'`.

    -- `[] ++ l'` simplifies to `l'` by the definition of list concatenation (`List.append_nil_left_eq`).
    -- `length []` simplifies to `0` by the definition of list length (`List.length_nil`).
    -- `0 + length l'` simplifies to `length l'` by the property of natural numbers (`Nat.zero_add`).
    -- Applying these simplifications, the goal becomes `length l' = length l'`, which is true by reflexivity.
    simp only [append_nil_left_eq, length_nil, Nat.zero_add]
  | cons a l_rest ih =>
    -- Inductive step: `l` is `a :: l_rest` (a non-empty list).
    -- The inductive hypothesis `ih` states: `length (l_rest ++ l') = length l_rest + length l'`.
    -- The goal is `length ((a :: l_rest) ++ l') = length (a :: l_rest) + length l'`.

    -- Step 1: Simplify `(a :: l_rest) ++ l'`.
    -- By definition of list concatenation (`List.append_cons`), `(a :: l_rest) ++ l'`
    -- simplifies to `a :: (l_rest ++ l')`.
    rw [append_cons]

    -- The goal is now `length (a :: (l_rest ++ l')) = length (a :: l_rest) + length l'`.

    -- Step 2: Simplify `length (a :: (l_rest ++ l'))`.
    -- By definition of list length (`List.length_cons`), `length (a :: X)`
    -- simplifies to `1 + length X`. Here, `X` is `l_rest ++ l'`.
    rw [length_cons]

    -- The goal is now `1 + length (l_rest ++ l') = length (a :: l_rest) + length l'`.

    -- Step 3: Simplify `length (a :: l_rest)` on the right-hand side.
    -- By `List.length_cons` again, `length (a :: l_rest)`
    -- simplifies to `1 + length l_rest`.
    rw [length_cons (a := a) (l := l_rest)] -- We can specify `a` and `l` for clarity,
                                            -- though Lean usually infers them.

    -- The goal is now `1 + length (l_rest ++ l') = (1 + length l_rest) + length l'`.

    -- Step 4: Apply the inductive hypothesis `ih`.
    -- The hypothesis `ih` is `length (l_rest ++ l') = length l_rest + length l'`.
    -- We substitute this into the left-hand side of the goal.
    rw [ih]

    -- The goal is now `1 + (length l_rest + length l') = (1 + length l_rest) + length l'`.

    -- Step 5: This equality is an instance of associativity of addition for natural numbers.
    -- `(X + Y) + Z = X + (Y + Z)` is `Nat.add_assoc`.
    rw [Nat.add_assoc]
    -- The proof is complete.
