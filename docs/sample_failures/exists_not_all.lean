theorem exists_not_all (P : Nat → Prop) : (∃ n, P n) → ¬ (∀ n, ¬ P n) := by
  intro h_exists_P -- Assume there exists an n such that P n
  intro h_forall_not_P -- Assume for all n, P n is false
  
  -- From 'h_exists_P', destructure it to get a specific n0 and a proof that P n0 holds
  cases h_exists_P with n0 h_P_n0
  
  -- We have 'n0 : Nat' and 'h_P_n0 : P n0'
  -- We also have 'h_forall_not_P : ∀ (n : Nat), ¬P n'
  
  -- Apply 'h_forall_not_P' to our specific 'n0' to get a proof that ¬P n0 holds
  let h_not_P_n0 := h_forall_not_P n0
  
  -- Now we have 'h_P_n0 : P n0' and 'h_not_P_n0 : ¬P n0' (which is P n0 → False)
  -- Applying 'h_not_P_n0' to 'h_P_n0' yields 'False', which is what we need for a contradiction.
  exact h_not_P_n0 h_P_n0
