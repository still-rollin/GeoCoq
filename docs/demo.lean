example (x y z : Nat) : (x + y) + z = x + (y + z) := by
  simp only [Nat.add_assoc]
