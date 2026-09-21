by
  intro hdvd
  have hS : ((S n : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff (S n) 5).2 hdvd
  have hA : ((A n : ℤ) : ZMod 5) = 0 := by rw [← key n, hS, mul_zero]
  have hpell : ((A n : ℤ) : ZMod 5) ^ 2 - 2 * ((B n : ℤ) : ZMod 5) ^ 2 = -1 := by
    have h := congrArg (fun x : ℤ => ((x : ZMod 5))) (pell n)
    push_cast at h
    simpa using h
  rw [hA] at hpell
  have hno : ∀ b : ZMod 5, (0 : ZMod 5) ^ 2 - 2 * b ^ 2 ≠ -1 := by decide
  exact hno _ hpell
