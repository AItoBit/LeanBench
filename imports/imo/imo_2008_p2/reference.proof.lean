by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => tripleOf ((n : ℚ) + 2)) ?_ ?_
  · intro m n hmn
    simp only [tripleOf, Prod.mk.injEq] at hmn
    have h : ((m : ℚ) + 2) ^ 2 = ((n : ℚ) + 2) ^ 2 := by linarith [hmn.1]
    have hm : (0 : ℚ) ≤ (m : ℚ) + 2 := by positivity
    have hn : (0 : ℚ) ≤ (n : ℚ) + 2 := by positivity
    have hmn' : (m : ℚ) = (n : ℚ) := by nlinarith
    exact_mod_cast hmn'
  · intro n
    refine tripleOf_mem _ ?_ ?_ <;>
      · intro h
        have : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        linarith
