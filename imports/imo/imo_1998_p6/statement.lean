/-- The least possible value of `f 1998` is `120`. -/
theorem candidate : IsLeast {v : ℕ | ∃ f : ℕ → ℕ, Good f ∧ f 1998 = v} 120 :=
