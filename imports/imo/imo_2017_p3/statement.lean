/--
Specialization to 20000 successful 200-round blocks.
-/
theorem candidate
    (D : ℕ → ℝ)
    (h :
      ∀ n : ℕ,
        D n + (1 : ℝ) / 2 < D (n + 1)) :
    D 0 + 10000 < D 20000 :=
