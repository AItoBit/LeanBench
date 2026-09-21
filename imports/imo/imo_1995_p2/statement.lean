theorem candidate (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * b * c = 1) :
    (1 : ℝ) / (a ^ 3 * (b + c)) + (1 : ℝ) / (b ^ 3 * (c + a)) +
        (1 : ℝ) / (c ^ 3 * (a + b)) ≥ (3 : ℝ) / 2 :=
