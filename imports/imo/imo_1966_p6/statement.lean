/-- The algebraic contradiction underlying the geometry problem. -/
theorem candidate
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ a)
    (he₀ : 0 ≤ e) (he₁ : e ≤ b)
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ c)
    (h₁ : b * c / 4 < f * (b - e))
    (h₂ : a * c / 4 < d * (c - f))
    (h₃ : a * b / 4 < e * (a - d)) :
    False :=
