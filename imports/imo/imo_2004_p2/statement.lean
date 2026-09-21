/-- **IMO 2004 P2.** -/
theorem candidate (f : ℝ[X]) :
    (∀ a b c : ℝ, a * b + b * c + c * a = 0 →
        f.eval (a - b) + f.eval (b - c) + f.eval (c - a) = 2 * f.eval (a + b + c))
      ↔ ∃ p q : ℝ, f = C p * X ^ 4 + C q * X ^ 2 :=
