/--
Let $a,b,c$ be real numbers. Given the equation for $\cos x$: $$a\cos^2x+b\cos x+c=0,$$ form a quadratic equation in $\cos{2x}$ whose roots are the same values of $x$. Compare the equations in $\cos x$ and $\cos{2x}$ for $a=4,b=2,c=-1$. -/
theorem imo_1959_p3 :
    ∃ f₀ f₁ f₂ : ℝ → ℝ → ℝ → ℝ,
      ∀ (a b c x : ℝ) (_h : a ≠ 0),
        f₀ a b c ≠ 0 ∧
          (a * Real.cos x ^ 2 + b * Real.cos x + c = 0 →
            f₀ a b c * Real.cos (2 * x) ^ 2 + f₁ a b c * Real.cos (2 * x) + f₂ a b c = 0) := by
  refine ⟨imo1959P3F₀, imo1959P3F₁, imo1959P3F₂, fun a b c x ha => ⟨?_, fun hx => ?_⟩⟩
  · simpa [imo1959P3F₀] using pow_ne_zero 2 ha
  · have h2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
    simp only [imo1959P3F₀, imo1959P3F₁, imo1959P3F₂, h2]
    linear_combination (4 * (a * Real.cos x ^ 2 - b * Real.cos x + c)) * hx
