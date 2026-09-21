/-- **IMO 1973, Problem 5.** -/
theorem candidate (G : Set (ℝ → ℝ))
    (hform : ∀ f ∈ G, ∃ a b : ℝ, a ≠ 0 ∧ ∀ x, f x = a * x + b)
    (hcomp : ∀ f ∈ G, ∀ g ∈ G, (f ∘ g) ∈ G)
    (hinv : ∀ f ∈ G, ∃ g ∈ G, (∀ x, f (g x) = x) ∧ (∀ x, g (f x) = x))
    (hfix : ∀ f ∈ G, ∃ x, f x = x) :
    ∃ k : ℝ, ∀ f ∈ G, f k = k :=
