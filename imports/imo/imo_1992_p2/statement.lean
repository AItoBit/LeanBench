theorem candidate (f : ℝ → ℝ) :
    (∀ x y : ℝ, f (x ^ 2 + f y) = y + (f x) ^ 2) ↔ ∀ x, f x = x :=
