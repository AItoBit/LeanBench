/--
Complete classification of IMO 2015 Problem 5.
-/
theorem candidate
    (f : ℝ → ℝ) :
    FunctionalEquation f ↔
      (∀ x : ℝ, f x = x) ∨
      (∀ x : ℝ, f x = 2 - x) :=
