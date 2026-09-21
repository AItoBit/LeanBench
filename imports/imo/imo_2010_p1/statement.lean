/--
**IMO 2010 Problem 1.**

The solutions are precisely the zero function and the constant
functions whose value lies in `[1,2)`.
-/
theorem candidate
    (f : ℝ → ℝ) :
    Good f ↔
      (∀ x : ℝ, f x = 0) ∨
      ∃ c : ℝ,
        1 ≤ c ∧
        c < 2 ∧
        ∀ x : ℝ, f x = c :=
