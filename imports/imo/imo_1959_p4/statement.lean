/-- Main Existence Theorem:
    For any given hypotenuse `c > 0`, there exist valid positive catheti `a` and `b`
    such that `a^2 + b^2 = c^2` and the median `c / 2` is the geometric mean of `a` and `b`. -/
theorem candidate (c : ℝ) (hc : 0 < c) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a^2 + b^2 = c^2 ∧ (c / 2)^2 = a * b :=
