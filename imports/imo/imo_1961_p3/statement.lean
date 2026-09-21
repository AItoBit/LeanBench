/-- **IMO 1961 Problem 3.** The solution set of `cos^n x - sin^n x = 1` for `n > 0`:
if `n` is even it is `{m * π | m : ℤ}`, and if `n` is odd it consists of the reals of the
form `2 * m * π` or `2 * m * π - π / 2` with `m : ℤ`. -/
theorem candidate (n : ℕ) (h₀ : n > 0) :
    {x : ℝ | Real.cos x ^ n - Real.sin x ^ n = 1} =
    (if Even n then {(m : ℝ) * π | m : ℤ} else
      {a : ℝ | ∃ m : ℤ, a = 2 * m * π ∨ a = 2 * m * π - π / 2}) :=
