namespace IMO1995P4

open Real

/-- The constraints of the problem on a sequence `x : ℕ → ℝ`. -/
def Constraint (x : ℕ → ℝ) : Prop :=
  (∀ i ≤ 1995, 0 < x i) ∧ x 0 = x 1995 ∧
    ∀ i, 1 ≤ i → i ≤ 1995 → x (i - 1) + 2 / x (i - 1) = 2 * x i + 1 / x i

/-- The extremal sequence: `x i = 2 ^ (997 - i)` for `i ≤ 1994`, and `x 1995 = 2 ^ 997`. -/
noncomputable def witness : ℕ → ℝ :=
  fun i => if i ≤ 1994 then (2 : ℝ) ^ (997 - (i : ℤ)) else (2 : ℝ) ^ (997 : ℤ)
