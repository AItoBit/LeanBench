/-- **IMO 1981, Problem 3.** The maximum value of `m² + n²` for integers
`m, n ∈ {1, 2, …, 1981}` satisfying `(n² - mn - m²)² = 1` is `3524578 = 987² + 1597²`. -/
theorem candidate :
    IsGreatest {s : ℤ | ∃ m n : ℤ, 1 ≤ m ∧ m ≤ 1981 ∧ 1 ≤ n ∧ n ≤ 1981 ∧
      (n ^ 2 - m * n - m ^ 2) ^ 2 = 1 ∧ s = m ^ 2 + n ^ 2} 3524578 :=
