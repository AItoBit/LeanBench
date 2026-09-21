/-- **IMO 1982, Problem 4 (a).**  A solution yields three pairwise distinct
solutions. -/
theorem imo1982_p4a (n : ℤ) (hn : 0 < n) (x y : ℤ)
    (h : x ^ 3 - 3 * x * y ^ 2 + y ^ 3 = n) :
    ∃ p q r : ℤ × ℤ, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
      p.1 ^ 3 - 3 * p.1 * p.2 ^ 2 + p.2 ^ 3 = n ∧
      q.1 ^ 3 - 3 * q.1 * q.2 ^ 2 + q.2 ^ 3 = n ∧
      r.1 ^ 3 - 3 * r.1 * r.2 ^ 2 + r.2 ^ 3 = n := by
  -- a solution of a positive `n` is not the zero pair
  have hxy : ¬ (x = 0 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩
    norm_num at h
    omega
  refine ⟨(x, y), (y - x, -x), (-y, x - y), ?_, ?_, ?_, h, ?_, ?_⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · intro hcon
    rw [Prod.mk.injEq] at hcon
    exact hxy ⟨by omega, by omega⟩
  · show (y - x) ^ 3 - 3 * (y - x) * (-x) ^ 2 + (-x) ^ 3 = n
    linear_combination h
  · show (-y) ^ 3 - 3 * (-y) * (x - y) ^ 2 + (x - y) ^ 3 = n
    linear_combination h
