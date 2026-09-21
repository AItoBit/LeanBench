/-- **IMO 1981, Problem 4 (b).** For `n > 2`, there is exactly one set of `n` consecutive positive
integers with the stated property precisely when `n = 4`. -/
theorem candidate (n : ℕ) (hn : 2 < n) : (∃! m, ConsecLcmProp n m) ↔ n = 4 :=
