/-- **IMO 1990, Problem 2.**  For `n ≥ 3`, the smallest `k` such that every colouring of `k` of
the `2n-1` points is good is `n` if `3 ∤ 2n-1`, and `3 * ⌊(2n-1)/6⌋ + 1` if `3 ∣ 2n-1`. -/
theorem candidate (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {k | ∀ S : Finset (ZMod (2 * n - 1)), S.card = k → IsGood n S} (answer n) :=
