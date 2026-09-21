/-- **IMO 1981, Problem 2.** For `1 ≤ r ≤ n`, the arithmetic mean `F (n, r)` of the smallest
members of all `r`-element subsets of `{1, 2, …, n}` equals `(n + 1) / (r + 1)`. -/
theorem candidate (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (∑ S ∈ (Finset.Icc 1 n).powersetCard r, (smallest S : ℚ))
        / (((Finset.Icc 1 n).powersetCard r).card : ℚ)
      = ((n : ℚ) + 1) / ((r : ℚ) + 1) :=
