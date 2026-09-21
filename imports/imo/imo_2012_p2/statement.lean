/--
IMO 2012 Problem 2 after establishing the pointwise AM-GM estimate.

The assumption

    ∏ i<n-1, a(i+2) = 1

is exactly

    a₂ a₃ ... aₙ = 1.

The conclusion is

    n^n ≤
      (a₂+1)^2 (a₃+1)^3 ... (aₙ+1)^n.
-/
theorem candidate
    (a : ℕ → ℝ)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hpos :
      ∀ i ∈ Finset.range (n - 1),
        0 < a (i + 2))
    (hprod :
      (∏ i ∈ Finset.range (n - 1),
          a (i + 2))
        = 1)
    (hAMGM :
      ∀ i ∈ Finset.range (n - 1),
        coeff (i + 2) * a (i + 2)
          ≤
        (a (i + 2) + 1) ^ (i + 2)) :
    ((n : ℝ) ^ n)
      ≤
    ∏ i ∈ Finset.range (n - 1),
      (a (i + 2) + 1) ^ (i + 2) :=
