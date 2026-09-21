/--
Formal numerical conclusion corresponding to IMO 2011 Problem 4.

If `W` satisfies the official insertion recurrence, then

    W(n) = 1 * 3 * 5 * ... * (2n-1).
-/
theorem candidate
    (W : ℕ → ℕ)
    (hzero :
      W 0 = 1)
    (hrec :
      ∀ n : ℕ,
        W (n + 1) =
          (2 * n + 1) * W n) :
    ∀ n : ℕ,
      W n =
        ∏ k ∈ Finset.range n,
          (2 * k + 1) :=
