/--
Expanded form of the IMO statement.

There is a list of exactly `k` positive integers and

    ∏ (1 + 1/m) =
      1 + (2^k - 1)/n.
-/
theorem candidate
    (k n : ℕ)
    (hk : 0 < k)
    (hn : 0 < n) :
    ∃ ms : List ℕ,
      ms.length = k ∧
      (∀ m ∈ ms, 0 < m) ∧
      (ms.map
          (fun m : ℕ =>
            (1 : ℚ) + 1 / (m : ℚ))).prod
        =
      1 +
        ((2 : ℚ) ^ k - 1) /
          (n : ℚ) :=
