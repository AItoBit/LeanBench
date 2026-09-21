/--
Once the case analysis on configurations has established

    F 1 = 1

and

    F(n+1) = 2F(n) + (n+1)2^n,

the expected number of operations is

    n(n+1)/4.
-/
theorem candidate
    (F : ℕ → ℕ)
    (hbase :
      F 1 = 1)
    (hrec :
      ∀ n : ℕ,
        1 ≤ n →
        F (n + 1) =
          2 * F n +
          (n + 1) * 2 ^ n)
    (n : ℕ)
    (hn : 0 < n) :
    (F n : ℚ) /
        ((2 ^ n : ℕ) : ℚ)
      =
    (n : ℚ) * (n + 1 : ℚ) / 4 :=
