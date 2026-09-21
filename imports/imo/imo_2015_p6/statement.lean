/--
The source eventually supplies `v`, `N`, and `w`.

Taking

    b = v + 1

and increasing `N` to `N+1` if necessary gives positive
integers `b,N₀` satisfying the required bound.
-/
theorem candidate
    (a w : ℕ → ℤ)
    (v : ℤ)
    (N : ℕ)
    (hv0 :
      0 ≤ v)
    (hv2014 :
      v ≤ 2014)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - (v + 1) =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧
        w j ≤ (2014 - v) * v) :
    ∃ b : ℤ,
      ∃ N₀ : ℕ,
        0 < b ∧
        0 < N₀ ∧
        ∀ m n : ℕ,
          N₀ ≤ m →
          m < n →
          abs
              (BlockDeviation
                a
                b
                m
                n)
            ≤
          (1007 : ℤ) ^ 2 :=
