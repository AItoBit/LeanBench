theorem candidate
    (hbound :
      ∀ k n : ℕ,
        0 < k →
        0 < n →
        k.factorial = rhs n →
        n ≤ 5)
    (k n : ℕ)
    (hk : 0 < k)
    (hn : 0 < n) :
    k.factorial = rhs n
      ↔
    ((k = 1 ∧ n = 1)
      ∨
     (k = 3 ∧ n = 2)) :=
