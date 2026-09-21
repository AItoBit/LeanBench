theorem candidate
    (hbase_forward :
      ∀ k : ℕ,
        Valid 3 k →
        k = 0 ∨ k = 1 ∨ k = 3)

    (h0 :
      Valid 3 0)

    (h1 :
      Valid 3 1)

    (h3 :
      Valid 3 3)

    (reduce :
      ∀ n k : ℕ,
        4 ≤ n →
        Valid n k →
        Valid (n - 1) k)

    (lift :
      ∀ n k : ℕ,
        3 ≤ n →
        Valid n k →
        Valid (n + 1) k) :

    ∀ n k : ℕ,
      3 ≤ n →
      (Valid n k ↔
       (k = 0 ∨ k = 1 ∨ k = 3)) :=
