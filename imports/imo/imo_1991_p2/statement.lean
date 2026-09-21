/--
IMO 1991 Problem 2.

`a 0, ..., a (k-1)` list exactly the positive integers
less than `n` that are coprime to `n`.

Their successive differences equal the positive integer `d`.
-/
theorem candidate
    (n k d : ℕ)
    (a : ℕ → ℕ)
    (hn : 6 < n)
    (hd : 0 < d)
    (hset :
      ∀ r : ℕ,
        (0 < r ∧ r < n ∧ Nat.Coprime r n) ↔
          ∃ i : ℕ, i < k ∧ a i = r)
    (hstep :
      ∀ i : ℕ, i + 1 < k →
        a (i + 1) = a i + d) :
    Nat.Prime n ∨ ∃ e : ℕ, n = 2 ^ e :=
