/--
**IMO 2005 P4.**

The only positive natural number coprime to every number

`2^n + 3^n + 6^n - 1`, for `n ≥ 1`,

is `1`.
-/
theorem candidate (k : ℕ) (hk : 0 < k) :
    (∀ n : ℕ, 1 ≤ n →
      Nat.Coprime k (2 ^ n + 3 ^ n + 6 ^ n - 1)) ↔
      k = 1 :=
