/--
IMO 2018 Problem 2.

For every `n ≥ 3`, a cyclic real solution exists
if and only if `n` is divisible by `3`.
-/
theorem candidate
    (n : ℕ)
    (hn :
      3 ≤ n) :
    Admissible n ↔ 3 ∣ n :=
