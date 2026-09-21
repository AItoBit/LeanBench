/--
Once the p-adic portion of the source proof has established

    a(n+1) ∣ a(n)

for all sufficiently large `n`, the original conclusion
follows.
-/
theorem candidate
    (a : ℕ → ℕ)
    (hpos :
      ∀ n : ℕ,
        0 < a n)
    (N : ℕ)
    (hdiv :
      ∀ n : ℕ,
        N ≤ n →
        a (n + 1) ∣ a n) :
    ∃ M : ℕ,
      ∀ m : ℕ,
        M ≤ m →
        a m = a (m + 1) :=
