/--
Consecutive values cannot be equal.

This is Lemma 1 of the source solution.
--/
theorem candidate
    (g : ℕ → ℕ)
    (hgood : Good g) :
    ∀ n : ℕ,
      g n ≠ g (n + 1) :=
