/--
**IMO 2010 Problem 6 — final stabilization step.**

Once the valid-type argument has established `TypeStabilizes`,
there are `1 ≤ ℓ ≤ s` and `N` such that

    a n = a ℓ + a (n - ℓ)

for every `n ≥ N`.
-/
theorem candidate
    (a : ℕ → ℝ)
    (s : ℕ)
    (_hs : 0 < s)
    (_hpos : PositiveSequence a)
    (_hrec : MaxRecurrence a s)
    (hstab : TypeStabilizes a s) :
    ∃ ℓ N : ℕ,
      1 ≤ ℓ ∧
      ℓ ≤ s ∧
      ∀ n : ℕ,
        N ≤ n →
        a n = a ℓ + a (n - ℓ) :=
