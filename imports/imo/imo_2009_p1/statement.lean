/--
**IMO 2009 Problem 1.**

Zero-based formulation.

`a 0, ..., a (k-1)` are distinct integers in `{1, ..., n}` and

    n ∣ a i * (a (i+1) - 1)

for every consecutive pair.

Then

    n ∤ a (k-1) * (a 0 - 1).
-/
theorem candidate
    (n : ℤ)
    (k : ℕ)
    (a : ℕ → ℤ)
    (hn : 0 < n)
    (hk : 2 ≤ k)
    (hbound :
      ∀ i : ℕ,
        i < k →
          1 ≤ a i ∧ a i ≤ n)
    (hdistinct :
      ∀ i j : ℕ,
        i < k →
        j < k →
        i ≠ j →
        a i ≠ a j)
    (hchain :
      ∀ i : ℕ,
        i + 1 < k →
          n ∣ a i * (a (i + 1) - 1)) :
    ¬ n ∣ a (k - 1) * (a 0 - 1) :=
