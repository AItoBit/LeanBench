/--
**IMO 2009 Problem 5.**

The functions satisfying the condition are exactly the identity function
on the positive integers.
-/
theorem candidate
    (f : ℕ → ℕ) :
    Good f ↔
      ∀ n : ℕ,
        0 < n →
        f n = n :=
