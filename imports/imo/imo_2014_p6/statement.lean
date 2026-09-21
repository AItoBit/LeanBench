/--
The same argument without mentioning real square roots:

    n ≤ k².

This is exactly equivalent to the numerical conclusion
needed by the olympiad problem.
-/
theorem candidate
    {n k r : ℕ}
    (hkn :
      k ≤ n)
    (hblocked :
      n - k ≤ r)
    (hred :
      r ≤ k * (k - 1)) :
    n ≤ k * k :=
