/--
This theorem reflects the exact structure of the supplied
solution:

* `lower_strategy` is Liu's geometric/doubling strategy;
* `upper_strategy` is Xiang's matching optimal response;
* `cap_sound` converts Xiang's strategy into an upper bound.

Hence the largest guaranteed length is exactly

    2^n / (2^(n+1)-1).
-/
theorem candidate
    (n : ℕ)

    (lower_strategy :
      LiuCanGuarantee
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1)))

    (upper_strategy :
      XiangCanCap
        n
        ((2 : ℝ) ^ n /
          ((2 : ℝ) ^ (n + 1) - 1)))

    (cap_sound :
      XiangCanCap
          n
          ((2 : ℝ) ^ n /
            ((2 : ℝ) ^ (n + 1) - 1)) →
      ∀ D : ℝ,
        LiuCanGuarantee n D →
        D ≤
          (2 : ℝ) ^ n /
            ((2 : ℝ) ^ (n + 1) - 1)) :

    IsLargestGuarantee
      LiuCanGuarantee
      n
      ((2 : ℝ) ^ n /
        ((2 : ℝ) ^ (n + 1) - 1)) :=
