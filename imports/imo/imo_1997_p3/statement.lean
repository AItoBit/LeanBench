/-- **IMO 1997 P3.** -/
theorem candidate (n : ℕ) (x : List ℝ) (hlen : x.length = n)
    (hsum : |x.sum| = 1) (hbd : ∀ a ∈ x, |a| ≤ ((n : ℝ) + 1) / 2) :
    ∃ y : List ℝ, List.Perm y x ∧ |f y| ≤ ((n : ℝ) + 1) / 2 :=
