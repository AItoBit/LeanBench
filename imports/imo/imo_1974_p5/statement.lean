/-- **IMO 1974, Problem 5.** The set of values attained by
`S = a/(a+b+d) + b/(a+b+c) + c/(b+c+d) + d/(a+c+d)` for positive reals `a, b, c, d`
is exactly the open interval `(1, 2)`. -/
theorem candidate :
    {s : ℝ | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ S a b c d = s} = Set.Ioo 1 2 :=
