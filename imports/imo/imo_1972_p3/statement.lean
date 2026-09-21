/-- **IMO 1972, Problem 3.**  `(2m)! (2n)!` is divisible by `m! n! (m+n)!`, i.e.
`(2m)!(2n)! / (m! n! (m+n)!)` is an integer. -/
theorem candidate (m n : ℕ) : (m ! * n ! * (m + n)!) ∣ ((2 * m)! * (2 * n)!) :=
