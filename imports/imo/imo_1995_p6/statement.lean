open Finset IMO1995P6 in
/-- **IMO 1995, Problem 6.**  For an odd prime `p`, the number of `p`-element subsets
of `{1, 2, …, 2p}` whose elements sum to a multiple of `p` equals
`(binom(2p, p) - 2)/p + 2`. -/
theorem candidate (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    (((Finset.Icc 1 (2 * p)).powerset.filter
        (fun A => A.card = p ∧ p ∣ ∑ x ∈ A, x)).card)
      = ((2 * p).choose p - 2) / p + 2 :=
