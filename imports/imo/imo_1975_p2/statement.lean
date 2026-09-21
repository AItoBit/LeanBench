/-- **IMO 1975, Problem 2.**

Let `a 1, a 2, a 3, …` be an infinite increasing sequence of positive integers.
Then for every `p ≥ 1` there are infinitely many `a m` which can be written in the form
`a m = x * a p + y * a q` with `x`, `y` positive integers and `q > p`.

The sequence is modelled as a function `a : ℕ → ℕ` which is strictly increasing and takes
positive values.  The conclusion says that the set of indices `m` for which such a
representation exists is infinite (equivalently, since `a` is injective, that infinitely
many terms `a m` are of that form).

The hypothesis `1 ≤ p` is part of the original statement (the sequence is indexed starting
from `1`); it is not needed for the proof. -/
theorem candidate (a : ℕ → ℕ) (hmono : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℕ) (hp : 1 ≤ p) :
    {m : ℕ | ∃ x y q : ℕ, 0 < x ∧ 0 < y ∧ p < q ∧ a m = x * a p + y * a q}.Infinite :=
