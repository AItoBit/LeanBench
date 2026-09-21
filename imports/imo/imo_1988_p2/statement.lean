/-- **IMO 1988, Problem 2, final answer.** The values of `n` for which *every* configuration as in
the problem admits an assignment of `0`/`1` making each `A i` carry exactly `n` zeros are exactly
the even ones. (The forward implication uses that configurations do exist for every `n`.) -/
theorem candidate (n : ℕ) : HasAssignment n ↔ Even n :=
