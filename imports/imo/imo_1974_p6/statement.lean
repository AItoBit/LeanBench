/-- **IMO 1974, Problem 6.**  Let `P` be a non-constant polynomial with integer
coefficients and let `n(P)` be the number of distinct integers `k` with `P(k)^2 = 1`.
Then `n(P) ≤ deg(P) + 2`. -/
theorem candidate (P : Polynomial ℤ) (hP : 0 < P.natDegree) :
    {k : ℤ | (P.eval k) ^ 2 = 1}.ncard ≤ P.natDegree + 2 :=
