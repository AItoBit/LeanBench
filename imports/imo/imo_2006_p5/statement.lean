/-- **IMO 2006, Problem 5**, set version: there are at most `n` integers `t` with `Q(t) = t`. -/
theorem candidate {P : ℤ[X]} (hP : 1 < P.natDegree) {k : ℕ} (hk : 0 < k) :
    {t : ℤ | (iterComp P k).eval t = t}.ncard ≤ P.natDegree :=
