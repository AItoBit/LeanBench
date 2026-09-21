/-- The core algebraic reduction of the divisibility problem shown in the solution. 
    This states that solving the problem is precisely equivalent to showing divisibility 
    between our newly simplified numerator and denominator forms. -/
theorem candidate (m k : ℤ) (n : ℕ) :
    (∏ i ∈ range n, c ((i : ℤ) + 1)) ∣ (∏ i ∈ range n, (c (m + (i : ℤ) + 1) - c k)) ↔
    ((n.factorial : ℤ) * ((n + 1).factorial : ℤ)) ∣
    ((∏ i ∈ range n, (m + (i : ℤ) + 1 - k)) * (∏ i ∈ range n, (m + (i : ℤ) + 1 + k + 1))) :=
