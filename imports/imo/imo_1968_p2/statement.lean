theorem candidate (x P : ℤ)
    (hP_le_x : P ≤ x)
    (hP_nonneg : 0 ≤ P)
    (h_eq : P = x^2 - 10 * x - 22) :
    x = 12 ∧ P = 2 :=
