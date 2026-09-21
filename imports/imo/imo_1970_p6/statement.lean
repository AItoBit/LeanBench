theorem candidate (A T L1 L2 k : ℕ)
    (hk_pos : 0 < k)
    (hL1 : L1 = k * T)
    (hL2 : L2 = k * A)
    (h_ratio : 10 * L2 ≤ 7 * L1) :
    10 * A ≤ 7 * T :=
