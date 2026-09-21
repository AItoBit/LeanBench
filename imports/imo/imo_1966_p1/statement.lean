theorem candidate (x y a : ℤ)
    (_hx : 0 < x) (_hy : 0 < y) (_ha : 0 < a)
    (_hxa : a ≤ x)                        -- i.e. `x - a ≥ 0`
    (_h_total : 2 * y - 1 + 3 * x - a = 25)
    (_h_half  : y = 3 * x - 2 * a) :
    2 * x - a = 6 :=
