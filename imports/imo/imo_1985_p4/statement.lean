theorem candidate (a b c d x y z : ℕ)
    (hx : a * b = x^2)
    (hy : c * d = y^2)
    (hz : x * y = z^2) :
    a * b * c * d = z^4 :=
