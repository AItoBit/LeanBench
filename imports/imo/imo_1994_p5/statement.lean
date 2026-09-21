theorem candidate (x y : ℝ) (hx : x + 1 ≠ 0) (hy : y + 1 ≠ 0) :
    f (x + f y + x * f y) = y + f x + y * f x :=
