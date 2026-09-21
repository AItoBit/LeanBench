/-- **IMO 1984, Problem 1 (Upper Bound via Solution A1)**:
$$yz + zx + xy - 2xyz \le \frac{1}{4} \cdot \frac{28}{27} = \frac{7}{27}.$$ -/
theorem candidate (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hsum : x + y + z = 1) :
    target x y z ≤ 7 / 27 :=
