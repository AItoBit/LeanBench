/--
Formalization of the contest problem, following the given solution.
* `a`        = number of students who solved B and C but not A;
* `2*x - a`  = number who solved B only,  `x - a` = number who solved C only
  (`x` a positive integer and `a ≤ x`, so `x - a ≥ 0`);
* `2*y - 1`  = number who solved A, and `y` = number who solved only A.
The two stated conditions become `h_total` and `h_half`.  We prove that the
number of students who solved only problem B, namely `2*x - a`, is `6`.
No `sorry`, no `axiom` declarations: `omega` gives a kernel‑checkable
Presburger‑arithmetic proof. -/
theorem candidate (x y a : ℤ)
    (_hx : 0 < x) (_hy : 0 < y) (_ha : 0 < a)
    (_hxa : a ≤ x)                        -- i.e. `x - a ≥ 0`
    (_h_total : 2 * y - 1 + 3 * x - a = 25)
    (_h_half  : y = 3 * x - 2 * a) :
    2 * x - a = 6 :=
