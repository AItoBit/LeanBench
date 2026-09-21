/--
Formalization of the final algebraic deduction in the solution for IMO 1970 Problem 2.
It demonstrates how the strict inequality between the highest-degree terms' ratios
directly implies the strict inequality between the remainders' ratios.
-/
theorem candidate (An A_prev Bn B_prev xn_an xn_bn : ℝ)
    (hAn_ne : An ≠ 0) (hBn_ne : Bn ≠ 0)
    (hA : An = A_prev + xn_an)
    (hB : Bn = B_prev + xn_bn)
    (h_ineq : xn_an / An > xn_bn / Bn) :
    A_prev / An < B_prev / Bn :=
