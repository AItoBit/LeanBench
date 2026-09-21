/--
This is the final construction from the PDF:

  h(x,y) = M (αx + βy)^d,

where αa + βb = 1.

At the primitive point p=(a,b), it evaluates to M.
-/
theorem candidate
    {p : ℤ × ℤ}
    (hp : Primitive p)
    (M : ℤ)
    (d : ℕ) :
    ∃ h : Poly,
      MvPolynomial.eval (pointVal p) h = M :=
