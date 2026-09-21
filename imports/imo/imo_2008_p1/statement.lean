/-- **IMO 2008 P1.** Every one of the six points lies on the circle centred at the circumcentre
with squared radius `2R² + ⟨A,B⟩ + ⟨B,C⟩ + ⟨C,A⟩`. -/
theorem candidate (a1 a2 b1 b2 c1 c2 R : ℝ)
    (hA : a1 ^ 2 + a2 ^ 2 = R ^ 2) (hB : b1 ^ 2 + b2 ^ 2 = R ^ 2)
    (hC : c1 ^ 2 + c2 ^ 2 = R ^ 2)
    (p1 p2 : ℝ)
    (hp : OnCircleA a1 a2 b1 b2 c1 c2 p1 p2 ∨ OnCircleA b1 b2 c1 c2 a1 a2 p1 p2
        ∨ OnCircleA c1 c2 a1 a2 b1 b2 p1 p2) :
    p1 ^ 2 + p2 ^ 2
      = 2 * R ^ 2 + (a1 * b1 + a2 * b2) + (b1 * c1 + b2 * c2) + (c1 * a1 + c2 * a2) :=
