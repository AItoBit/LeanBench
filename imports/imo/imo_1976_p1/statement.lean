/-- The value `8 * √2` is attained: an explicit convex quadrilateral of area `32` with
`AB + BD + DC = 16` and `AC = 8 * √2`. -/
theorem candidate :
    ∃ A B C D : Pt, ConvexCCW A B C D ∧ |area A B C D| = 32 ∧
      dist A B + dist B D + dist D C = 16 ∧ dist A C = 8 * Real.sqrt 2 :=
