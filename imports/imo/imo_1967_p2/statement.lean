open Real

/--
Formalization of the algebraic conclusion.
After setting up the geometry, the volume of the tetrahedron is bounded by
`(x / 6) * (1 - x^2 / 4)`, where `x` is the length of edge AB and `0 < x ≤ 1`.
We prove that this is at most `1 / 8`, and that this inequality is equivalent
to `(1 - x) * (3 - x - x^2) ≥ 0` exactly as stated in the solution.
-/

theorem candidate (x : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) :
    (1 / 8 - (x / 6) * (1 - x^2 / 4) ≥ 0 ↔ (1 - x) * (3 - x - x^2) ≥ 0) ∧
    (x / 6) * (1 - x^2 / 4) ≤ 1 / 8 :=
