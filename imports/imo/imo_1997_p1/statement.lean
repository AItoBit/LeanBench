/-- The `180°` rotation about a point with integer coordinates preserves colours, away from the
grid lines. The hypotheses `⌈x⌉ = ⌊x⌋ + 1` say exactly that the coordinate is not an integer;
the excluded set is a null set, so this is all the symmetry argument of part (a) needs. -/
theorem candidate (p : ℝ × ℝ) (c₁ c₂ : ℤ)
    (h1 : ⌈p.1⌉ = ⌊p.1⌋ + 1) (h2 : ⌈p.2⌉ = ⌊p.2⌋ + 1) :
    IsBlack (2 * (c₁ : ℝ) - p.1, 2 * (c₂ : ℝ) - p.2) ↔ IsBlack p :=
