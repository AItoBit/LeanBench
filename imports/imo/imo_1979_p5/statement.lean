open Imo1979P5 in
/-- **IMO 1979, Problem 5.**  The real numbers `a` for which there exist non-negative
reals `x₁, …, x₅` with `∑ k x_k = a`, `∑ k³ x_k = a²` and `∑ k⁵ x_k = a³` are exactly
`0, 1, 4, 9, 16, 25`. -/
theorem candidate (a : ℝ) :
    Sols a ↔ a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 9 ∨ a = 16 ∨ a = 25 :=
