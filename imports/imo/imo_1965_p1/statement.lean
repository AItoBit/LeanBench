/-- **IMO 1965, Problem 1.** For `0 ≤ x ≤ 2π`, the inequality
`2 cos x ≤ |√(1 + sin 2x) − √(1 − sin 2x)| ≤ √2` holds precisely for `x ∈ [π/4, 7π/4]`. -/
theorem candidate {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2 * Real.pi) :
    (2 * Real.cos x ≤ |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))| ∧
      |Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))| ≤ Real.sqrt 2)
      ↔ x ∈ Set.Icc (Real.pi / 4) (7 * Real.pi / 4) :=
