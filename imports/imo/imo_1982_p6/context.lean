namespace Imo1982P6

variable {P : Type*} [PseudoMetricSpace P]

/-- The length of the portion of the polygonal path `A` between indices `j` and
`k`. -/
noncomputable def plen (A : ℕ → P) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j k, dist (A i) (A (i + 1))
