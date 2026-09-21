namespace Imo1973P1

/-- If `x, y ≥ 0` and `x + y ≤ π`, then `cos x + cos y ≥ 0`. -/
private lemma cos_add_cos_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ Real.pi) : 0 ≤ Real.cos x + Real.cos y := by
  rw [Real.cos_add_cos]
  have hpi := Real.pi_pos
  have h1 : 0 ≤ Real.cos ((x + y) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h2 : 0 ≤ Real.cos ((x - y) / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  exact mul_nonneg (by linarith) h2
