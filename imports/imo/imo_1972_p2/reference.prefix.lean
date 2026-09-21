namespace Imo1972P2

/-- The point of the plane with coordinates `(x, y)`, as a complex number. -/
noncomputable def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] lemma pt_re (x y : ℝ) : (pt x y).re = x := by
  simp only [pt, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

@[simp] lemma pt_im (x y : ℝ) : (pt x y).im = y := by
  simp only [pt, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma dist_pt (x₁ y₁ x₂ y₂ : ℝ) :
    dist (pt x₁ y₁) (pt x₂ y₂) = Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) := by
  rw [Complex.dist_eq_re_im, pt_re, pt_re, pt_im, pt_im]

/-- **Every trapezoid symmetric about the `y`-axis is cyclic.**  The vertices
`(±a, h₀)` and `(±b, h₁)` lie on the circle centred at `(0, k)` with
`k = (b² + h₁² - a² - h₀²) / (2 (h₁ - h₀))`. -/
theorem trapezoid_cyclic (a b h₀ h₁ : ℝ) (hne : h₀ ≠ h₁) :
    ∃ (o : ℂ) (r : ℝ),
      dist (pt a h₀) o = r ∧ dist (pt (-a) h₀) o = r ∧
      dist (pt b h₁) o = r ∧ dist (pt (-b) h₁) o = r := by
  have hd : h₁ - h₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set k : ℝ := (b ^ 2 + h₁ ^ 2 - a ^ 2 - h₀ ^ 2) / (2 * (h₁ - h₀)) with hk
  refine ⟨pt 0 k, Real.sqrt (a ^ 2 + (h₀ - k) ^ 2), ?_, ?_, ?_, ?_⟩
  · rw [dist_pt]; congr 1; ring
  · rw [dist_pt]; congr 1; ring
  · rw [dist_pt]
    congr 1
    rw [hk]
    field_simp
    ring
  · rw [dist_pt]
    congr 1
    rw [hk]
    field_simp
    ring

/-- The horizontal line at height `t` meets the leg from `(a, 0)` to `(b, h)`
exactly at `(a + (b - a) * t / h, t)`. -/
theorem cut_mem_segment (a b h t : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hth : t ≤ h) :
    pt (a + (b - a) * t / h) t ∈ segment ℝ (pt a 0) (pt b h) := by
  have hC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  refine ⟨1 - t / h, t / h, ?_, div_nonneg ht0 hh.le, by ring, ?_⟩
  · have : t / h ≤ 1 := (div_le_one hh).mpr hth
    linarith
  · simp only [pt, Complex.real_smul]
    push_cast
    field_simp
    ring
