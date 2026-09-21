namespace Imo1999P5

/-- The Euclidean inner product on `ℂ`. -/
noncomputable def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

theorem dot_comm (z w : ℂ) : dot z w = dot w z := by
  simp only [dot]; ring

theorem dot_self (z : ℂ) : dot z z = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rfl

theorem dot_sub_left (z w v : ℂ) : dot (z - w) v = dot z v - dot w v := by
  simp only [dot, Complex.sub_re, Complex.sub_im]; ring

theorem dot_real_smul (r : ℝ) (z w : ℂ) : dot ((r : ℂ) * z) w = r * dot z w := by
  simp only [dot, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem norm_sub_sq (Y Z : ℂ) : ‖Y - Z‖ ^ 2 = dot Y Y - 2 * dot Y Z + dot Z Z := by
  rw [← dot_self]
  simp only [dot, Complex.sub_re, Complex.sub_im]
  ring
