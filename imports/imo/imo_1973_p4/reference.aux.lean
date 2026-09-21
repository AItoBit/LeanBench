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

/-- **The reflection step.**  For `A = (0,0)` and `B = (s,0)`, among all points
`X = (x, t)` on a fixed horizontal line, `AX + BX` is minimal at the midpoint
`(s/2, t)`.  (Reflect `B` in the line: the sum becomes `AX + XB'`, minimised on
the segment `AB'`, whose intersection with the line is exactly `(s/2, t)`.) -/
theorem dist_sum_min_on_line (s t x : ℝ) :
    dist (pt 0 0) (pt (s / 2) t) + dist (pt s 0) (pt (s / 2) t)
      ≤ dist (pt 0 0) (pt x t) + dist (pt s 0) (pt x t) := by
  have e1 : dist (pt 0 0) (pt (s / 2) t) = Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  have e5 : dist (pt s 0) (pt (s / 2) t) = Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  have e3 : dist (pt 0 0) (pt s (2 * t)) = Real.sqrt (s ^ 2 + 4 * t ^ 2) := by
    rw [dist_pt]; congr 1; ring
  -- reflecting `B = (s, 0)` in the line `y = t` gives `B' = (s, 2t)`
  have e4 : dist (pt s 0) (pt x t) = dist (pt s (2 * t)) (pt x t) := by
    rw [dist_pt, dist_pt]; congr 1; ring
  have h4 : Real.sqrt (s ^ 2 + 4 * t ^ 2) = 2 * Real.sqrt ((s / 2) ^ 2 + t ^ 2) := by
    rw [show s ^ 2 + 4 * t ^ 2 = 2 ^ 2 * ((s / 2) ^ 2 + t ^ 2) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  calc dist (pt 0 0) (pt (s / 2) t) + dist (pt s 0) (pt (s / 2) t)
      = dist (pt 0 0) (pt s (2 * t)) := by rw [e1, e5, e3, h4]; ring
    _ ≤ dist (pt 0 0) (pt x t) + dist (pt x t) (pt s (2 * t)) := dist_triangle _ _ _
    _ = dist (pt 0 0) (pt x t) + dist (pt s 0) (pt x t) := by
        rw [dist_comm (pt x t) (pt s (2 * t)), ← e4]

/-- **The length of the proposed path.**  With `E = (s/2, h/2)` the midpoint of
`CD` and `F` the point of `EB` at distance `h/2 = (√3/4) s` from `B`, the path
`A → E → F` has length `AE + (BE - h/2) = (√7/2 - √3/4) s`. -/
theorem path_length (s : ℝ) (hs : 0 ≤ s) :
    dist (pt 0 0) (pt (s / 2) (Real.sqrt 3 / 4 * s))
      + dist (pt s 0) (pt (s / 2) (Real.sqrt 3 / 4 * s))
      - Real.sqrt 3 / 4 * s
    = (Real.sqrt 7 / 2 - Real.sqrt 3 / 4) * s := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hnn : (0:ℝ) ≤ Real.sqrt 7 / 4 * s := mul_nonneg (by positivity) hs
  have e1 : dist (pt 0 0) (pt (s / 2) (Real.sqrt 3 / 4 * s)) = Real.sqrt 7 / 4 * s := by
    rw [dist_pt, show (0 - s / 2) ^ 2 + (0 - Real.sqrt 3 / 4 * s) ^ 2
        = (Real.sqrt 7 / 4 * s) ^ 2 from by
      linear_combination (s ^ 2 / 16) * h3 - (s ^ 2 / 16) * h7]
    exact Real.sqrt_sq hnn
  have e2 : dist (pt s 0) (pt (s / 2) (Real.sqrt 3 / 4 * s)) = Real.sqrt 7 / 4 * s := by
    rw [dist_pt, show (s - s / 2) ^ 2 + (0 - Real.sqrt 3 / 4 * s) ^ 2
        = (Real.sqrt 7 / 4 * s) ^ 2 from by
      linear_combination (s ^ 2 / 16) * h3 - (s ^ 2 / 16) * h7]
    exact Real.sqrt_sq hnn
  rw [e1, e2]
  ring
