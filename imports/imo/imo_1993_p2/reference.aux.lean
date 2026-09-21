/-- **Part (a).** `AB·CD = √2 · AC·BD`. -/
theorem part_a (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c))) :
    ‖(a - b) * (c - d)‖ = Real.sqrt 2 * ‖(a - c) * (b - d)‖ := by
  have key : (a - b) * (c - d) = -(1 + Complex.I) * ((a - d) * (b - c)) := by
    linear_combination hD
  have h1 : ‖(1 + Complex.I : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    norm_num
  rw [key, hD]
  simp only [norm_mul, norm_neg, h1, Complex.norm_I, one_mul]

/-- **Part (b), algebraic core.** The two tangent directions at `c` differ by a factor `i`. -/
theorem tangentDir_eq (a b c d : ℂ)
    (hD : (a - c) * (b - d) = -Complex.I * ((a - d) * (b - c)))
    (hac : c - a ≠ 0) (hbc : c - b ≠ 0) :
    tangentDir a c d = Complex.I * tangentDir b c d := by
  unfold tangentDir
  rw [← mul_div_assoc, div_eq_div_iff hac hbc]
  linear_combination (-(d - c) * Complex.I) * hD
    + ((d - c) * (a - d) * (b - c)) * Complex.I_sq
