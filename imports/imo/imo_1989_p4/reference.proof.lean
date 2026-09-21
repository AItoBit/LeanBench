by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  -- the three squared horizontal offsets
  have e1 : (p - q) ^ 2 = 4 * (a * b) := sq_of_tangent hAB
  have e2 : (p - r) ^ 2 = 4 * (a * h) := sq_of_tangent hAP
  have e3 : (r - q) ^ 2 = 4 * (h * b) := sq_of_tangent hBP
  -- the middle offset is the product of the two absolute offsets
  have habs : (p - r) * (r - q) = 4 * (h * (Real.sqrt a * Real.sqrt b)) := by
    have hmul : ((p - r) * (r - q)) ^ 2 = (4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2 := by
      have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
      have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
      calc ((p - r) * (r - q)) ^ 2 = (p - r) ^ 2 * (r - q) ^ 2 := by ring
        _ = (4 * (a * h)) * (4 * (h * b)) := by rw [e2, e3]
        _ = 16 * (h ^ 2 * (Real.sqrt a ^ 2 * Real.sqrt b ^ 2)) := by rw [hA, hB]; ring
        _ = (4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2 := by ring
    have hnn : (0 : ℝ) ≤ 4 * (h * (Real.sqrt a * Real.sqrt b)) := by positivity
    calc (p - r) * (r - q) = Real.sqrt (((p - r) * (r - q)) ^ 2) := (Real.sqrt_sq hbet).symm
      _ = Real.sqrt ((4 * (h * (Real.sqrt a * Real.sqrt b))) ^ 2) := by rw [hmul]
      _ = 4 * (h * (Real.sqrt a * Real.sqrt b)) := Real.sqrt_sq hnn
  -- combining: `ab = h (√a + √b)²`
  have hkey : a * b = h * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hexp : (p - q) ^ 2 = (p - r) ^ 2 + 2 * ((p - r) * (r - q)) + (r - q) ^ 2 := by ring
    rw [e1, e2, e3, habs] at hexp
    nlinarith [hexp, hA, hB]
  -- hence `√h (√a + √b) = √a √b`
  have hmain : Real.sqrt h * (Real.sqrt a + Real.sqrt b) = Real.sqrt a * Real.sqrt b := by
    have hsq : (Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2
        = (Real.sqrt a * Real.sqrt b) ^ 2 := by
      have hA : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
      have hB : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
      have hH : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
      calc (Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2
          = Real.sqrt h ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by ring
        _ = h * (Real.sqrt a + Real.sqrt b) ^ 2 := by rw [hH]
        _ = a * b := hkey.symm
        _ = (Real.sqrt a * Real.sqrt b) ^ 2 := by rw [mul_pow, hA, hB]
    have hnn1 : (0 : ℝ) ≤ Real.sqrt h * (Real.sqrt a + Real.sqrt b) := by positivity
    have hnn2 : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt b := by positivity
    calc Real.sqrt h * (Real.sqrt a + Real.sqrt b)
        = Real.sqrt ((Real.sqrt h * (Real.sqrt a + Real.sqrt b)) ^ 2) := (Real.sqrt_sq hnn1).symm
      _ = Real.sqrt ((Real.sqrt a * Real.sqrt b) ^ 2) := by rw [hsq]
      _ = Real.sqrt a * Real.sqrt b := Real.sqrt_sq hnn2
  rw [div_add_div _ _ hsa.ne' hsb.ne', eq_div_iff (by positivity), div_mul_eq_mul_div,
    div_eq_iff hsh.ne']
  linear_combination -hmain
