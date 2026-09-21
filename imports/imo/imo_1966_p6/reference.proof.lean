by

  have habc : 0 < a * b * c := by positivity

  have hbc4 : 0 < b * c / 4 := by positivity
  have hac4 : 0 < a * c / 4 := by positivity
  have hab4 : 0 < a * b / 4 := by positivity

  have hX : 0 < f * (b - e) := by
    linarith

  have hY : 0 < d * (c - f) := by
    linarith

  have hZ : 0 < e * (a - d) := by
    linarith

  have hXY : 0 <
      f * (b - e) * (d * (c - f)) := by
    positivity

  have hlower₁ :
      (b * c / 4) * (a * c / 4)
        < (f * (b - e)) * (d * (c - f)) := by
    calc
      (b * c / 4) * (a * c / 4)
          < (f * (b - e)) * (a * c / 4) :=
        mul_lt_mul_of_pos_right h₁ hac4
      _ < (f * (b - e)) * (d * (c - f)) :=
        mul_lt_mul_of_pos_left h₂ hX

  have hlower :
      (b * c / 4) * (a * c / 4) * (a * b / 4)
        < (f * (b - e)) * (d * (c - f)) * (e * (a - d)) := by
    calc
      (b * c / 4) * (a * c / 4) * (a * b / 4)
          < (f * (b - e)) * (d * (c - f)) * (a * b / 4) :=
        mul_lt_mul_of_pos_right hlower₁ hab4
      _ < (f * (b - e)) * (d * (c - f)) * (e * (a - d)) :=
        mul_lt_mul_of_pos_left h₃ hXY

  have hu₁ : d * (a - d) ≤ a ^ 2 / 4 := by
    nlinarith [sq_nonneg (a - 2 * d)]

  have hu₂ : e * (b - e) ≤ b ^ 2 / 4 := by
    nlinarith [sq_nonneg (b - 2 * e)]

  have hu₃ : f * (c - f) ≤ c ^ 2 / 4 := by
    nlinarith [sq_nonneg (c - 2 * f)]

  have hU₁ : 0 ≤ d * (a - d) := by
    positivity

  have hU₂ : 0 ≤ e * (b - e) := by
    positivity

  have hU₃ : 0 ≤ f * (c - f) := by
    positivity

  have hA : 0 ≤ a ^ 2 / 4 := by positivity
  have hB : 0 ≤ b ^ 2 / 4 := by positivity
  have hAB : 0 ≤ (a ^ 2 / 4) * (b ^ 2 / 4) := by positivity

  have hupper :
      d * (a - d) * (e * (b - e)) * (f * (c - f))
        ≤ (a ^ 2 * b ^ 2 * c ^ 2) / 64 := by
    have h₁' :
        d * (a - d) * (e * (b - e))
          ≤ (a ^ 2 / 4) * (b ^ 2 / 4) := by
      calc
        d * (a - d) * (e * (b - e))
            ≤ (a ^ 2 / 4) * (e * (b - e)) :=
          mul_le_mul_of_nonneg_right hu₁ hU₂
        _ ≤ (a ^ 2 / 4) * (b ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hu₂ hA

    have h₂' :
        d * (a - d) * (e * (b - e)) * (f * (c - f))
          ≤ ((a ^ 2 / 4) * (b ^ 2 / 4)) * (f * (c - f)) := by
      exact mul_le_mul_of_nonneg_right h₁' hU₃

    have h₃' :
        ((a ^ 2 / 4) * (b ^ 2 / 4)) * (f * (c - f))
          ≤ ((a ^ 2 / 4) * (b ^ 2 / 4)) * (c ^ 2 / 4) := by
      exact mul_le_mul_of_nonneg_left hu₃ hAB

    calc
      d * (a - d) * (e * (b - e)) * (f * (c - f))
          ≤ ((a ^ 2 / 4) * (b ^ 2 / 4)) * (f * (c - f)) := h₂'
      _ ≤ ((a ^ 2 / 4) * (b ^ 2 / 4)) * (c ^ 2 / 4) := h₃'
      _ = (a ^ 2 * b ^ 2 * c ^ 2) / 64 := by ring

  have hlower' :
      (a ^ 2 * b ^ 2 * c ^ 2) / 64
        < d * (a - d) * (e * (b - e)) * (f * (c - f)) := by
    calc
      (a ^ 2 * b ^ 2 * c ^ 2) / 64
          = (b * c / 4) * (a * c / 4) * (a * b / 4) := by ring
      _ < (f * (b - e)) * (d * (c - f)) * (e * (a - d)) := hlower
      _ = d * (a - d) * (e * (b - e)) * (f * (c - f)) := by ring

  linarith
