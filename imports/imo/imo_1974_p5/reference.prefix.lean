open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option pp.fullNames true

set_option pp.structureInstances true

set_option pp.coercions.types true

set_option pp.funBinderTypes true

set_option pp.letVarTypes true

set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1974P5

/-- The expression of IMO 1974 Problem 5. -/
noncomputable def S (a b c d : ℝ) : ℝ :=
  a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)

/-- For positive reals, `S a b c d > 1`. -/
theorem one_lt_S {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 < S a b c d := by
  have htot : 0 < a + b + c + d := by linarith
  have h1 : a / (a + b + c + d) < a / (a + b + d) := by
    apply div_lt_div_of_pos_left ha (by linarith) (by linarith)
  have h2 : b / (a + b + c + d) < b / (a + b + c) := by
    apply div_lt_div_of_pos_left hb (by linarith) (by linarith)
  have h3 : c / (a + b + c + d) < c / (b + c + d) := by
    apply div_lt_div_of_pos_left hc (by linarith) (by linarith)
  have h4 : d / (a + b + c + d) < d / (a + c + d) := by
    apply div_lt_div_of_pos_left hd (by linarith) (by linarith)
  have hsum : a / (a + b + c + d) + b / (a + b + c + d) + c / (a + b + c + d)
      + d / (a + b + c + d) = 1 := by
    field_simp
  unfold S
  linarith

/-- For positive reals, `S a b c d < 2`. -/
theorem S_lt_two {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    S a b c d < 2 := by
  have h1 : a / (a + b + d) < a / (a + b) := by
    apply div_lt_div_of_pos_left ha (by linarith) (by linarith)
  have h2 : b / (a + b + c) < b / (a + b) := by
    apply div_lt_div_of_pos_left hb (by linarith) (by linarith)
  have h3 : c / (b + c + d) < c / (c + d) := by
    apply div_lt_div_of_pos_left hc (by linarith) (by linarith)
  have h4 : d / (a + c + d) < d / (c + d) := by
    apply div_lt_div_of_pos_left hd (by linarith) (by linarith)
  have e1 : a / (a + b) + b / (a + b) = 1 := by
    field_simp
  have e2 : c / (c + d) + d / (c + d) = 1 := by
    field_simp
  unfold S
  linarith

/-- Solving `3 t / (2 t ^ 2 + 5 t + 2) = v` for `t ≥ 1`, for any `v ∈ (0, 1/3]`. -/
theorem exists_param {v : ℝ} (hv : 0 < v) (hv3 : v ≤ 1 / 3) :
    ∃ t : ℝ, 1 ≤ t ∧ 3 * t / (2 * t ^ 2 + 5 * t + 2) = v := by
  set m : ℝ := 3 / v - 5 with hm
  have h3v : (9 : ℝ) ≤ 3 / v := by
    rw [le_div_iff₀ hv]; linarith
  have hm4 : 4 ≤ m := by simp only [hm]; linarith
  set r : ℝ := Real.sqrt (m ^ 2 - 16) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = m ^ 2 - 16 := Real.sq_sqrt (by nlinarith)
  refine ⟨(m + r) / 4, by linarith, ?_⟩
  set t : ℝ := (m + r) / 4 with ht
  have ht1 : 1 ≤ t := by simp only [ht]; linarith
  have ht0 : 0 < t := by linarith
  have hquad : 2 * t ^ 2 - m * t + 2 = 0 := by
    simp only [ht]
    nlinarith [hrsq]
  have hmv : m + 5 = 3 / v := by simp only [hm]; ring
  have hden : 2 * t ^ 2 + 5 * t + 2 = (3 / v) * t := by
    rw [← hmv]; nlinarith [hquad]
  rw [hden]
  have htne : t ≠ 0 := ne_of_gt ht0
  have hvne : v ≠ 0 := ne_of_gt hv
  field_simp

/-- The construction giving values in `(1, 4/3]`. -/
theorem S_lower_family {t : ℝ} (ht : 0 < t) :
    S 1 t t 1 = 1 + 3 * t / (2 * t ^ 2 + 5 * t + 2) := by
  have h1 : (0 : ℝ) < t + 2 := by linarith
  have h2 : (0 : ℝ) < 2 * t + 1 := by linarith
  unfold S
  have e : (2 : ℝ) * t ^ 2 + 5 * t + 2 = (t + 2) * (2 * t + 1) := by ring
  rw [e]
  field_simp
  ring

/-- The construction giving values in `[4/3, 2)`. -/
theorem S_upper_family {t : ℝ} (ht : 0 < t) :
    S t 1 t 1 = 2 - 2 * (3 * t / (2 * t ^ 2 + 5 * t + 2)) := by
  have h1 : (0 : ℝ) < t + 2 := by linarith
  have h2 : (0 : ℝ) < 2 * t + 1 := by linarith
  unfold S
  have e : (2 : ℝ) * t ^ 2 + 5 * t + 2 = (t + 2) * (2 * t + 1) := by ring
  rw [e]
  field_simp
  ring
