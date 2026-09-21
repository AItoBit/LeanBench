by
  have hpi := Real.pi_pos
  -- nondegeneracy of the triangle
  have hAB : A ≠ B := by rintro rfl; rw [angle_self_left] at hA; linarith
  have hAC : A ≠ C := by rintro rfl; rw [angle_self_right] at hA; linarith
  have hBC : B ≠ C := by rintro rfl; rw [angle_self_of_ne hAB.symm] at hA; linarith
  have hnc1 : ¬ Collinear ℝ ({B, A, C} : Set Pt) := by
    intro h
    rcases collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.1 h with h | h | h | h
    · exact hAB h.symm
    · exact hAC h.symm
    · rw [hA] at h; linarith
    · rw [hA] at h; linarith
  have hnc2 : ¬ Collinear ℝ ({A, B, C} : Set Pt) := by rwa [Set.insert_comm] at hnc1
  have hnc3 : ¬ Collinear ℝ ({B, C, A} : Set Pt) := by
    rwa [show ({B, C, A} : Set Pt) = {B, A, C} by rw [Set.pair_comm]]
  -- the bisected angle at `A`
  have hsplitA : ∠ B A X + ∠ X A C = ∠ B A C := angle_add_of_ne_of_ne hAB hAC hX
  have hBAX : ∠ B A X = π / 6 := by rw [hA, hAX] at hsplitA; rw [hAX]; linarith
  -- `X ≠ B` and `Y ≠ A`
  have hXB : X ≠ B := by rintro rfl; rw [angle_self_of_ne hAB.symm] at hBAX; linarith
  have hABCpos : 0 < ∠ A B C := angle_pos_of_not_collinear hnc2
  have hYA : Y ≠ A := by
    rintro rfl
    rw [angle_self_of_ne hAB] at hBY
    linarith
  -- the bisected angle at `B`
  set x := ∠ A B Y with hxdef
  have hsplitB : ∠ A B Y + ∠ Y B C = ∠ A B C := angle_add_of_ne_of_ne hAB.symm hBC hY
  have hABC : ∠ A B C = 2 * x := by rw [← hsplitB, ← hxdef, ← hBY]; ring
  -- the angles of the triangle at `B` and `C`
  have hsumABC : ∠ A B C + ∠ B C A + ∠ C A B = π := angle_add_angle_add_angle_eq_pi C hAB.symm
  have hBCApos : 0 < ∠ B C A := angle_pos_of_not_collinear hnc3
  have hCAB : ∠ C A B = π / 3 := by rw [angle_comm]; exact hA
  have hx0 : 0 < x := by linarith
  have hx3 : x < π / 3 := by linarith
  -- the third angle of triangle `ABX`
  have hABX : ∠ A B X = 2 * x := by rw [hX.angle_eq_right A hXB, hABC]
  have htri1 : ∠ A B X + ∠ B X A + ∠ X A B = π := angle_add_angle_add_angle_eq_pi X hAB.symm
  have hAXB : ∠ A X B = 5 * π / 6 - 2 * x := by
    rw [angle_comm]
    rw [hABX, angle_comm X A B, hBAX] at htri1
    linarith
  -- the third angle of triangle `ABY`
  have hBAY : ∠ B A Y = π / 3 := by rw [hY.angle_eq_right B hYA, hA]
  have htri2 : ∠ A B Y + ∠ B Y A + ∠ Y A B = π := angle_add_angle_add_angle_eq_pi Y hAB.symm
  have hAYB : ∠ A Y B = 2 * π / 3 - x := by
    rw [angle_comm]
    rw [angle_comm Y A B, hBAY, ← hxdef] at htri2
    linarith
  -- the law of sines in triangles `ABX` and `ABY`
  have hc : 0 < dist A B := dist_pos.2 hAB
  have law1 : sin (5 * π / 6 - 2 * x) * dist B X = sin (π / 6) * dist A B := by
    have := law_sin A X B
    rwa [hAXB, hBAX, dist_comm X B, dist_comm B A] at this
  have law2 : sin (2 * π / 3 - x) * dist Y B = sin (π / 3) * dist A B := by
    have := law_sin A Y B
    rwa [hAYB, hBAY, dist_comm B A] at this
  have law3 : sin (2 * π / 3 - x) * dist A Y = sin x * dist A B := by
    have := law_sin B Y A
    rwa [angle_comm B Y A, hAYB, ← hxdef, dist_comm Y A] at this
  -- the resulting trigonometric equation
  have hzero : sin (5 * π / 6 - 2 * x) * sin (2 * π / 3 - x) + sin (π / 6) * sin (2 * π / 3 - x)
      - (sin x + sin (π / 3)) * sin (5 * π / 6 - 2 * x) = 0 := by
    have hmul : dist A B * (sin (5 * π / 6 - 2 * x) * sin (2 * π / 3 - x)
        + sin (π / 6) * sin (2 * π / 3 - x)
        - (sin x + sin (π / 3)) * sin (5 * π / 6 - 2 * x)) = 0 := by
      linear_combination (sin (5 * π / 6 - 2 * x) * sin (2 * π / 3 - x)) * hsum
        - sin (2 * π / 3 - x) * law1 + sin (5 * π / 6 - 2 * x) * law3
        + sin (5 * π / 6 - 2 * x) * law2
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd h hc.ne'
    · exact h
  rw [trig_factorization] at hzero
  -- solve the equation
  have hs : 0 < sin (x / 2 + π / 6) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> nlinarith
  have hcos : 0 < 2 * cos x - 1 := by
    have h1 : cos (π / 3) < cos x :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hx3
    rw [Real.cos_pi_div_three] at h1
    linarith
  have hzero' : cos (3 * x / 2 + π / 6) = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hs.ne'
      · exact h
    · linarith
  have hsol : 3 * x / 2 + π / 6 = π / 2 := by
    refine Real.injOn_cos ⟨by positivity, by linarith⟩ ⟨by positivity, by linarith⟩ ?_
    rw [hzero', Real.cos_pi_div_two]
  rw [hABC]
  linarith
