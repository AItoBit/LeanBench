by
  have hcov : sides A B C ⊆ S ∪ T := by rw [hunion]
  -- the nine points
  set p0 : Pt := upt A B C (1/3) 0 with hp0
  set p1 : Pt := upt A B C (2/3) (1/3) with hp1
  set p2 : Pt := upt A B C 0 (2/3) with hp2
  set p3 : Pt := upt A B C (2/3) 0 with hp3
  set p4 : Pt := upt A B C (1/3) (2/3) with hp4
  set p5 : Pt := upt A B C 0 (1/3) with hp5
  set p6 : Pt := upt A B C (3/4) 0 with hp6
  set p7 : Pt := upt A B C (1/4) (3/4) with hp7
  set p8 : Pt := upt A B C 0 (1/4) with hp8
  have m0 : p0 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m3 : p3 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m6 : p6 ∈ sides A B C := upt_mem_AB _ (by norm_num) (by norm_num)
  have m1 : p1 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m4 : p4 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m7 : p7 ∈ sides A B C := upt_mem_BC _ _ (by norm_num) (by norm_num) (by norm_num)
  have m2 : p2 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  have m5 : p5 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  have m8 : p8 ∈ sides A B C := upt_mem_CA _ (by norm_num) (by norm_num)
  -- distinctness
  have ne : ∀ {a b c d : ℝ}, (a - c) ^ 2 + (a - c) * (b - d) + (b - d) ^ 2 ≠ 0 →
      upt A B C a b ≠ upt A B C c d := fun h => upt_ne hABBC hBCCA hAB h
  -- right angles
  have ang : ∀ a b c d a' b' : ℝ,
      (a - c) * (a' - c) + (b - d) * (b' - d) + ((a - c) * (b' - d) + (b - d) * (a' - c)) / 2 = 0 →
      ⟪upt A B C a b - upt A B C c d, upt A B C a' b' - upt A B C c d⟫ = 0 := by
    intro a b c d a' b' h
    rw [upt_inner hABBC hBCCA, h, mul_zero]
  rcases bool_ramsey (decide (p0 ∈ S)) (decide (p1 ∈ S)) (decide (p2 ∈ S)) (decide (p3 ∈ S))
      (decide (p4 ∈ S)) (decide (p5 ∈ S)) (decide (p6 ∈ S)) (decide (p7 ∈ S))
      (decide (p8 ∈ S)) with
    h | h | h | h | h | h | h | h | h | h | h | h
  -- (0,1,7), right angle at 1
  · exact mono_right_triangle hcov m0 m1 m7 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,2,6), right angle at 0 : (P,Q,R) = (p2,p0,p6)
  · exact mono_right_triangle hcov m2 m0 m6 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,3,4), right angle at 3 : (p0,p3,p4)
  · exact mono_right_triangle hcov m0 m3 m4 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (0,4,5), right angle at 5 : (p0,p5,p4)
  · exact mono_right_triangle hcov m0 m5 m4 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,2,8), right angle at 2 : (p1,p2,p8)
  · exact mono_right_triangle hcov m1 m2 m8 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,3,5), right angle at 3 : (p1,p3,p5)
  · exact mono_right_triangle hcov m1 m3 m5 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (1,4,5), right angle at 4 : (p1,p4,p5)
  · exact mono_right_triangle hcov m1 m4 m5 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (2,3,4), right angle at 4 : (p2,p4,p3)
  · exact mono_right_triangle hcov m2 m4 m3 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (2,3,5), right angle at 5 : (p2,p5,p3)
  · exact mono_right_triangle hcov m2 m5 m3 h.2 h.1
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (3,4,6), right angle at 3 : (p4,p3,p6)
  · exact mono_right_triangle hcov m4 m3 m6 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (3,5,8), right angle at 5 : (p3,p5,p8)
  · exact mono_right_triangle hcov m3 m5 m8 h.1 h.2
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
  -- (4,5,7), right angle at 4 : (p5,p4,p7)
  · exact mono_right_triangle hcov m5 m4 m7 h.1.symm (h.1.symm.trans h.2)
      (ne (by norm_num)) (ne (by norm_num)) (ne (by norm_num)) (ang _ _ _ _ _ _ (by norm_num))
