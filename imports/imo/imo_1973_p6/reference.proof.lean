by
  have hq' : (0:ℝ) < 1 - q := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ k ∈ Finset.range n, a k := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ k ∈ Finset.range n, cc n q a k := ⟨_, rfl⟩
  have hApos : 0 < A := by
    rw [hA]
    exact Finset.sum_pos (fun j _ => ha j) (Finset.nonempty_range_iff.mpr (by omega))
  have hCpos : 0 < C := by
    rw [hC]
    exact Finset.sum_pos (fun j _ => cc_pos hn hq0 ha j)
      (Finset.nonempty_range_iff.mpr (by omega))
  -- condition (c) for the unscaled construction
  have hswap : ∑ k ∈ Finset.range n, cc n q a k
      = ∑ j ∈ Finset.range n, (∑ k ∈ Finset.range n, q ^ dd k j) * a j := by
    unfold cc
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have hkey : C < (1 + q) / (1 - q) * A := by
    rw [hC, hA, hswap, Finset.mul_sum]
    refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) ?_
    intro j hj
    exact mul_lt_mul_of_pos_right (inner_bound hq0 hq1 (Finset.mem_range.mp hj)) (ha j)
  -- the scaling factor
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ((1 + q) / (1 - q) * A + C) / (2 * C) := ⟨_, rfl⟩
  have h2C : (0:ℝ) < 2 * C := by linarith
  have hμmul : μ * (2 * C) = (1 + q) / (1 - q) * A + C := by
    rw [hμ]; field_simp
  have hμ1 : 1 < μ := by
    refine lt_of_mul_lt_mul_right ?_ h2C.le
    rw [hμmul]
    linarith
  have hμpos : 0 < μ := by linarith
  refine ⟨fun k => μ * cc n q a k, ?_, ?_, ?_, ?_⟩
  · intro k _
    exact mul_pos hμpos (cc_pos hn hq0 ha k)
  · intro k hk
    have h1 := le_cc hq0 ha hk
    have h2 := cc_pos (n := n) hn hq0 ha k
    nlinarith
  · intro k hk
    constructor
    · have := cc_lower hq0 hq1 ha hk
      nlinarith
    · have := cc_upper hq0 hq1 ha hk
      nlinarith
  · have hsum : ∑ k ∈ Finset.range n, μ * cc n q a k = μ * C := by
      rw [hC, Finset.mul_sum]
    rw [hsum, ← hA]
    -- `μ * C = (R A + C)/2 < R A`
    have : μ * C * 2 = (1 + q) / (1 - q) * A + C := by
      rw [← hμmul]; ring
    linarith
