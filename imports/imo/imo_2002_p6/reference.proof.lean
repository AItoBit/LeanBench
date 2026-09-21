by
  have h1 := core n hn d H hH3 far θ hfar hfarmin hhull hθ hinner
  have h2 := sum_erase_eq_two_mul n (fun i j => 2 / d i j) (fun i j => by rw [hsymm])
  have h3 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), (2:ℝ) / d i j
      = 2 * ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), 1 / d i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith [h1, h2, h3]
