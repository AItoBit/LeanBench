by
  -- Apply the exact distance identity
  rw [convex_distance_sq_identity]
  
  -- Set up the bounds and non-negativity constraints for the subtracted term
  have ht_sub : 0 ≤ 1 - t := by linarith
  have hsq : 0 ≤ normSq (d1 - e1) (d2 - e2) := by
    dsimp [normSq]
    positivity
  
  -- Rigorously establish that the subtraction component is non-negative
  have h_prod1 : 0 ≤ t * (1 - t) := mul_nonneg ht0 ht_sub
  have h_prod2 : 0 ≤ t * (1 - t) * normSq (d1 - e1) (d2 - e2) := mul_nonneg h_prod1 hsq
  
  -- Let M be the maximum of the two squared distances
  let M := max (normSq d1 d2) (normSq e1 e2)
  have hdM : normSq d1 d2 ≤ M := le_max_left _ _
  have heM : normSq e1 e2 ≤ M := le_max_right _ _
  
  -- Multiply the inequalities by the non-negative convex weights
  have H1 : t * normSq d1 d2 ≤ t * M := mul_le_mul_of_nonneg_left hdM ht0
  have H2 : (1 - t) * normSq e1 e2 ≤ (1 - t) * M := mul_le_mul_of_nonneg_left heM ht_sub
  
  -- Conclude the proof by stringing together the linear inequalities
  calc
    t * normSq d1 d2 + (1 - t) * normSq e1 e2 - t * (1 - t) * normSq (d1 - e1) (d2 - e2)
      ≤ t * normSq d1 d2 + (1 - t) * normSq e1 e2 := by 
        -- Subtracting a non-negative value maintains or decreases the total
        linarith
    _ ≤ t * M + (1 - t) * M := add_le_add H1 H2
    _ = M := by ring
