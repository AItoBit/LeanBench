by
  -- Apply the sequence bound
  have h_bound := sumAdj_bound n l 1 h_div
  rw [h_last] at h_bound
  
  -- Use the property n^2 = n * n to cleanly close the inequality
  rw [pow_two]
  omega
