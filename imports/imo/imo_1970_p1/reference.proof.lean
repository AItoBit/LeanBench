by
  calc (r1 / q1) * (r2 / q2)
    _ = (tA * tM) * (tB * tM') := by rw [h_r1q1, h_r2q2]
    _ = (tA * tB) * (tM * tM') := by ring
    _ = (tA * tB) * 1 := by rw [h_supp]
    _ = tA * tB := by ring
    _ = r / q := h_rq.symm
