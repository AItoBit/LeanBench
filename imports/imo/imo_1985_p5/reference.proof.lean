by
  
  constructor
  · -- Prove angle_AON + angle_AMN = 180
    calc angle_AON + angle_AMN = (2 * η + 2 * lam) + 2 * φ := by rw [h3, h4]
      _ = 2 * (η + lam) + 2 * φ := by ring
      _ = 2 * θ + 2 * φ := by rw [← h2]
      _ = 2 * (θ + φ) := by ring
      _ = 2 * 90 := by rw [h1]
      _ = 180 := by norm_num
  
  · -- Prove angle_OMB = 90
    calc angle_OMB = angle_OMN + angle_MNB := h7
      _ = φ + θ := by rw [h5, h6]
      _ = θ + φ := by ring
      _ = 90 := h1
