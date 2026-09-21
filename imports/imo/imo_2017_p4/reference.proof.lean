by

  have hKST :
      KST = KRA := by
    calc
      KST = SRK + SKR := h₁
      _ = KRA := h₂

  have hsupp :
      Supplementary KST KBT := by
    unfold Supplementary
    rw [hKST, h₃]
    simp

  unfold TangentChord

  calc
    STK = SBK := h₄.symm
    _ = SAT := h₅
