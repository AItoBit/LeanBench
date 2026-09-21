by
  
  -- XY ≤ XX' + X'Y ≤ 1
  have hXY : dist X Y ≤ 1 := by
    have t1 := dist_triangle X X' Y
    linarith

  -- XB ≥ X'B' - XX' - BB' ≥ 100 - 1/2 - 1/2 = 99
  have hXB : 99 ≤ dist X B := by
    have t1 := dist_triangle X' B B'
    have t2 := dist_triangle X' X B
    have t3 := dist_comm X X'
    linarith

  -- YB ≥ X'B' - X'Y - BB' ≥ 100 - 1/2 - 1/2 = 99
  have hYB : 99 ≤ dist Y B := by
    have t1 := dist_triangle X' B B'
    have t2 := dist_triangle X' Y B
    linarith

  -- The path from X to Y via B has length at least 198
  exact ⟨hXY, hXB, hYB, by linarith⟩
