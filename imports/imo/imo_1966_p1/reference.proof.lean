by
  -- Eliminating `y` from the two conditions gives `9x - 5a = 26`.
  have _hD : 9 * x - 5 * a = 26 := by omega
  -- With `1 ≤ a` and `a ≤ x`, the Diophantine equation forces `x = 4`, `a = 2`
  -- (the next solution `x = 9, a = 11` violates `a ≤ x`).
  have _hx4 : x = 4 := by omega
  have _ha2 : a = 2 := by omega
  -- Hence “B only” `= 2*x - a = 8 - 2 = 6`.
  omega
