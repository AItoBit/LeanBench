by
  
  constructor
  · -- Part 1: f(4n+1) - f(4n)
    have eq_4n : 4 * n = 2 * (2 * n) := by ring
    have h1 : f (4 * n) = f (2 * n) := by
      rw [eq_4n]
      exact h_even (2 * n)
      
    calc f (4 * n + 1) - f (4 * n)
      _ = (2 * f (2 * n + 1) - f n) - f (2 * n) := by rw [h_mod1 n, h1]
      _ = (2 * f (2 * n + 1) - f (2 * n)) - f (2 * n) := by rw [← h_even n]
      _ = 2 * (f (2 * n + 1) - f (2 * n)) := by ring

  · -- Part 2: f(4n+3) - f(4n+2)
    have eq_4n2 : 4 * n + 2 = 2 * (2 * n + 1) := by ring
    have h2 : f (4 * n + 2) = f (2 * n + 1) := by
      rw [eq_4n2]
      exact h_even (2 * n + 1)
      
    calc f (4 * n + 3) - f (4 * n + 2)
      _ = (3 * f (2 * n + 1) - 2 * f n) - f (2 * n + 1) := by rw [h_mod3 n, h2]
      _ = (3 * f (2 * n + 1) - 2 * f (2 * n)) - f (2 * n + 1) := by rw [← h_even n]
      _ = 2 * (f (2 * n + 1) - f (2 * n)) := by ring
