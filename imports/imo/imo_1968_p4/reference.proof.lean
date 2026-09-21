by
  
  -- As shown in "image_98e229.png", we condition on whether b + f > a
  by_cases h : b + f > a
  · -- If b + f > a, the vertex with edges a, b, f forms a triangle.
    -- a + b > f and f + a > b follow from a ≥ f, a ≥ b, and the strict positivity of edges.
    have h_abf : a + b > f ∧ b + f > a ∧ f + a > b := ⟨by linarith, h, by linarith⟩
    exact Or.inr (Or.inr (Or.inl h_abf))
    
  · -- Otherwise, b + f ≤ a. We show the vertex with edges a, c, e forms a triangle.
    -- c + e > a follows from combining e + f > a, b + c > a, and b + f ≤ a.
    -- a + c > e and e + a > c follow from a ≥ e, a ≥ c, and edge positivity.
    have h_le : b + f ≤ a := not_lt.mp h
    have h_ace : a + c > e ∧ c + e > a ∧ e + a > c := ⟨by linarith, by linarith, by linarith⟩
    exact Or.inr (Or.inl h_ace)
