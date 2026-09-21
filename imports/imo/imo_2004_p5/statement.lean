/-- **IMO 2004 P5.** -/
theorem candidate (r x y u v s w lam mu : ℝ)
    (hr : 0 < r)
    -- `B ≠ D`
    (hbd : (x - u) ^ 2 + (y - v) ^ 2 ≠ 0)
    -- `BD` does not bisect `∠ABC`
    (hK : ¬(x = 0 ∧ u = 0))
    -- the two isogonal lines are not parallel
    (hE : r ^ 2 * (x * y - u * v) + x * y * (v ^ 2 - u ^ 2) + u * v * (x ^ 2 - y ^ 2) ≠ 0)
    -- `∠PBC = ∠DBA`
    (h1 : (u - x) * (s - x) - (v - y) * (w - y) = lam * (x ^ 2 - y ^ 2 - r ^ 2))
    (h2 : (u - x) * (w - y) + (v - y) * (s - x) = lam * (2 * x * y))
    -- `∠PDC = ∠BDA`
    (h3 : (x - u) * (s - u) - (y - v) * (w - v) = mu * (u ^ 2 - v ^ 2 - r ^ 2))
    (h4 : (x - u) * (w - v) + (y - v) * (s - u) = mu * (2 * u * v)) :
    ((s + r) ^ 2 + w ^ 2 = (s - r) ^ 2 + w ^ 2)
      ↔ (x ^ 2 + y ^ 2 - r ^ 2) * v = (u ^ 2 + v ^ 2 - r ^ 2) * y :=
