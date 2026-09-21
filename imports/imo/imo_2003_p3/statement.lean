/-- 
Formalization of the median step from IMO 2005 Problem 5:
"Suppose a triangle has side lengths a, b, c and the length of the median 
to the midpoint of side length c is m. Then applying the cosine rule twice 
we get m^2 = a^2/2 + b^2/2 - c^2/4. So if m^2 = 3/4 c^2, it follows that 
a^2 + b^2 = 2c^2. Similarly, b^2 + c^2 = 2a^2. Subtracting, a = c. 
Similarly for the other pairs of sides."
-/
theorem candidate (a b c m_a m_b m_c : ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  (hmc : m_c^2 = a^2 / 2 + b^2 / 2 - c^2 / 4)
  (hmc_val : m_c^2 = 3 / 4 * c^2)
  (hma : m_a^2 = b^2 / 2 + c^2 / 2 - a^2 / 4)
  (hma_val : m_a^2 = 3 / 4 * a^2)
  (hmb : m_b^2 = c^2 / 2 + a^2 / 2 - b^2 / 4)
  (hmb_val : m_b^2 = 3 / 4 * b^2) :
  a = b ∧ b = c :=
