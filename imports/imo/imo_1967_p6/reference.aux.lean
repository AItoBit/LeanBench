/--
Auxiliary lemma solving the linear recurrence from the solution:
`m_{k+1} = (6/7) * m_k - (6/7) * (k+1)`
-/
lemma m_explicit (m_seq : ℕ → ℝ) (m0 : ℝ)
    (h0 : m_seq 0 = m0)
    (h_rec : ∀ k, m_seq (k + 1) = (6 / 7) * m_seq k - (6 / 7) * (k + 1 : ℝ))
    (k : ℕ) :
    m_seq k = (m0 - 36) * (6 / 7) ^ k - 6 * (k : ℝ) + 36 := by
  induction k with
  | zero =>
    simp [h0]
  | succ k ih =>
    rw [h_rec k, ih]
    push_cast
    rw [pow_succ]
    ring
