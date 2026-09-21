/--
Formalization of the algebraic derivation in the solution for the IMO problem.
It demonstrates that the simplified recurrence relation ending with `m_{n-1} = n` 
yields the explicit algebraic identity for `m - 36`.
-/
theorem candidate
    (m_seq : ℕ → ℝ) (m : ℝ) (n : ℕ) (hn : 0 < n)
    (h0 : m_seq 0 = m)
    (h_rec : ∀ k, m_seq (k + 1) = (6 / 7) * m_seq k - (6 / 7) * (k + 1 : ℝ))
    (h_end : m_seq (n - 1) = (n : ℝ)) :
    m - 36 = 7 * ((n : ℝ) - 6) * (7 / 6) ^ (n - 1) :=
