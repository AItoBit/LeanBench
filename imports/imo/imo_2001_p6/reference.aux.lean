/-- Rearrangement of the hypothesis `K*M + L*N = (K+L-M+N)*(-K+L+M+N)`. -/
theorem sq_rearrange {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    K ^ 2 - K * M + M ^ 2 = L ^ 2 + L * N + N ^ 2 := by
  linear_combination heq

/-- The key factorization identity:
`(K*M + L*N) * (L^2 + L*N + N^2) = (K*L + M*N) * (K*N + L*M)`. -/
theorem key_identity {K L M N : ℤ}
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    (K * M + L * N) * (L ^ 2 + L * N + N ^ 2) = (K * L + M * N) * (K * N + L * M) := by
  linear_combination (-(L * N)) * sq_rearrange heq
