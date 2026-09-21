/-- **IMO 2001, Problem 6.** If `K > L > M > N` are positive integers with
`K*M + L*N = (K+L-M+N)*(-K+L+M+N)`, then `K*L + M*N` is not prime. -/
theorem candidate {K L M N : ℤ}
    (hN : 0 < N) (hMN : N < M) (hLM : M < L) (hKL : L < K)
    (heq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
    ¬ Prime (K * L + M * N) :=
