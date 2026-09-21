by
  intro hp
  -- ordering of the three quantities
  have hpos : 0 < K * N + L * M := by nlinarith
  have h1 : K * N + L * M < K * M + L * N := by nlinarith
  have h2 : K * M + L * N < K * L + M * N := by nlinarith
  -- divisibility coming from the key identity
  have hdvd : (K * M + L * N) ∣ (K * L + M * N) * (K * N + L * M) :=
    ⟨L ^ 2 + L * N + N ^ 2, (key_identity heq).symm⟩
  -- the prime `K*L + M*N` does not divide the smaller positive number `K*M + L*N`
  have hnd : ¬ (K * L + M * N) ∣ (K * M + L * N) := by
    intro h
    have := Int.le_of_dvd (by linarith) h
    linarith
  have hcop : IsCoprime (K * M + L * N) (K * L + M * N) :=
    (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hdvd' : (K * M + L * N) ∣ (K * N + L * M) :=
    hcop.dvd_of_dvd_mul_left hdvd
  have := Int.le_of_dvd hpos hdvd'
  linarith
