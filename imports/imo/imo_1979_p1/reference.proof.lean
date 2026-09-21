by
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [problem_sum_eq, div_eq_iff hq0] at h
  -- `p * D = q * A` over the integers
  have hQ : ((p * D : ℤ) : ℚ) = ((q * A : ℤ) : ℚ) := by
    push_cast
    rw [A_eq, h]
    ring
  have hZ : (p : ℤ) * D = (q : ℤ) * A := by exact_mod_cast hQ
  have hp : Prime (1979 : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    norm_num
  have hdvd : (1979 : ℤ) ∣ (p : ℤ) * D := by
    rw [hZ]
    exact Dvd.dvd.mul_left dvd_A _
  rcases hp.dvd_mul.1 hdvd with h1 | h2
  · exact_mod_cast h1
  · exact absurd h2 not_dvd_D
