/-- A number with two distinct prime divisors is not a prime power. -/
theorem not_isPrimePow_of_two_primes {x p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpd : p ∣ x) (hqd : q ∣ x) : ¬ IsPrimePow x := by
  rintro ⟨r, k, hr, hk, hrk⟩
  have hrp : r.Prime := Nat.prime_iff.2 hr
  have h1 : p ∣ r ^ k := by rw [hrk]; exact hpd
  have h2 : q ∣ r ^ k := by rw [hrk]; exact hqd
  have hp' : p = r := (Nat.prime_dvd_prime_iff_eq hp hrp).1 (hp.dvd_of_dvd_pow h1)
  have hq' : q = r := (Nat.prime_dvd_prime_iff_eq hq hrp).1 (hq.dvd_of_dvd_pow h2)
  exact hpq (hp'.trans hq'.symm)
