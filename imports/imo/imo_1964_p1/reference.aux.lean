/-- The powers of `2` are periodic mod `7` with period `3`. -/
theorem two_pow_mod_seven (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 3) [MOD 7] :=
  calc 2 ^ n = 2 ^ (3 * (n / 3) + n % 3) := by rw [Nat.div_add_mod]
    _ = (2 ^ 3) ^ (n / 3) * 2 ^ (n % 3) := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / 3) * 2 ^ (n % 3) [MOD 7] := by gcongr; decide
    _ = 2 ^ (n % 3) := by ring

/-- (a) The natural numbers `n` for which `7` divides `2 ^ n - 1` are exactly
the multiples of `3`. -/
theorem imo_1964_p1.parts.a :
    {n : ℕ | 7 ∣ (2 ^ n - 1 : ℕ)} = {n : ℕ | 3 ∣ n} := by
  ext n
  simp only [Set.mem_ofPred_eq]
  have ht : n % 3 < 3 := Nat.mod_lt _ (by decide)
  calc 7 ∣ 2 ^ n - 1 ↔ 2 ^ n ≡ 1 [MOD 7] := by
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']
        exact Nat.one_le_pow' n 1
    _ ↔ 2 ^ (n % 3) ≡ 1 [MOD 7] :=
        ⟨(two_pow_mod_seven n).symm.trans, (two_pow_mod_seven n).trans⟩
    _ ↔ n % 3 = 0 := by interval_cases h : n % 3 <;> simp_all <;> decide
    _ ↔ 3 ∣ n := by rw [Nat.dvd_iff_mod_eq_zero]

/-- (b) There is no positive natural number `n` for which `7` divides `2 ^ n + 1`.
(The positivity hypothesis `_h₀` is kept as stated, but is not needed: the claim also
holds for `n = 0`.) -/
theorem imo_1964_p1.parts.b (n : ℕ) (_h₀ : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have ht : n % 3 < 3 := Nat.mod_lt _ (by decide)
  have H : 2 ^ (n % 3) + 1 ≡ 0 [MOD 7] := calc
    2 ^ (n % 3) + 1 ≡ 2 ^ n + 1 [MOD 7] := by gcongr ?_ + 1; exact (two_pow_mod_seven n).symm
      _ ≡ 0 [MOD 7] := h.modEq_zero_nat
  interval_cases h : n % 3 <;> simp_all [Nat.ModEq]
