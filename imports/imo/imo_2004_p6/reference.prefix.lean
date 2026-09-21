namespace Imo2004P6

/-- `m` is alternating: consecutive decimal digits have different parity. Digit `i` of `m` has the
parity of `m / 10 ^ i`, and exists exactly when `10 ^ i ≤ m`. -/
def Alternating (m : ℕ) : Prop :=
  ∀ i : ℕ, 10 ^ (i + 1) ≤ m → (m / 10 ^ i) % 2 ≠ (m / 10 ^ (i + 1)) % 2

/-! ### Sanity checks on the definition -/

theorem alternating_sixteen : Alternating 16 := by
  intro i hi
  match i with
  | 0 => norm_num
  | (k + 1) =>
      exfalso
      have h1 : (10 : ℕ) ^ 2 ≤ 10 ^ (k + 1 + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (10 : ℕ) ^ 2 = 100 := by norm_num
      omega

/-! ### No multiple of `20` is alternating -/

theorem not_alternating_of_twenty_dvd {m : ℕ} (hm : 0 < m) (h : 20 ∣ m) : ¬ Alternating m := by
  intro halt
  obtain ⟨t, rfl⟩ := h
  have ht : 1 ≤ t := by omega
  have hpow : (10 : ℕ) ^ (0 + 1) = 10 := by norm_num
  have hle : 10 ^ (0 + 1) ≤ 20 * t := by omega
  have hne := halt 0 hle
  have e0 : (20 * t) / 10 ^ 0 = 20 * t := by norm_num
  have e1 : (20 * t) / 10 ^ (0 + 1) = 2 * t := by rw [hpow]; omega
  rw [e0, e1] at hne
  exact hne (by omega)
