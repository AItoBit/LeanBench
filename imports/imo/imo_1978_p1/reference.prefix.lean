set_option maxRecDepth 10000

namespace Imo1978P1

/-- `1978` has multiplicative order exactly `100` modulo `125`. -/
private lemma order_125 {d : ℕ} (h : 1978 ^ d ≡ 1 [MOD 125]) : 100 ∣ d := by
  have h100 : 1978 ^ 100 ≡ 1 [MOD 125] := by decide
  have hzero : ∀ s ∈ Finset.range 100, 1978 ^ s ≡ 1 [MOD 125] → s = 0 := by decide
  have hd : d = 100 * (d / 100) + d % 100 := (Nat.div_add_mod d 100).symm
  have hstep : 1978 ^ (d % 100) ≡ 1 [MOD 125] := by
    have e : 1978 ^ d = (1978 ^ 100) ^ (d / 100) * 1978 ^ (d % 100) := by
      rw [← pow_mul, ← pow_add, ← hd]
    rw [e] at h
    have h1 : (1978 ^ 100) ^ (d / 100) ≡ 1 [MOD 125] := by
      simpa using h100.pow (d / 100)
    calc 1978 ^ (d % 100) ≡ 1 * 1978 ^ (d % 100) [MOD 125] := by rw [one_mul]
      _ ≡ (1978 ^ 100) ^ (d / 100) * 1978 ^ (d % 100) [MOD 125] := (h1.mul_right _).symm
      _ ≡ 1 [MOD 125] := h
  have hlt : d % 100 < 100 := Nat.mod_lt d (by norm_num)
  have := hzero (d % 100) (Finset.mem_range.mpr hlt) hstep
  omega

private lemma dvd4 : ∀ k, 2 ≤ k → 4 ∣ 1978 ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  rw [pow_add]
  exact Dvd.dvd.mul_right (by norm_num) _

private lemma dvd8 : ∀ k, 3 ≤ k → 8 ∣ 1978 ^ k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
  rw [pow_add]
  exact Dvd.dvd.mul_right (by norm_num) _
