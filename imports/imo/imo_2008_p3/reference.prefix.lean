namespace Imo2008P3

/-- For a prime `p ≡ 1 (mod 4)` with `p > 20`, some `n` with `p ∣ n² + 1` beats the bound. -/
theorem key (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) (hp20 : 20 < p) :
    ∃ n : ℕ, 0 < n ∧ p ∣ n ^ 2 + 1 ∧ (2 * (n : ℝ) + Real.sqrt (2 * (n : ℝ)) < p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- a square root of `-1` modulo `p`
  obtain ⟨y, hy⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  have hcast : ((y.val : ℕ) : ZMod p) = y := by simp
  obtain ⟨x, hxlt, hxdvd⟩ : ∃ x : ℕ, x < p ∧ p ∣ x ^ 2 + 1 := by
    refine ⟨y.val, ZMod.val_lt y, ?_⟩
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    push_cast
    rw [hcast]
    linear_combination -hy
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hxdvd
    norm_num at hxdvd
    omega
  -- fold into the range `2n < p`
  obtain ⟨n, hn0, hn2p, hndvd⟩ : ∃ n, 0 < n ∧ 2 * n < p ∧ p ∣ n ^ 2 + 1 := by
    rcases Nat.lt_or_ge (2 * x) p with hlt | hge
    · exact ⟨x, by omega, hlt, hxdvd⟩
    · refine ⟨p - x, by omega, by omega, ?_⟩
      refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
      have hxp : x ≤ p := le_of_lt hxlt
      have hx : (((x : ℕ) ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hxdvd
      push_cast at hx ⊢
      rw [Nat.cast_sub hxp, ZMod.natCast_self]
      linear_combination hx
  -- `k = p - 2n`
  obtain ⟨k, hk⟩ : ∃ k, p = 2 * n + k := ⟨p - 2 * n, by omega⟩
  have hkdvd : p ∣ k ^ 2 + 4 := by
    refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    have hkk : ((k : ℕ) : ZMod p) = -(2 * (n : ZMod p)) := by
      have h0 : (((2 * n + k : ℕ)) : ZMod p) = 0 := by rw [← hk]; exact ZMod.natCast_self p
      push_cast at h0
      linear_combination h0
    have hn : (((n : ℕ) ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hndvd
    push_cast at hn ⊢
    rw [hkk]
    linear_combination 4 * hn
  have hkge : p ≤ k ^ 2 + 4 := Nat.le_of_dvd (by positivity) hkdvd
  have hk4 : 4 < k := by nlinarith
  have h2nk : 2 * n < k ^ 2 := by omega
  refine ⟨n, hn0, hndvd, ?_⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlt : 2 * (n : ℝ) < (k : ℝ) ^ 2 := by exact_mod_cast h2nk
  have hsq : Real.sqrt (2 * (n : ℝ)) < (k : ℝ) := (Real.sqrt_lt' hkR).2 hlt
  have hpR : (p : ℝ) = 2 * (n : ℝ) + (k : ℝ) := by exact_mod_cast hk
  rw [hpR]
  linarith
