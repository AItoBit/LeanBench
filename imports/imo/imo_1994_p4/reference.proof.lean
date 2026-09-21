by
  constructor
  · rintro ⟨hm, hn, hdiv⟩
    rcases hdiv with ⟨k, hk⟩
    have hmn : 1 ≤ m * n := by nlinarith [Nat.mul_pos hm hn]
    have hkpos : 0 < k := by
      by_contra hk0
      have : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      simp at hk
    have heq : n ^ 3 + 1 + k = m * n * k := by
      calc
        n ^ 3 + 1 + k = (m * n - 1) * k + k := by rw [hk]
        _ = ((m * n - 1) + 1) * k := by ring
        _ = m * n * k := by rw [Nat.sub_add_cancel hmn]
    have hmod : (k + 1) % n = 0 := by
      have h := congrArg (fun x : ℕ => x % n) heq
      simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using h
    have hndvd : n ∣ k + 1 := Nat.dvd_of_mod_eq_zero hmod
    rcases hndvd with ⟨j, hj_eq⟩
    have hjpos : 0 < j := by
      have : 0 < n * j := by rw [← hj_eq]; omega
      exact Nat.pos_of_mul_pos_left this
    have hbig : n * (n ^ 2 + j + m) = n * (m * n * j) := by
      calc
        n * (n ^ 2 + j + m) = n ^ 3 + n * j + m * n := by ring
        _ = (n ^ 3 + 1 + k) + m * n := by rw [← hj_eq]; ring
        _ = m * n * k + m * n := by rw [heq]
        _ = m * n * (k + 1) := by ring
        _ = n * (m * n * j) := by rw [hj_eq]; ring
    have hquad : n ^ 2 + j + m = m * n * j :=
      Nat.mul_left_cancel hn hbig
    have hmul_le : n * n ≤ n * (m * j) := by
      calc
        n * n ≤ n ^ 2 + j + m := by
          simp [pow_two]
          omega
        _ = m * n * j := hquad
        _ = n * (m * j) := by ring
    have hn_le : n ≤ m * j := Nat.le_of_mul_le_mul_left hmul_le hn
    let p := m * j - n
    have hfirst : n + p = m * j := by
      exact Nat.add_sub_of_le hn_le
    have hsecond : n * p = m + j := by
      calc
        n * p = n * (m * j) - n * n := by
          simp [p, Nat.mul_sub_left_distrib]
        _ = (n ^ 2 + j + m) - n ^ 2 := by
          congr 1
          · calc
              n * (m * j) = m * n * j := by ring
              _ = n ^ 2 + j + m := hquad.symm
          · simp [pow_two]
        _ = m + j := by omega
    have hppos : 0 < p := by
      apply Nat.pos_of_mul_pos_left (a := n)
      rw [hsecond]
      omega
    exact classify_four m n j p hm hn hjpos hppos hfirst hsecond
  · rintro (h | h | h | h | h | h | h | h | h)
    all_goals
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      norm_num
