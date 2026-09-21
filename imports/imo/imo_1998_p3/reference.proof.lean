by
  constructor
  · rintro ⟨n, hn, he⟩

    have hd : (d n : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (d_pos hn))

    have heR :
        (d (n ^ 2) : ℚ) = (k : ℚ) * (d n : ℚ) :=
      (div_eq_iff hd).mp he

    have heN : d (n ^ 2) = k * d n := by
      exact_mod_cast heR

    have ho := odd_d_square hn
    rw [heN] at ho
    exact (Nat.odd_mul.mp ho).1

  · intro hk
    obtain ⟨es, hes⟩ := odd_list k hk
    obtain ⟨n, hn, he⟩ := realize_list es
    exact ⟨n, hn, he.trans hes⟩
