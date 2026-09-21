by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h := eq_answer_of_conditions (m + 1) hn P h1 h2 h3
    rwa [Nat.add_sub_cancel] at h
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro t x y
      rw [ev_answer, ev_answer, show t * x - 2 * (t * y) = t * (x - 2 * y) by ring,
        show t * x + t * y = t * (x + y) by ring, mul_pow, pow_succ]
      ring
    · intro a b c
      rw [ev_answer, ev_answer, ev_answer, show b + c + a = a + b + c by ring,
        show c + a + b = a + b + c by ring]
      ring
    · rw [ev_answer]
      norm_num
