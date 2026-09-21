lemma without_digits {n : ℕ} (hn : ProblemPredicate n) : ∃ c : ℕ, ProblemPredicate' c n := by
  refine ⟨n / 10, ?_, ?_⟩
  · have := hn.1
    omega
  · rcases n with - | n
    · simp [ProblemPredicate] at hn
    · rw [ProblemPredicate, digits_def' (by decide : 2 ≤ 10) n.succ_pos, List.tail_cons,
        List.concat_eq_append, ofDigits_append, ofDigits_digits, ofDigits_singleton] at hn
      rw [← hn.right, add_comm, mul_comm]

lemma case_lt_5_digits {c n k : ℕ} (hk : k < 5) (hc : (digits 10 c).length = k)
    (hpp : ProblemPredicate' c n) : False := by
  obtain ⟨h1, h2⟩ := hpp
  rw [hc] at h2
  interval_cases k <;> simp_all <;> omega

lemma case_5_digits {c n : ℕ} (hc : (digits 10 c).length = 5) (hpp : ProblemPredicate' c n) :
    c = 15384 := by
  obtain ⟨h1, h2⟩ := hpp
  rw [hc, h1] at h2
  norm_num at h2
  omega

lemma case_more_digits {c n : ℕ} (hc : 6 ≤ (digits 10 c).length) (hpp : ProblemPredicate' c n) :
    153846 ≤ n := by
  have hnz : c ≠ 0 := by
    rintro rfl
    simp at hc
  calc
    (153846 : ℕ) ≤ 10 ^ 6 := by norm_num
    _ ≤ 10 ^ (digits 10 c).length := Nat.pow_le_pow_right (by decide) hc
    _ ≤ 10 * c := base_pow_length_digits_le 10 c (by decide) hnz
    _ ≤ n := by omega

lemma satisfied_by_153846 : ProblemPredicate 153846 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.digits_def' (by norm_num : 1 < 10), Nat.ofDigits]

lemma no_smaller_solutions (n : ℕ) (hn : ProblemPredicate n) : 153846 ≤ n := by
  obtain ⟨c, hcn⟩ := without_digits hn
  rcases lt_or_ge (digits 10 c).length 6 with h | h
  · rcases Nat.lt_or_ge (digits 10 c).length 5 with h5 | h5
    · exact (case_lt_5_digits h5 rfl hcn).elim
    · have hc5 : (digits 10 c).length = 5 := by omega
      have hc' := case_5_digits hc5 hcn
      have hn' := hcn.1
      omega
  · exact case_more_digits h hcn
