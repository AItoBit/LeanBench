by
  rintro ⟨A, hA, heq⟩
  have h : Balanced n A := ⟨hA, heq⟩
  have key : ∀ t, t ∈ block n → ¬ 2 ∣ t → ¬ 3 ∣ t → ¬ 5 ∣ t → t = 1 := fun t ht h2 h3 h5 =>
    eq_one_of_smooth (fun p hp hpt => prime_factor_le_five h hp ht hpt) h2 h3 h5
  -- pick the first odd member `m` of the block
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m, n ≤ m ∧ m ≤ n + 1 ∧ ¬ 2 ∣ m := by
    by_cases hpar : 2 ∣ n
    · exact ⟨n + 1, by omega, by omega, by omega⟩
    · exact ⟨n, by omega, by omega, hpar⟩
  -- one of the three odd members `m`, `m + 2`, `m + 4` avoids `3` and `5`, hence is `1`
  have hn1 : n = 1 := by
    have hpick : (¬ 2 ∣ m ∧ ¬ 3 ∣ m ∧ ¬ 5 ∣ m) ∨
        (¬ 2 ∣ (m + 2) ∧ ¬ 3 ∣ (m + 2) ∧ ¬ 5 ∣ (m + 2)) ∨
        (¬ 2 ∣ (m + 4) ∧ ¬ 3 ∣ (m + 4) ∧ ¬ 5 ∣ (m + 4)) := by omega
    rcases hpick with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
    · have := key m (by simp only [block, Finset.mem_Icc]; omega) a b c; omega
    · have := key (m + 2) (by simp only [block, Finset.mem_Icc]; omega) a b c; omega
    · have := key (m + 4) (by simp only [block, Finset.mem_Icc]; omega) a b c; omega
  subst hn1
  -- in `{1, …, 6}` only `5` is a multiple of `5`
  obtain ⟨a, ha, b, hb, hab, h5a, h5b⟩ :=
    exists_two_distinct_multiples h (p := 5) (m := 5) (by norm_num)
      (by simp only [block, Finset.mem_Icc]; omega) dvd_rfl
  simp only [block, Finset.mem_Icc] at ha hb
  omega
