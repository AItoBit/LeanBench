private lemma classify_four (m n j p : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hj : 0 < j) (hp : 0 < p)
    (h₁ : n + p = m * j) (h₂ : n * p = m + j) :
    (m, n) = (1, 2) ∨ (m, n) = (2, 1) ∨
    (m, n) = (1, 3) ∨ (m, n) = (3, 1) ∨
    (m, n) = (2, 2) ∨ (m, n) = (2, 5) ∨
    (m, n) = (5, 2) ∨ (m, n) = (3, 5) ∨
    (m, n) = (5, 3) := by
  by_cases hm1 : m = 1
  · subst m
    have hn2 : 2 ≤ n := by
      by_contra h
      have : n = 1 := by omega
      subst n
      norm_num at h₁ h₂
      omega
    have hp2 : 2 ≤ p := by
      by_contra h
      have : p = 1 := by omega
      subst p
      norm_num at h₁ h₂
      omega
    have hnp : n * p = n + p + 1 := by omega
    have hnpZ : (n : ℤ) * p = n + p + 1 := by exact_mod_cast hnp
    have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 2) :=
      mul_nonneg (by omega) (by omega)
    have hn3 : n ≤ 3 := by nlinarith
    have hp3 : p ≤ 3 := by nlinarith
    interval_cases n <;> interval_cases p <;> norm_num at h₁ h₂ ⊢
  · by_cases hj1 : j = 1
    · subst j
      have hn2 : 2 ≤ n := by
        by_contra h
        have : n = 1 := by omega
        subst n
        norm_num at h₁ h₂
        omega
      have hp2 : 2 ≤ p := by
        by_contra h
        have : p = 1 := by omega
        subst p
        norm_num at h₁ h₂
        omega
      have hnp : n * p = n + p + 1 := by omega
      have hnpZ : (n : ℤ) * p = n + p + 1 := by exact_mod_cast hnp
      have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 2) :=
        mul_nonneg (by omega) (by omega)
      have hn3 : n ≤ 3 := by nlinarith
      have hp3 : p ≤ 3 := by nlinarith
      interval_cases n <;> interval_cases p <;> norm_num at h₁ h₂ ⊢ <;> omega
    · by_cases hn1 : n = 1
      · subst n
        have hm2 : 2 ≤ m := by omega
        have hj2 : 2 ≤ j := by omega
        have hmj : m * j = m + j + 1 := by omega
        have hmjZ : (m : ℤ) * j = m + j + 1 := by exact_mod_cast hmj
        have hnonneg : 0 ≤ ((m : ℤ) - 2) * ((j : ℤ) - 2) :=
          mul_nonneg (by omega) (by omega)
        have hm3 : m ≤ 3 := by nlinarith
        have hj3 : j ≤ 3 := by nlinarith
        interval_cases m <;> interval_cases j <;> norm_num at h₁ h₂ ⊢
      · by_cases hp1 : p = 1
        · subst p
          have hm2 : 2 ≤ m := by omega
          have hj2 : 2 ≤ j := by omega
          have hmj : m * j = m + j + 1 := by omega
          have hmjZ : (m : ℤ) * j = m + j + 1 := by exact_mod_cast hmj
          have hnonneg : 0 ≤ ((m : ℤ) - 2) * ((j : ℤ) - 2) :=
            mul_nonneg (by omega) (by omega)
          have hm3 : m ≤ 3 := by nlinarith
          have hj3 : j ≤ 3 := by nlinarith
          interval_cases m <;> interval_cases j <;> norm_num at h₁ h₂ ⊢ <;> omega
        · have hm2 : 2 ≤ m := by omega
          have hn2 : 2 ≤ n := by omega
          have hj2 : 2 ≤ j := by omega
          have hp2 : 2 ≤ p := by omega
          have hsumprod :
              ((m : ℤ) - 1) * ((j : ℤ) - 1) +
                ((n : ℤ) - 1) * ((p : ℤ) - 1) = 2 := by
            nlinarith
          have hA : (m : ℤ) - 1 ≤ ((m : ℤ) - 1) * ((j : ℤ) - 1) := by
            have hnonneg : 0 ≤ ((m : ℤ) - 1) * ((j : ℤ) - 2) :=
              mul_nonneg (by omega) (by omega)
            nlinarith
          have hB : 1 ≤ ((n : ℤ) - 1) * ((p : ℤ) - 1) := by
            have hnonneg : 0 ≤ ((n : ℤ) - 2) * ((p : ℤ) - 1) :=
              mul_nonneg (by omega) (by omega)
            nlinarith
          have hm_le : m ≤ 2 := by nlinarith
          have : m = 2 := by omega
          subst m
          have : j = 2 := by nlinarith
          subst j
          have : n = 2 := by nlinarith
          subst n
          have : p = 2 := by nlinarith
          subst p
          simp
