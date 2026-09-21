by
  obtain ⟨a, ha⟩ := exists_good
  refine ⟨a, ?_, ?_⟩
  · intro x h1 hx n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [x_eq_s h1 hx k, x_eq_s h1 hx (k + 1)]
    exact good_imp_cond ha k
  · intro b hb
    have hrec : ∀ n : ℕ, 1 ≤ n → (fun n => s b (n - 1)) (n + 1) =
        (fun n => s b (n - 1)) n * ((fun n => s b (n - 1)) n + 1 / (n : ℝ)) := by
      intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [s_succ]
    have hgood : Good b := by
      apply cond_imp_good
      intro k
      have h := hb (fun n => s b (n - 1)) (by simp) hrec (k + 1) (by omega)
      simpa using h
    exact good_unique hgood ha
