by
  -- Key: `f n ≥ k` whenever `n ≥ k` and `n > 0`.
  have key : ∀ k n : ℕ, k ≤ n → 0 < n → k ≤ f n := by
    intro k
    induction k with
    | zero => intro n _ _; exact Nat.zero_le _
    | succ k ih =>
      intro n hkn hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have hk0 : k = 0 := by omega
        have hp := hpos (m + 1) (by omega)
        omega
      · have h1 : k ≤ f m := ih m (by omega) hm
        have h2 : 0 < f m := hpos m hm
        have h3 : k ≤ f (f m) := ih (f m) h1 h2
        have h4 := h m hm
        omega
  -- `n ≤ f n`
  have hge : ∀ n, 0 < n → n ≤ f n := fun n hn => key n n (le_refl n) hn
  -- `f` is strictly increasing on the positives
  have hstep : ∀ n, 0 < n → f n < f (n + 1) := by
    intro n hn
    have h1 := h n hn
    have h2 : f n ≤ f (f n) := hge (f n) (hpos n hn)
    omega
  have hmono : ∀ a b : ℕ, 0 < a → a ≤ b → f a ≤ f b := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ m hm ih =>
      have hs := hstep m (by omega)
      omega
  -- `f n ≤ n`
  intro n hn
  have hle : f n ≤ n := by
    by_contra hcon
    have h1 : n + 1 ≤ f n := by omega
    have h2 : f (n + 1) ≤ f (f n) := hmono (n + 1) (f n) (by omega) h1
    have h3 := h n hn
    omega
  have h4 := hge n hn
  omega
