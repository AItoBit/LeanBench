by
  -- superadditivity
  have super : ∀ m n, 1 ≤ m → 1 ≤ n → f m + f n ≤ f (m + n) := by
    intro m n hm hn
    rcases h m n hm hn with hh | hh <;> omega
  -- `f 1 = 0`
  have hf1 : f 1 = 0 := by
    have hs := super 1 1 (by omega) (by omega)
    norm_num at hs
    omega
  -- `f 3 = 1`
  have hf3 : f 3 = 1 := by
    have hd := h 2 1 (by omega) (by omega)
    norm_num at hd
    omega
  -- `f (k * m) ≥ k * f m`
  have mult : ∀ k m, 1 ≤ k → 1 ≤ m → k * f m ≤ f (k * m) := by
    intro k
    induction k with
    | zero => intro m hk hm; omega
    | succ j ih =>
      intro m hk hm
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · have h1 := ih m hj hm
        have h2' := super (j * m) m (Nat.mul_pos hj hm) hm
        have e : (j + 1) * m = j * m + m := by ring
        have e2 : (j + 1) * f m = j * f m + f m := by ring
        rw [e, e2]
        omega
  -- lower bound
  have hl : 660 * f 3 ≤ f 1980 := by
    have hm := mult 660 3 (by omega) (by omega)
    norm_num at hm
    exact hm
  have hlow : 660 ≤ f 1982 := by
    have hs := super 1980 2 (by omega) (by omega)
    norm_num at hs
    omega
  -- upper bound
  have h87 : 29 * f 3 ≤ f 87 := by
    have hm := mult 29 3 (by omega) (by omega)
    norm_num at hm
    exact hm
  have h89 : 29 ≤ f 89 := by
    have hs := super 87 2 (by omega) (by omega)
    norm_num at hs
    omega
  have h9910 : 5 * f 1982 ≤ f 9910 := by
    have hm := mult 5 1982 (by omega) (by omega)
    norm_num at hm
    exact hm
  have hup : f 1982 ≤ 660 := by
    have hs := super 9910 89 (by omega) (by omega)
    norm_num at hs
    omega
  omega
