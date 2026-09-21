by
  have hm := m_eq_mul n
  obtain ⟨t, ht⟩ := cyclen_odd n hn
  have hgc : gcd3 n * (cyclen n - 1) = 2 * n - 1 - gcd3 n := by
    rw [Nat.mul_sub, Nat.mul_one, ← hm]
  have heven : 2 * ((2 * n - 1 - gcd3 n) / 2) = 2 * n - 1 - gcd3 n := by
    rw [← hgc, ht]
    have h1 : 2 * t + 1 - 1 = 2 * t := by omega
    rw [h1]
    have h2 : gcd3 n * (2 * t) = 2 * (gcd3 n * t) := by ring
    rw [h2, Nat.mul_div_cancel_left _ (by norm_num)]
  constructor
  · intro S hS
    by_contra hbad
    rw [good_iff n hn] at hbad
    push Not at hbad
    have hle := bad_card_le n hn S hbad
    rw [hS, answer_eq n hn] at hle
    omega
  · intro k hk
    by_contra hlt
    push Not at hlt
    rw [answer_eq n hn] at hlt
    have hcard := badSet_card n hn
    have hle : k ≤ (badSet n).card := by rw [hcard]; omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hle
    have hgood := hk B hBcard
    rw [good_iff n hn] at hgood
    obtain ⟨x, hx, hx'⟩ := hgood
    exact badSet_bad n hn x (hBsub hx) (hBsub hx')
