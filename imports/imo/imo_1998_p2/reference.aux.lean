lemma row_count {a b : ℕ}
    (vote : Fin a → Fin b → Bool) (i : Fin a) :
    (∑ j : Fin b, ∑ l : Fin b, agreement vote i j l) =
      (passes (vote i) : ℝ) ^ 2 +
      (failures (vote i) : ℝ) ^ 2 := by
  have h (j l : Fin b) :
      agreement vote i j l =
        (if vote i j = true then (1 : ℝ) else 0) *
          (if vote i l = true then 1 else 0) +
        (if vote i j = false then (1 : ℝ) else 0) *
          (if vote i l = false then 1 else 0) := by
    cases hj : vote i j <;> cases hl : vote i l <;>
      simp [agreement, hj, hl]
  simp_rw [
    h,
    Finset.sum_add_distrib,
    ← Finset.mul_sum,
    ← Finset.sum_mul
  ]
  simp [passes, failures, pow_two]

lemma split_count {b : ℕ} (v : Fin b → Bool) :
    passes v + failures v = b := by
  calc
    passes v + failures v =
        ∑ j : Fin b,
          ((if v j = true then 1 else 0) +
            (if v j = false then 1 else 0) : ℕ) := by
      simp [passes, failures, Finset.sum_add_distrib]
    _ = ∑ _j : Fin b, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      cases v j <;> simp
    _ = b := by simp

lemma odd_square_bound {p q b : ℕ}
    (hs : p + q = b) (hb : Odd b) :
    (b : ℝ) ^ 2 + 1 ≤
      2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
  obtain ⟨m, hm⟩ := hb
  have hne : p ≠ q := by omega
  have hsR : (p : ℝ) + q = b := by
    exact_mod_cast hs
  have hs2 :
      ((p : ℝ) + q) ^ 2 = (b : ℝ) ^ 2 :=
    congrArg (fun z : ℝ => z ^ 2) hsR
  rcases lt_or_gt_of_ne hne with h | h
  · have hgap : (p : ℝ) + 1 ≤ q := by
      exact_mod_cast h
    nlinarith [sq_nonneg ((q : ℝ) - p - 1)]
  · have hgap : (q : ℝ) + 1 ≤ p := by
      exact_mod_cast h
    nlinarith [sq_nonneg ((p : ℝ) - q - 1)]
