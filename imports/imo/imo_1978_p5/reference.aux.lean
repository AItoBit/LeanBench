/-- **Abel summation bound.** If all the partial sums `∑_{k=1}^m d k` are nonnegative and the
weights `w` are nonincreasing on `{1, 2, …}`, then the weighted partial sum dominates `w n`
times the partial sum of `d`. -/
theorem partial_weighted_sum_ge (d w : ℕ → ℝ)
    (hw : ∀ i : ℕ, 1 ≤ i → w (i + 1) ≤ w i)
    (hD : ∀ m : ℕ, 0 ≤ ∑ k ∈ Finset.Icc 1 m, d k) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, d k) * w n ≤ ∑ k ∈ Finset.Icc 1 n, d k * w k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have key : (∑ k ∈ Finset.Icc 1 n, d k) * w (n + 1) ≤ (∑ k ∈ Finset.Icc 1 n, d k) * w n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact mul_le_mul_of_nonneg_left (hw n h) (hD n)
    nlinarith [ih, key]

/-- **Abel summation bound, weak form.** If all the partial sums `∑_{k=1}^m d k` are nonnegative
and the weights `w` are nonnegative and nonincreasing on `{1, 2, …}`, then the weighted sum is
nonnegative. -/
theorem weighted_sum_nonneg (d w : ℕ → ℝ)
    (hw : ∀ i : ℕ, 1 ≤ i → w (i + 1) ≤ w i)
    (hwpos : ∀ i : ℕ, 1 ≤ i → 0 ≤ w i)
    (hD : ∀ m : ℕ, 0 ≤ ∑ k ∈ Finset.Icc 1 m, d k) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 n, d k * w k := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact le_trans (mul_nonneg (hD n) (hwpos n h)) (partial_weighted_sum_ge d w hw hD n)

/-- The sum of the `m` distinct positive integers `f 1, …, f m` is at least `1 + 2 + ⋯ + m`. -/
theorem sum_le_sum_of_injOn (f : ℕ → ℕ) (hinj : Set.InjOn f {k : ℕ | 1 ≤ k})
    (hpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ f k) (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, k ≤ ∑ k ∈ Finset.Icc 1 m, f k := by
  have hgauss : ∑ n ∈ Finset.range m, (1 + (n : ℤ)) = ∑ k ∈ Finset.Icc 1 m, (k : ℤ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
      push_cast
      ring
  set s : Finset ℤ := (Finset.Icc 1 m).image (fun k => (f k : ℤ)) with hs
  have hinj' : Set.InjOn (fun k => (f k : ℤ)) (Finset.Icc 1 m : Finset ℕ) := by
    intro a ha b hb hab
    have hab' : (f a : ℤ) = (f b : ℤ) := hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    exact hinj (by simpa using ha.1) (by simpa using hb.1) (by exact_mod_cast hab')
  have hcard : s.card = m := by
    rw [hs, Finset.card_image_of_injOn hinj', Nat.card_Icc]
    omega
  have hsum : ∑ x ∈ s, x = ∑ k ∈ Finset.Icc 1 m, (f k : ℤ) := by
    rw [hs, Finset.sum_image (fun a ha b hb h => hinj' ha hb h)]
  have hb : ∀ x ∈ s, (1 : ℤ) ≤ x := by
    intro x hx
    rw [hs] at hx
    simp only [Finset.mem_image, Finset.mem_Icc] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact_mod_cast hpos k hk.1
  have hmain := Finset.sum_range_le_sum hb
  rw [hcard, hsum, hgauss, ← Nat.cast_sum, ← Nat.cast_sum] at hmain
  exact_mod_cast hmain
