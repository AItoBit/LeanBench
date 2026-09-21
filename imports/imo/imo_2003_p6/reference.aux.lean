/-- Splitting off the two lowest terms of a geometric sum. -/
theorem geom_split (x k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), x ^ i = 1 + x + x ^ 2 * ∑ i ∈ Finset.range k, x ^ i := by
  induction k with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- A product of naturals each `≡ 1 (mod m)` is `≡ 1 (mod m)`. -/
theorem list_prod_modEq_one {m : ℕ} :
    ∀ l : List ℕ, (∀ x ∈ l, x ≡ 1 [MOD m]) → l.prod ≡ 1 [MOD m] := by
  intro l
  induction l with
  | nil => intro _; simp [Nat.ModEq]
  | cons a t ih =>
      intro h
      rw [List.prod_cons]
      have h1 : a ≡ 1 [MOD m] := h a (by simp)
      have h2 : t.prod ≡ 1 [MOD m] := ih fun x hx => h x (by simp [hx])
      simpa using h1.mul h2
