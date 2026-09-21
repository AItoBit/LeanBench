namespace Imo1977P3

/-- `m` belongs to `Vₙ`. -/
def V (n m : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ m = 1 + j * n

/-- `m` is indecomposable in `Vₙ`. -/
def Indec (n m : ℕ) : Prop := V n m ∧ ¬ ∃ p q, V n p ∧ V n q ∧ m = p * q

private lemma V_mul {n a b : ℕ} (ha : V n a) (hb : V n b) : V n (a * b) := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := hb
  exact ⟨i + j + i * j * n, by omega, by ring⟩

/-- To prove indecomposability it suffices to rule out the *smaller* factor. -/
private lemma indec_of (n m : ℕ) (hm : V n m)
    (h : ∀ p, V n p → p ∣ m → p * p ≤ m → False) : Indec n m := by
  refine ⟨hm, ?_⟩
  rintro ⟨p, q, hp, hq, hpq⟩
  rcases le_total p q with hle | hle
  · refine h p hp ⟨q, hpq⟩ ?_
    rw [hpq]
    exact Nat.mul_le_mul (le_refl p) hle
  · refine h q hq ⟨p, by rw [hpq]; ring⟩ ?_
    rw [hpq]
    exact Nat.mul_le_mul hle (le_refl q)
