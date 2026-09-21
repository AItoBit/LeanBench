/-- Splitting a sum over `range (2 * N)` into its even- and odd-indexed parts. -/
lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ m ∈ Finset.range (2 * N), f m = ∑ k ∈ Finset.range N, (f (2 * k) + f (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [add_assoc]

/-- A finite sum in `ℤ√2` is computed componentwise. -/
lemma sum_mk (f g : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (⟨f k, g k⟩ : Zsqrtd 2)
      = ⟨∑ k ∈ Finset.range N, f k, ∑ k ∈ Finset.range N, g k⟩ := by
  induction N with
  | zero => simp; rfl
  | succ n ih => simp [Finset.sum_range_succ, ih]

lemma sqrtd_two_mul (k : ℕ) : (Zsqrtd.sqrtd (d := 2)) ^ (2 * k) = ⟨2 ^ k, 0⟩ := by
  rw [pow_mul]
  have h : (Zsqrtd.sqrtd (d := 2)) ^ 2 = ⟨2, 0⟩ := by ext <;> simp [pow_two]
  rw [h]
  induction k with
  | zero => rfl
  | succ m ih => rw [pow_succ, pow_succ, ih]; ext <;> simp

/-- `(1 + √2) ^ (2n+1) = A n + B n * √2` inside `ℤ√2`. -/
lemma pow_eq (n : ℕ) : (⟨1, 1⟩ : Zsqrtd 2) ^ (2 * n + 1) = ⟨A n, B n⟩ := by
  have hbase : (⟨1, 1⟩ : Zsqrtd 2) = Zsqrtd.sqrtd + 1 := by ext <;> simp
  rw [hbase, add_pow]
  have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
  rw [h2, sum_range_two_mul]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (Zsqrtd.sqrtd (d := 2)) ^ (2 * k) * 1 ^ (2 * n + 1 - 2 * k)
          * ((2 * n + 1).choose (2 * k) : ℤ√2)
        + (Zsqrtd.sqrtd (d := 2)) ^ (2 * k + 1) * 1 ^ (2 * n + 1 - (2 * k + 1))
          * ((2 * n + 1).choose (2 * k + 1) : ℤ√2)
      = (⟨((2 * n + 1).choose (2 * k) : ℤ) * 2 ^ k,
          ((2 * n + 1).choose (2 * k + 1) : ℤ) * 2 ^ k⟩ : Zsqrtd 2) := by
    intro k _
    rw [sqrtd_two_mul, pow_succ, sqrtd_two_mul]
    ext <;> simp <;> ring
  rw [Finset.sum_congr rfl hterm, sum_mk]
  rfl

/-- The Pell identity `A n ^ 2 - 2 * B n ^ 2 = -1`. -/
lemma pell (n : ℕ) : A n ^ 2 - 2 * B n ^ 2 = -1 := by
  have hn : ((⟨1, 1⟩ : Zsqrtd 2) ^ (2 * n + 1)).norm
      = (Zsqrtd.norm (⟨1, 1⟩ : Zsqrtd 2)) ^ (2 * n + 1) :=
    map_pow (Zsqrtd.normMonoidHom (d := 2)) _ _
  rw [pow_eq n] at hn
  have h1 : (Zsqrtd.norm (⟨1, 1⟩ : Zsqrtd 2)) = -1 := by simp [Zsqrtd.norm_def]
  rw [h1, Odd.neg_one_pow ⟨n, by ring⟩, Zsqrtd.norm_def] at hn
  simp only at hn
  linear_combination hn

/-- Modulo `5` we have `2 ^ n * S n = A n`. -/
lemma key (n : ℕ) : (2 : ZMod 5) ^ n * (S n : ZMod 5) = ((A n : ℤ) : ZMod 5) := by
  rw [S, A]
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_range_reflect
    (fun k => (2 : ZMod 5) ^ n * ((((2 * n + 1).choose (2 * k + 1) : ℕ) : ZMod 5) * 2 ^ (3 * k)))]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  have hidx : n + 1 - 1 - k = n - k := by omega
  simp only [hidx]
  have hch : (2 * n + 1).choose (2 * (n - k) + 1) = (2 * n + 1).choose (2 * k) := by
    have h : 2 * (n - k) + 1 = (2 * n + 1) - 2 * k := by omega
    rw [h, Nat.choose_symm (by omega)]
  rw [hch]
  have hexp : (2 : ZMod 5) ^ n * 2 ^ (3 * (n - k)) = 2 ^ k := by
    rw [← pow_add]
    have h4 : n + 3 * (n - k) = 4 * (n - k) + k := by omega
    rw [h4, pow_add, pow_mul]
    have h16 : ((2 : ZMod 5) ^ 4) = 1 := by decide
    rw [h16, one_pow, one_mul]
  calc (2 : ZMod 5) ^ n * ((((2 * n + 1).choose (2 * k) : ℕ) : ZMod 5) * 2 ^ (3 * (n - k)))
      = (((2 * n + 1).choose (2 * k) : ℕ) : ZMod 5) * ((2 : ZMod 5) ^ n * 2 ^ (3 * (n - k))) := by
        ring
    _ = _ := by rw [hexp]
