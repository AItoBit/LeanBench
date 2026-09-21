/--
If `1 ≤ ℓ < n`, then `ℓ` is a legal split.
-/
lemma mem_splits
    {n ℓ : ℕ}
    (hℓ1 : 1 ≤ ℓ)
    (hℓn : ℓ < n) :
    ℓ ∈ splits n := by
  simp [splits]
  omega

/--
A legal split satisfies `1 ≤ k < n`.
-/
lemma bounds_of_mem_splits
    {n k : ℕ}
    (hk : k ∈ splits n) :
    1 ≤ k ∧ k < n := by
  simp [splits] at hk
  omega

/--
Unfolding the split value.
-/
lemma splitValue_eq
    (a : ℕ → ℝ)
    (n ℓ : ℕ) :
    splitValue a n ℓ =
      a ℓ + a (n - ℓ) := by
  rfl

/-! ## Consequences of the recurrence -/

/--
Every legal split is at most the maximizing value `a n`.
-/
lemma split_le
    {a : ℕ → ℝ}
    {s n k : ℕ}
    (hrec : MaxRecurrence a s)
    (hsn : s < n)
    (hk : k ∈ splits n) :
    a k + a (n - k) ≤ a n := by

  exact
    (hrec n hsn).1 k hk

/--
For every `n > s`, some legal split realizes `a n`.
-/
lemma exists_maximizing_split
    {a : ℕ → ℝ}
    {s n : ℕ}
    (hrec : MaxRecurrence a s)
    (hsn : s < n) :
    ∃ k : ℕ,
      1 ≤ k ∧
      k < n ∧
      a n = a k + a (n - k) := by

  obtain ⟨k, hk, hval⟩ :=
    (hrec n hsn).2

  have hb :
      1 ≤ k ∧ k < n :=
    bounds_of_mem_splits hk

  refine ⟨k, hb.1, hb.2, ?_⟩

  exact hval.symm

/-! ## Stabilization interface -/

/--
Convert `TypeStabilizes` into exactly the eventual recurrence required
by the olympiad conclusion.

The threshold is enlarged once to

    max N (s + 1),

so every `n` beyond it automatically satisfies both `N ≤ n`
and `s < n`.
-/
lemma eventual_fixed_split_of_type_stabilizes
    {a : ℕ → ℝ}
    {s : ℕ}
    (hstab : TypeStabilizes a s) :
    ∃ ℓ N : ℕ,
      1 ≤ ℓ ∧
      ℓ ≤ s ∧
      ∀ n : ℕ,
        N ≤ n →
        a n = a ℓ + a (n - ℓ) := by

  obtain ⟨ℓ, N₀, hℓ1, hℓs, hmax⟩ :=
    hstab

  let N : ℕ :=
    max N₀ (s + 1)

  refine
    ⟨ℓ, N, hℓ1, hℓs, ?_⟩

  intro n hn

  have hN₀ :
      N₀ ≤ n := by
    apply le_trans
      (le_max_left N₀ (s + 1))
      hn

  have hs1 :
      s + 1 ≤ n := by
    apply le_trans
      (le_max_right N₀ (s + 1))
      hn

  have hsn :
      s < n := by
    omega

  exact
    (hmax n hN₀ hsn).symm

/-! ## Final theorem -/
