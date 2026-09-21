by
  rintro ⟨f, hf⟩
  -- Step 1: shifting by 1987.
  have hshift : ∀ n, f (n + 1987) = f n + 1987 := by
    intro n
    rw [← hf n, hf (f n)]
  have hshiftk : ∀ n k, f (n + 1987 * k) = f n + 1987 * k := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      calc f (n + 1987 * (k + 1)) = f ((n + 1987 * k) + 1987) := congrArg f (by ring)
        _ = f (n + 1987 * k) + 1987 := hshift _
        _ = f n + 1987 * (k + 1) := by omega
  -- Step 2: `f n mod 1987` depends only on `n mod 1987`.
  have hmod : ∀ n, f n % 1987 = f (n % 1987) % 1987 := by
    intro n
    have h := hshiftk (n % 1987) (n / 1987)
    rw [Nat.mod_add_div] at h
    rw [h]
    omega
  have hinv : ∀ r, r < 1987 → f (f r % 1987) % 1987 = r := by
    intro r hr
    rw [← hmod (f r), hf r]
    omega
  -- Step 3: no fixed point.
  have hnofix : ∀ r, r < 1987 → f r % 1987 ≠ r := by
    intro r _ hfix
    have h1 : f r = r + 1987 * (f r / 1987) := by
      have := Nat.mod_add_div (f r) 1987
      omega
    have h2 := hshiftk r (f r / 1987)
    rw [← h1, hf r] at h2
    omega
  -- Step 4: parity contradiction.
  have hprod : ∏ _x ∈ Finset.range 1987, (-1 : ℤ) = 1 := by
    refine Finset.prod_involution
      (fun (a : ℕ) (_ : a ∈ Finset.range 1987) => f a % 1987) ?_ ?_ ?_ ?_
    · intro a _
      norm_num
    · intro a ha _
      exact hnofix a (Finset.mem_range.mp ha)
    · intro a _
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by norm_num))
    · intro a ha
      exact hinv a (Finset.mem_range.mp ha)
  rw [Finset.prod_const, Finset.card_range] at hprod
  norm_num at hprod
