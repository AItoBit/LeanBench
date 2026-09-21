/--
If

    a m ≡ a m * a (m + 1) [ZMOD n],

then the product through `m` is congruent to the product through `m+1`.
-/
lemma chainProd_step
    (n : ℤ)
    (a : ℕ → ℤ)
    (m : ℕ)
    (h :
      a m ≡ a m * a (m + 1) [ZMOD n]) :
    chainProd a m ≡ chainProd a (m + 1) [ZMOD n] := by
  cases m with

  | zero =>
      simpa [chainProd] using h

  | succ j =>
      have hm :=
        h.mul_left (chainProd a j)

      simpa [chainProd, mul_assoc] using hm

/--
All the consecutive congruences imply

    a 0 ≡ a 0 * ... * a m [ZMOD n].
-/
lemma first_modeq_chainProd
    (n : ℤ)
    (k : ℕ)
    (a : ℕ → ℤ)
    (hrel :
      ∀ i : ℕ,
        i + 1 < k →
          a i ≡ a i * a (i + 1) [ZMOD n]) :
    ∀ m : ℕ,
      m < k →
        a 0 ≡ chainProd a m [ZMOD n] := by

  intro m

  induction m with

  | zero =>
      intro _
      exact Int.ModEq.refl _

  | succ m ih =>
      intro hm

      have hm' : m < k := by
        omega

      have h₁ :
          a 0 ≡ chainProd a m [ZMOD n] :=
        ih hm'

      have h₂ :
          chainProd a m ≡
            chainProd a (m + 1) [ZMOD n] := by
        apply chainProd_step
        exact hrel m hm

      exact h₁.trans h₂

/-!
## Convert divisibility to congruence
-/

/--
From

    n ∣ x * (y - 1)

we obtain

    x ≡ x*y [ZMOD n].
-/
lemma modeq_of_chain_dvd
    {n x y : ℤ}
    (h : n ∣ x * (y - 1)) :
    x ≡ x * y [ZMOD n] := by

  apply Int.modEq_of_dvd

  have heq :
      x * y - x = x * (y - 1) := by
    ring

  rw [heq]

  exact h

/-!
## Congruence inside `[1,n]` implies equality
-/

/--
If `x,y ∈ [1,n]` and

    x ≡ y [ZMOD n],

then `x = y`.
-/
lemma eq_of_modeq_of_mem_interval
    {n x y : ℤ}
    (hx₁ : 1 ≤ x)
    (hxn : x ≤ n)
    (hy₁ : 1 ≤ y)
    (hyn : y ≤ n)
    (hxy : x ≡ y [ZMOD n]) :
    x = y := by

  by_cases hle : x ≤ y

  · have hdvd : n ∣ y - x := by
      exact hxy.dvd

    have hnonneg : 0 ≤ y - x := by
      omega

    have hlt : y - x < n := by
      omega

    have hz : y - x = 0 := by
      exact
        Int.eq_zero_of_dvd_of_nonneg_of_lt
          hnonneg
          hlt
          hdvd

    omega

  · have hdvd : n ∣ x - y := by
      exact hxy.symm.dvd

    have hnonneg : 0 ≤ x - y := by
      omega

    have hlt : x - y < n := by
      omega

    have hz : x - y = 0 := by
      exact
        Int.eq_zero_of_dvd_of_nonneg_of_lt
          hnonneg
          hlt
          hdvd

    omega

/-!
## IMO 2009 Problem 1
-/
