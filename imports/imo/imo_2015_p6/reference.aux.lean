/--
If

    a_j - b = w_{j+1} - w_j

eventually, then a consecutive block telescopes.
-/
lemma telescoping_len
    (a w : ℕ → ℤ)
    (b : ℤ)
    (N m len : ℕ)
    (hm : N ≤ m)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j) :
    (∑ i ∈ Finset.range len,
        (a (m + 1 + i) - b))
      =
    w (m + 1 + len) -
      w (m + 1) := by

  induction len with

  | zero =>
      simp

  | succ len ih =>

      rw [Finset.sum_range_succ]

      rw [ih]

      have hj :
          N ≤ m + 1 + len := by
        omega

      rw [hrec (m + 1 + len) hj]

      have hidx :
          m + 1 + (len + 1) =
            (m + 1 + len) + 1 := by
        omega

      rw [hidx]

      ring

/--
Version indexed by the original endpoints `m,n`.
-/
lemma blockDeviation_eq
    (a w : ℕ → ℤ)
    (b : ℤ)
    (N m n : ℕ)
    (hm : N ≤ m)
    (hmn : m < n)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j) :
    BlockDeviation a b m n =
      w (n + 1) - w (m + 1) := by

  unfold BlockDeviation

  have htel :=
    telescoping_len
      a
      w
      b
      N
      m
      (n - m)
      hm
      hrec

  have hidx :
      m + 1 + (n - m) =
        n + 1 := by
    omega

  rw [hidx] at htel

  exact htel

/-!
## Bounding a difference
-/

/--
If `x,y ∈ [0,B]`, then

    |x-y| ≤ B.
-/
lemma abs_sub_le_bound
    {x y B : ℤ}
    (hx0 : 0 ≤ x)
    (hxB : x ≤ B)
    (hy0 : 0 ≤ y)
    (hyB : y ≤ B) :
    abs (x - y) ≤ B := by

  rw [abs_le]

  constructor <;>
    linarith

/-!
## Bound obtained from the pattern weights
-/

/--
If every eventual weight lies in `[0,B]`,
then every telescoping block has absolute value at most `B`.
-/
lemma blockDeviation_le_weight_range
    (a w : ℕ → ℤ)
    (b B : ℤ)
    (N m n : ℕ)
    (hm : N ≤ m)
    (hmn : m < n)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - b =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧ w j ≤ B) :
    abs (BlockDeviation a b m n) ≤ B := by

  have hsum :
      BlockDeviation a b m n =
        w (n + 1) - w (m + 1) :=
    blockDeviation_eq
      a
      w
      b
      N
      m
      n
      hm
      hmn
      hrec

  have hm1 :
      N ≤ m + 1 := by
    omega

  have hn1 :
      N ≤ n + 1 := by
    omega

  obtain ⟨hwm0, hwmB⟩ :=
    hweight (m + 1) hm1

  obtain ⟨hwn0, hwnB⟩ :=
    hweight (n + 1) hn1

  rw [hsum]

  exact
    abs_sub_le_bound
      hwn0
      hwnB
      hwm0
      hwmB

/-!
## The numerical 1007² bound
-/

/--
For `0 ≤ v ≤ 2014`,

    (2014-v)v ≤ 1007².

This is simply

    (v-1007)² ≥ 0.
-/
lemma volume_weight_le_1007_sq
    {v : ℤ}
    (hv0 : 0 ≤ v)
    (hv2014 : v ≤ 2014) :
    (2014 - v) * v ≤
      (1007 : ℤ) ^ 2 := by

  have hsquare :
      0 ≤ (v - 1007) ^ 2 :=
    sq_nonneg (v - 1007)

  nlinarith

/-!
## General final theorem for the eventual pattern
-/

/--
Once the eventual pattern supplied by the source has been
constructed, its recurrence and weight bounds imply the
required IMO estimate.
-/
theorem eventual_pattern_bound
    (a w : ℕ → ℤ)
    (v : ℤ)
    (N : ℕ)
    (hv0 :
      0 ≤ v)
    (hv2014 :
      v ≤ 2014)
    (hrec :
      ∀ j : ℕ,
        N ≤ j →
        a j - (v + 1) =
          w (j + 1) - w j)
    (hweight :
      ∀ j : ℕ,
        N ≤ j →
        0 ≤ w j ∧
        w j ≤ (2014 - v) * v) :
    ∀ m n : ℕ,
      N ≤ m →
      m < n →
      abs
          (BlockDeviation
            a
            (v + 1)
            m
            n)
        ≤
      (1007 : ℤ) ^ 2 := by

  intro m n hm hmn

  have hB :
      0 ≤ (2014 - v) * v := by
    exact
      mul_nonneg
        (sub_nonneg.mpr hv2014)
        hv0

  have hblock :
      abs
          (BlockDeviation
            a
            (v + 1)
            m
            n)
        ≤
      (2014 - v) * v := by

    exact
      blockDeviation_le_weight_range
        a
        w
        (v + 1)
        ((2014 - v) * v)
        N
        m
        n
        hm
        hmn
        hrec
        hweight

  have hmax :
      (2014 - v) * v ≤
        (1007 : ℤ) ^ 2 :=
    volume_weight_le_1007_sq
      hv0
      hv2014

  exact
    le_trans
      hblock
      hmax

/-!
## Exact existential form requested by IMO 2015 P6
-/
