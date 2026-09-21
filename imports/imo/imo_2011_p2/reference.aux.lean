/--
If a sequence does not change at any adjacent step from `m`
through `m+d`, then the endpoint values are equal.
-/
lemma constant_of_no_adjacent_change
    {α : Type*}
    (c : ℕ → α)
    (m d : ℕ)
    (h :
      ∀ j : ℕ,
        m ≤ j →
        j < m + d →
        c j = c (j + 1)) :
    c m = c (m + d) := by

  induction d generalizing m with

  | zero =>
      simp

  | succ d ih =>

      have hfirst :
          c m = c (m + 1) := by
        apply h

        · omega

        · omega

      have htail :
          ∀ j : ℕ,
            m + 1 ≤ j →
            j < (m + 1) + d →
            c j = c (j + 1) := by

        intro j hj₁ hj₂

        apply h

        · omega

        · omega

      have hrec :
          c (m + 1) =
            c ((m + 1) + d) :=
        ih (m + 1) htail

      have hadd :
          (m + 1) + d =
            m + (d + 1) := by
        omega

      calc
        c m
            = c (m + 1) := hfirst

        _ = c ((m + 1) + d) := hrec

        _ = c (m + (d + 1)) := by
              rw [hadd]

/--
If two values of a sequence at indices `m<n` are different,
there must be an adjacent change somewhere between them.
-/
lemma exists_adjacent_change
    {α : Type*}
    (c : ℕ → α)
    {m n : ℕ}
    (hmn : m < n)
    (hne : c m ≠ c n) :
    ∃ j : ℕ,
      m ≤ j ∧
      j < n ∧
      c j ≠ c (j + 1) := by

  have hmn' :
      m ≤ n :=
    Nat.le_of_lt hmn

  obtain ⟨d, hd⟩ :=
    Nat.exists_eq_add_of_le hmn'

  subst n

  by_contra hnone

  have hall :
      ∀ j : ℕ,
        m ≤ j →
        j < m + d →
        c j = c (j + 1) := by

    intro j hj₁ hj₂

    by_contra hchange

    apply hnone

    exact
      ⟨j, hj₁, hj₂, hchange⟩

  have heq :
      c m = c (m + d) :=
    constant_of_no_adjacent_change
      c
      m
      d
      hall

  exact hne heq

/-!
## Boolean flip
-/

/--
A Boolean is never equal to its negation.
-/
lemma bool_ne_not
    (b : Bool) :
    b ≠ !b := by
  cases b <;> decide

/-!
## Every half-turn contains the point as pivot
-/

/--
A point must occur as a pivot during every half-turn interval.

If the interval starts at time `s`, there is some pivot index
`t` between `s` and `s + period` involving `p`.
-/
lemma pivot_occurs_in_half_turn
    {N : ℕ}
    (W : HalfTurnWindmill N)
    (p : Fin N)
    (s : ℕ) :
    ∃ t : ℕ,
      s ≤ t ∧
      t ≤ s + W.period ∧
      W.pivot t = p := by

  have hperiod :
      0 < W.period :=
    W.period_pos

  have hend :
      s < s + W.period := by
    omega

  have hflip :=
    W.half_turn_flip s p

  have hne :
      W.color s p ≠
        W.color (s + W.period) p := by

    rw [hflip]

    exact bool_ne_not _

  obtain ⟨j, hsj, hjend, hchange⟩ :=
    exists_adjacent_change
      (fun t => W.color t p)
      hend
      hne

  have hpivot :=
    W.color_change_pivot
      j p hchange

  rcases hpivot with hpivot | hpivot

  · refine ⟨j, hsj, ?_, hpivot.symm⟩

    omega

  · refine ⟨j + 1, ?_, ?_, hpivot.symm⟩

    · omega

    · omega

/-!
## Infinitely often
-/

/--
Every point is a pivot infinitely often.
-/
theorem every_point_pivots_infinitely_often
    {N : ℕ}
    (W : HalfTurnWindmill N)
    (p : Fin N) :
    PivotsInfinitelyOften W p := by

  intro B

  let s : ℕ :=
    B + W.period

  have hperiod :
      0 < W.period :=
    W.period_pos

  have hBs :
      B < s := by
    dsimp [s]
    omega

  obtain ⟨t, hst, htend, hpivot⟩ :=
    pivot_occurs_in_half_turn
      W
      p
      s

  refine ⟨t, ?_, hpivot⟩

  exact
    lt_of_lt_of_le
      hBs
      hst

/-!
## Final theorem
-/
