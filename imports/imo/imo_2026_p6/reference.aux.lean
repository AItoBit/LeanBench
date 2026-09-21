lemma succ_add_shift
    (n T : ℕ) :
    (n + 1) + T =
      (n + T) + 1 := by

  omega

/-!
============================================================
3. Main recurrence induction
============================================================
-/

theorem translation_recurrence
    {a next : ℕ → ℕ}
    {T L : ℕ}
    (hrec :
      FollowsNext a next)
    (htrans :
      NextTranslationInvariant next L)
    (hbase :
      a T = a 0 + L) :
    ∀ n : ℕ,
      a (n + T) =
        a n + L := by

  intro n

  induction n with

  | zero =>
      simpa using hbase

  | succ n ih =>

      have hrec_left :
          a ((n + T) + 1) =
            next (a (n + T)) :=
        hrec (n + T)

      have hrec_right :
          a (n + 1) =
            next (a n) :=
        hrec n

      calc
        a ((n + 1) + T)
            =
          a ((n + T) + 1) := by
            rw [succ_add_shift]

        _ =
          next (a (n + T)) :=
            hrec_left

        _ =
          next (a n + L) := by
            rw [ih]

        _ =
          next (a n) + L :=
            htrans (a n)

        _ =
          a (n + 1) + L := by
            rw [hrec_right]

/-!
============================================================
4. Positive-period formulation
============================================================
-/

theorem periodic_translation_of_next
    {a next : ℕ → ℕ}
    {T L : ℕ}
    (hT :
      0 < T)
    (hL :
      0 < L)
    (hrec :
      FollowsNext a next)
    (htrans :
      NextTranslationInvariant next L)
    (hbase :
      a T =
        a 0 + L) :
    HasPeriodicTranslation a := by

  refine
    ⟨T, L, hT, hL, ?_⟩

  exact
    translation_recurrence
      hrec
      htrans
      hbase

/-!
============================================================
5. One-based indexing
============================================================
-/

lemma zero_based_implies_one_based
    {a : ℕ → ℕ}
    (h :
      HasPeriodicTranslation a) :
    HasPeriodicTranslationOneBased a := by

  rcases h with
    ⟨T, L, hT, hL, hshift⟩

  refine
    ⟨T, L, hT, hL, ?_⟩

  intro n hn

  exact
    hshift n

/-!
============================================================
6. Set of sequence values
============================================================
-/

lemma value_mem
    (a : ℕ → ℕ)
    (n : ℕ) :
    a n ∈ Values a := by

  exact
    ⟨n, rfl⟩

/-!
============================================================
7. Eventual translation invariance
============================================================
-/

lemma mem_add_of_eventually_translation_invariant
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m ∈ A) :
    m + L ∈ A := by

  exact
    (h m hm).mp
      hmem

/-!
============================================================
9. Backward membership translation
============================================================
-/

lemma mem_of_add_mem
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m + L ∈ A) :
    m ∈ A := by

  exact
    (h m hm).mpr
      hmem

/-!
============================================================
10. Repeated translations
============================================================
-/

lemma mem_add_mul
    {A : Set ℕ}
    {start L m : ℕ}
    (h :
      EventuallyTranslationInvariant A start L)
    (hm :
      start ≤ m)
    (hmem :
      m ∈ A) :
    ∀ k : ℕ,
      m + k * L ∈ A := by

  intro k

  induction k with

  | zero =>
      simpa using hmem

  | succ k ih =>

      have hm_le :
          m ≤ m + k * L := by
        exact
          Nat.le_add_right
            m
            (k * L)

      have hmk :
          start ≤ m + k * L :=
        le_trans
          hm
          hm_le

      have hnext :
          (m + k * L) + L ∈ A :=
        (h (m + k * L) hmk).mp
          ih

      have hindex :
          m + (k + 1) * L =
            (m + k * L) + L := by
        ring

      rw [hindex]

      exact hnext

/-!
============================================================
11. Source reduction data
============================================================
-/

/-
IMPORTANT:

This structure must live in `Type`, not `Prop`, because
it contains actual data fields `T : ℕ` and `L : ℕ`.
-/

theorem imo2026_p6_core
    {a next : ℕ → ℕ}
    (D :
      SourcePeriodData a next) :
    ∃ T L : ℕ,
      0 < T ∧
      0 < L ∧
      ∀ n : ℕ,
        a (n + T) =
          a n + L := by

  refine
    ⟨D.T,
     D.L,
     D.T_pos,
     D.L_pos,
     ?_⟩

  exact
    translation_recurrence
      D.recurrence
      D.next_translation
      D.first_period

/-!
============================================================
13. Compact final theorem
============================================================
-/
