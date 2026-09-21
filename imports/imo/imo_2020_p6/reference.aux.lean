lemma lineDistance_nonneg
    (L : Line)
    (x : Point) :
    0 ≤ lineDistance L x := by
  unfold lineDistance
  exact abs_nonneg _

/-!
============================================================
4. Separation
============================================================
-/

lemma HasSeparatingLine.mono
    {S : Finset Point}
    {δ₁ δ₂ : ℝ}
    (hδ : δ₁ ≤ δ₂)
    (h : HasSeparatingLine S δ₂) :
    HasSeparatingLine S δ₁ := by

  obtain ⟨L, hsep, hdist⟩ := h

  refine ⟨L, hsep, ?_⟩

  intro x hx

  exact
    le_trans
      hδ
      (hdist x hx)

/-!
============================================================
7. n^(-1/3)
============================================================
-/

lemma nScale_nonneg
    (n : ℕ) :
    0 ≤ nScale n := by

  unfold nScale

  have hn0 :
      0 ≤ (n : ℝ) := by
    positivity

  have hrpow :
      0 ≤
        Real.rpow
          (n : ℝ)
          ((1 : ℝ) / 3) := by
    exact
      Real.rpow_nonneg
        hn0
        ((1 : ℝ) / 3)

  exact
    one_div_nonneg.mpr
      hrpow

lemma nScale_pos
    {n : ℕ}
    (hn : 0 < n) :
    0 < nScale n := by

  unfold nScale

  have hnreal :
      0 < (n : ℝ) := by
    exact_mod_cast hn

  have hrpow :
      0 <
        Real.rpow
          (n : ℝ)
          ((1 : ℝ) / 3) := by
    exact
      Real.rpow_pos_of_pos
        hnreal
        ((1 : ℝ) / 3)

  exact
    one_div_pos.mpr
      hrpow

/-!
============================================================
8. Scaling constants
============================================================
-/

lemma constant_scale_mono
    {C₁ C₂ : ℝ}
    (n : ℕ)
    (hC : C₁ ≤ C₂) :
    C₁ * nScale n
      ≤
    C₂ * nScale n := by

  exact
    mul_le_mul_of_nonneg_right
      hC
      (nScale_nonneg n)

/-!
============================================================
9. Abstract large-width case
============================================================
-/

/-
`Wide n S` represents the large-width alternative in the
source solution.
-/

theorem combine_cases
    (Cw Cn : ℝ)
    (hCw : 0 < Cw)
    (hCn : 0 < Cn)

    (wide_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          Wide n S →
          HasSeparatingLine
            S
            (Cw * nScale n))

    (narrow_case :
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          ¬ Wide n S →
          HasSeparatingLine
            S
            (Cn * nScale n)) :

    ∃ C : ℝ,
      0 < C ∧
      ∀ n : ℕ,
        ∀ S : Finset Point,
          1 < n →
          S.card = n →
          UnitSeparated S →
          HasSeparatingLine
            S
            (C * nScale n) := by

  let C : ℝ :=
    min Cw Cn

  have hCpos :
      0 < C := by
    unfold C
    exact
      lt_min
        hCw
        hCn

  refine
    ⟨C,
     hCpos,
     ?_⟩

  intro n S hn hcard hsep

  by_cases hwide :
      Wide n S

  · have hw :
        HasSeparatingLine
          S
          (Cw * nScale n) :=
      wide_case
        n
        S
        hn
        hcard
        hsep
        hwide

    have hCle :
        C ≤ Cw := by
      unfold C
      exact
        min_le_left
          Cw
          Cn

    have hscale :
        C * nScale n
          ≤
        Cw * nScale n :=
      constant_scale_mono
        n
        hCle

    exact
      HasSeparatingLine.mono
        hscale
        hw

  · have hnarrow :
        HasSeparatingLine
          S
          (Cn * nScale n) :=
      narrow_case
        n
        S
        hn
        hcard
        hsep
        hwide

    have hCle :
        C ≤ Cn := by
      unfold C
      exact
        min_le_right
          Cw
          Cn

    have hscale :
        C * nScale n
          ≤
        Cn * nScale n :=
      constant_scale_mono
        n
        hCle

    exact
      HasSeparatingLine.mono
        hscale
        hnarrow

/-!
============================================================
11. IMO 2020 Problem 6 wrapper
============================================================
-/
