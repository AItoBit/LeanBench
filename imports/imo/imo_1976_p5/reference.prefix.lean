open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 8000000

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option pp.fullNames true

set_option pp.structureInstances true

set_option pp.coercions.types true

set_option pp.funBinderTypes true

set_option pp.letVarTypes true

set_option pp.piBinderTypes true

set_option grind.warning false

namespace Imo1976P5

/-- The "number of `-1` coefficients" in row `i`, as an integer. -/
noncomputable def negCount {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) : ℤ :=
  ∑ j : Fin q, (if a i j = -1 then (1 : ℤ) else 0)

/-- The "number of `+1` coefficients" in row `i`, as an integer. -/
noncomputable def posCount {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) : ℤ :=
  ∑ j : Fin q, (if a i j = 1 then (1 : ℤ) else 0)

/-- A row cannot have more than `q` coefficients equal to `±1`. -/
lemma posCount_add_negCount_le {p q : ℕ} (a : Fin p → Fin q → ℤ) (i : Fin p) :
    posCount a i + negCount a i ≤ (q : ℤ) := by
  unfold posCount negCount
  rw [← Finset.sum_add_distrib]
  calc ∑ j : Fin q, ((if a i j = 1 then (1 : ℤ) else 0) + (if a i j = -1 then (1 : ℤ) else 0))
      ≤ ∑ _j : Fin q, (1 : ℤ) := by
        refine Finset.sum_le_sum ?_
        intro j _
        by_cases h1 : a i j = 1
        · simp [h1]
        · simp only [h1, if_false, zero_add]
          split <;> norm_num
    _ = (q : ℤ) := by simp

/-- Lower bound for a row sum when all entries `x j` lie in `[0, q]`. -/
lemma row_sum_lower {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    -(q : ℤ) * negCount a i ≤ ∑ j : Fin q, a i j * x j := by
  unfold negCount
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  rcases ha i j with h | h | h
  · have := hx0 j
    have := hxq j
    simp [h]
    linarith
  · simp [h]
  · have := hx0 j
    have h1 : (1 : ℤ) ≠ -1 := by norm_num
    simp [h, h1]
    linarith

/-- Upper bound for a row sum when all entries `x j` lie in `[0, q]`. -/
lemma row_sum_upper {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    ∑ j : Fin q, a i j * x j ≤ (q : ℤ) * posCount a i := by
  unfold posCount
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _
  rcases ha i j with h | h | h
  · have := hx0 j
    have h1 : (-1 : ℤ) ≠ 1 := by norm_num
    simp [h, h1]
    linarith
  · simp [h]
  · have := hxq j
    simp [h]
    linarith

/-- Every row sum lies in an interval of length `q ^ 2`. -/
lemma row_sum_mem_Icc {p q : ℕ} (a : Fin p → Fin q → ℤ)
    (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1)
    (x : Fin q → ℤ) (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ (q : ℤ)) (i : Fin p) :
    (∑ j : Fin q, a i j * x j) ∈
      Finset.Icc (-(q : ℤ) * negCount a i) (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2) := by
  have hlow := row_sum_lower a ha x hx0 hxq i
  have hup := row_sum_upper a ha x hx0 hxq i
  have hcount := posCount_add_negCount_le a i
  have hq : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
  refine Finset.mem_Icc.mpr ⟨hlow, ?_⟩
  have : (q : ℤ) * posCount a i ≤ -(q : ℤ) * negCount a i + (q : ℤ) ^ 2 := by
    nlinarith [hcount, hq]
  linarith
