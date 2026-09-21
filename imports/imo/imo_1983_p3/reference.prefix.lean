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

namespace Imo1983P3

/-- Auxiliary: if `u` and `v` are coprime integers and `v > 0`, then for every integer `n`
there is a natural number `x < v` with `v ∣ n - x * u`. -/
lemma exists_small_nat_smul_congr {u v : ℤ} (hv : 0 < v) (h : IsCoprime u v) (n : ℤ) :
    ∃ x : ℕ, (x : ℤ) < v ∧ v ∣ n - x * u := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨((n * s) % v).toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hv))]
    exact Int.emod_lt_of_pos _ hv
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hv))]
    refine ⟨n * t + ((n * s) / v) * u, ?_⟩
    have hd : (n * s) % v = n * s - v * ((n * s) / v) := Int.emod_def _ _
    rw [hd]
    linear_combination (-n) * hst

/-- Chicken McNugget / Sylvester, integer form: if `b`, `c` are coprime positive naturals then
every integer `m` with `(b-1)*(c-1) ≤ m` can be written as `y*c + z*b` with `y z : ℕ`. -/
lemma exists_repr_of_ge {b c : ℕ} (hb : 0 < b) (hcop : Nat.Coprime b c) (m : ℤ)
    (hm : ((b : ℤ) - 1) * ((c : ℤ) - 1) ≤ m) :
    ∃ y z : ℕ, m = y * c + z * b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hcop' : IsCoprime (c : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨y, hylt, hdvd⟩ := exists_small_nat_smul_congr hb' hcop' m
  obtain ⟨z, hz⟩ := hdvd
  have hyle : (y : ℤ) ≤ (b : ℤ) - 1 := by omega
  have hzpos : 0 ≤ z := by
    by_contra hneg
    push_neg at hneg
    have hz1 : z ≤ -1 := by omega
    have : m - y * c ≤ -(b : ℤ) := by
      calc m - y * c = b * z := hz
        _ ≤ b * (-1) := by
            exact mul_le_mul_of_nonneg_left hz1 (le_of_lt hb')
        _ = -(b : ℤ) := by ring
    nlinarith [hm, hyle, hz]
  refine ⟨y, z.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hzpos]
  linarith [hz]
