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

/-!
## IMO 1970, Problem 4

Find the set of all positive integers `n` with the property that the set
`{n, n+1, n+2, n+3, n+4, n+5}` can be partitioned into two sets such that the
product of the numbers in one set equals the product of the numbers in the
other set.

The answer is that **there is no such `n`**: the set of such `n` is empty.

A partition of the block into two parts is recorded by one part `A`; the other
part is then `block n \ A`.
-/

namespace IMO1970P4

/-- The block `{n, n+1, n+2, n+3, n+4, n+5}` of six consecutive integers. -/
def block (n : ℕ) : Finset ℕ := Finset.Icc n (n + 5)

/-- `A` is one part of a partition of `block n` into two parts with equal products. -/
def Balanced (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ block n ∧ ∏ x ∈ A, x = ∏ x ∈ block n \ A, x

/-- If a prime `p` divides some member of a block admitting a balanced partition,
then `p` divides two *distinct* members of the block: indeed `p` divides the
common value of the two products, hence divides a member of each part. -/
theorem exists_two_distinct_multiples {n : ℕ} {A : Finset ℕ} (h : Balanced n A)
    {p m : ℕ} (hp : p.Prime) (hm : m ∈ block n) (hpm : p ∣ m) :
    ∃ a ∈ block n, ∃ b ∈ block n, a ≠ b ∧ p ∣ a ∧ p ∣ b := by
  obtain ⟨hA, heq⟩ := h
  have hprod : (∏ x ∈ block n \ A, x) * (∏ x ∈ A, x) = ∏ x ∈ block n, x :=
    Finset.prod_sdiff hA
  have hdvd : p ∣ ∏ x ∈ block n, x := hpm.trans (Finset.dvd_prod_of_mem id hm)
  rw [← hprod, ← heq] at hdvd
  have hpA : p ∣ ∏ x ∈ A, x := (hp.prime.dvd_mul.mp hdvd).elim id id
  have hpB : p ∣ ∏ x ∈ block n \ A, x := heq ▸ hpA
  obtain ⟨a, ha, hpa⟩ := hp.prime.exists_mem_finset_dvd hpA
  obtain ⟨b, hb, hpb⟩ := hp.prime.exists_mem_finset_dvd hpB
  refine ⟨a, hA ha, b, Finset.sdiff_subset hb, ?_, hpa, hpb⟩
  rintro rfl
  exact (Finset.mem_sdiff.mp hb).2 ha

/-- Every member of a block admitting a balanced partition is `5`-smooth: a prime
`p ≥ 7` could divide at most one of six consecutive integers. -/
theorem prime_factor_le_five {n : ℕ} {A : Finset ℕ} (h : Balanced n A)
    {p m : ℕ} (hp : p.Prime) (hm : m ∈ block n) (hpm : p ∣ m) : p ≤ 5 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, ha, b, hb, hab, hpa, hpb⟩ := exists_two_distinct_multiples h hp hm hpm
  simp only [block, Finset.mem_Icc] at ha hb
  rcases lt_or_gt_of_ne hab with hlt2 | hlt2
  · have hd : p ∣ b - a := Nat.dvd_sub hpb hpa
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : p ∣ a - b := Nat.dvd_sub hpa hpb
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- A `5`-smooth number divisible by none of `2`, `3`, `5` equals `1`. -/
theorem eq_one_of_smooth {t : ℕ} (hsmooth : ∀ p : ℕ, p.Prime → p ∣ t → p ≤ 5)
    (h2 : ¬ 2 ∣ t) (h3 : ¬ 3 ∣ t) (h5 : ¬ 5 ∣ t) : t = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd hne
  have h5' := hsmooth p hp hpt
  have h2' := hp.two_le
  interval_cases p
  · exact h2 hpt
  · exact h3 hpt
  · exact absurd hp (by norm_num)
  · exact h5 hpt
