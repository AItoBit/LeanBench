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

set_option grind.warning false

namespace Imo1981P3

/-- Every pair of positive naturals `(m, n)` with `(n² - mn - m²)² = 1` is a pair of
consecutive Fibonacci numbers. -/
theorem solutions_are_fib :
    ∀ N m n : ℕ, m + n ≤ N → 1 ≤ m → 1 ≤ n → ((n : ℤ) ^ 2 - m * n - m ^ 2) ^ 2 = 1 →
      ∃ k, m = Nat.fib k ∧ n = Nat.fib (k + 1) := by
  intro N
  induction N with
  | zero => intro m n hN hm _ _; omega
  | succ N ih =>
    intro m n hN hm hn h
    rcases lt_trichotomy m n with hmn | hmn | hmn
    · -- descend to `(n - m, m)`
      have hmn' : (((n - m : ℕ) : ℤ)) = (n : ℤ) - m := by
        push_cast [Nat.cast_sub hmn.le]; ring
      have h' : ((m : ℤ) ^ 2 - ((n - m : ℕ) : ℤ) * m - ((n - m : ℕ) : ℤ) ^ 2) ^ 2 = 1 := by
        rw [hmn']
        nlinarith [h]
      obtain ⟨k, hk1, hk2⟩ := ih (n - m) m (by omega) (by omega) hm h'
      refine ⟨k + 1, hk2, ?_⟩
      have hfib : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      omega
    · subst hmn
      have hm1 : m = 1 := by
        by_contra hne
        have h2 : 2 ≤ m := by omega
        have h2' : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast h2
        have hm4 : (m : ℤ) ^ 4 = 1 := by linear_combination h
        nlinarith [hm4, h2', sq_nonneg ((m : ℤ) - 2)]
      subst hm1
      exact ⟨1, rfl, rfl⟩
    · exfalso
      have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
      have h2 : (n : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hmn
      have hnm : (1 : ℤ) ≤ (m : ℤ) - n := by linarith
      have hprod : (1 : ℤ) ≤ (n : ℤ) * ((m : ℤ) - n) := by nlinarith
      have he : (n : ℤ) ^ 2 - m * n - m ^ 2 ≤ -2 := by nlinarith
      nlinarith [he, h]

theorem fib_index_le (k : ℕ) (h : Nat.fib (k + 1) ≤ 1981) : k ≤ 16 := by
  by_contra hk
  have h17 : 17 ≤ k := by omega
  have : Nat.fib 18 ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have h18 : Nat.fib 18 = 2584 := by decide
  omega
