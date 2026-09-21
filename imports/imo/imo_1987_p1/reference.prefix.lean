open Finset

open scoped Nat

namespace Imo1987P1

/-- Number of fixed points of a permutation of `Fin n`. -/
def numFixed {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (univ.filter fun i => σ i = i).card

/-- `p n k` : number of permutations of `Fin n` with exactly `k` fixed points. -/
def p (n k : ℕ) : ℕ :=
  (univ.filter fun σ : Equiv.Perm (Fin n) => numFixed σ = k).card

/-- Permutations fixing `i` are in bijection with permutations sending `a` to `i`. -/
lemma card_fix_eq (n : ℕ) (a i : Fin n) :
    (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card =
      (univ.filter fun σ : Equiv.Perm (Fin n) => σ a = i).card := by
  refine card_nbij' (fun σ => σ * Equiv.swap a i) (fun σ => σ * Equiv.swap a i)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hσ]
  · intro σ hσ
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hσ]
  · intro σ _
    exact Equiv.mul_swap_mul_self a i σ
  · intro σ _
    exact Equiv.mul_swap_mul_self a i σ
