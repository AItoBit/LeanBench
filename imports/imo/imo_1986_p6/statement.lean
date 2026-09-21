namespace IMO1986P6

open Finset

/-- 
Given a finite grid of points colored with integers, if all rows sum to 0 
except row `r₀` which sums to `t_h`, and all columns sum to 0 except 
column `c₀` which sums to `t_v`, then `t_h = t_v`.
-/

theorem candidate
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} [Fintype β] [DecidableEq β]
    (f : α → β → ℤ)
    (r₀ : α) (c₀ : β)
    (t_h t_v : ℤ)
    (h_rows : ∀ r ≠ r₀, ∑ c, f r c = 0)
    (h_r₀   : ∑ c, f r₀ c = t_h)
    (h_cols : ∀ c ≠ c₀, ∑ r, f r c = 0)
    (h_c₀   : ∑ r, f r c₀ = t_v) :
    t_h = t_v :=
