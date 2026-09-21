by

  -- Evaluate the total sum of the grid by isolating the non-zero row
  have sum_by_rows : ∑ r, ∑ c, f r c = t_h := by
    calc ∑ r, ∑ c, f r c = ∑ c, f r₀ c := by
           apply sum_eq_single r₀
           · intro r _ hr_neq
             exact h_rows r hr_neq
           · intro h_not_in
             exact False.elim (h_not_in (mem_univ r₀))
         _ = t_h := h_r₀

  -- Evaluate the total sum of the grid by isolating the non-zero column
  have sum_by_cols : ∑ c, ∑ r, f r c = t_v := by
    calc ∑ c, ∑ r, f r c = ∑ r, f r c₀ := by
           apply sum_eq_single c₀
           · intro c _ hc_neq
             exact h_cols c hc_neq
           · intro h_not_in
             exact False.elim (h_not_in (mem_univ c₀))
         _ = t_v := h_c₀

  -- Swap the summation order (Fubini's theorem for finite sums)
  have swap_sum : ∑ r, ∑ c, f r c = ∑ c, ∑ r, f r c := sum_comm

  -- Combine the evaluations to prove equality
  calc t_h = ∑ r, ∑ c, f r c := sum_by_rows.symm
    _ = ∑ c, ∑ r, f r c := swap_sum
    _ = t_v := sum_by_cols
