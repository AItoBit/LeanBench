by
  obtain ⟨hn3, hsum⟩ := three_rounds hn hp hpq hqr hdeal hA hB hC
  subst hn3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hA hB hC
  have hs0 := round_sum hdeal 0 (by norm_num)
  have hs1 := round_sum hdeal 1 (by norm_num)
  have hs2 := round_sum hdeal 2 (by norm_num)
  obtain ⟨ha0, hb0, -⟩ := mem_cards hdeal 0 (by norm_num)
  obtain ⟨ha1, hb1, -⟩ := mem_cards hdeal 1 (by norm_num)
  obtain ⟨ha2, -, -⟩ := mem_cards hdeal 2 (by norm_num)
  norm_num at hlast
  rcases ha0 with h | h | h <;> rcases ha1 with h' | h' | h' <;>
    rcases ha2 with h'' | h'' | h'' <;> rcases hb0 with k | k | k <;>
      rcases hb1 with k' | k' | k' <;> omega
