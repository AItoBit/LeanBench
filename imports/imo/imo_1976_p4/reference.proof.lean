by
  constructor
  · refine ⟨2 :: List.replicate 658 3, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · norm_num
      · rw [List.eq_of_mem_replicate hy]; norm_num
    · rw [List.sum_cons, List.sum_replicate, smul_eq_mul]
    · rw [List.prod_cons, List.prod_replicate]
  · rintro p ⟨l, _, hsum, rfl⟩
    exact prod_le l hsum
