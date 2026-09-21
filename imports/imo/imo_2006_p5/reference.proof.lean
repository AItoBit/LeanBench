by
  have hfin := imo2006_p5_setOf_finite hP hk
  rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
  exact imo2006_p5 hP hk fun t ht => hfin.mem_toFinset.1 ht
