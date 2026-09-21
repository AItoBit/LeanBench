by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_sphere, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨A, B, C, hcfg, rfl⟩
    exact ⟨dist_midpoint_AC R r O A P B C hcfg,
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hC hcfg.hAP (Or.inl rfl),
      midpoint_ne_on_axis hr hrR hcfg.hA hcfg.hP hcfg.hC hcfg.hAP (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨A, B, C, hcfg, hXm⟩ := exists_config_midpoint hr hrR hP h1 h2 h3
    exact ⟨A, C, B, hcfg.swap, hXm⟩
