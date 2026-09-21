by
  refine ⟨⟨?_, ?_⟩, fun R hR => ratio_eq_maxRatio_iff hnv hQ hR⟩
  · obtain ⟨R, hR, hval⟩ := exists_ratio_eq_maxRatio hnv hQ
    exact ⟨R, hR, hval⟩
  · rintro y ⟨R, hR, rfl⟩
    exact ratio_le_maxRatio hnv hQ hR
