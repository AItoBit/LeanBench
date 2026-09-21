by
  constructor
  · exact every_217_subset
  · intro k hk
    change ForcesFive k at hk
    by_contra hnot
    have hkle : k ≤ bad.card := by
      rw [bad_card]
      omega
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hkle
    have hSU : S ⊆ domain := fun x hx => bad_subset (hS hx)
    obtain ⟨T, hTS, hTcard, hcop⟩ := hk S hSU hcard
    exact bad_has_no_five
      ⟨T, (fun x hx => hS (hTS hx)), hTcard, hcop⟩
