by
  rw [← Nat.card_eq_of_bijective Phi ⟨Phi_injective, Phi_surjective⟩]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_perm]
  decide
