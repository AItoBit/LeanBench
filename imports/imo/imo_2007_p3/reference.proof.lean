by
  classical
  obtain ⟨m, hm⟩ := hEven
  have hm' : cliqueSize G Finset.univ = 2 * m := by omega
  have hglobal : ∀ s : Finset V, G.IsClique (s : Set V) → s.card ≤ 2 * m := by
    intro s hs
    have := le_cliqueSize (Finset.subset_univ s) hs
    omega
  obtain ⟨M, -, hMclique, hMcard⟩ := exists_clique_cliqueSize G Finset.univ
  rw [hm'] at hMcard
  -- Choose a subset `S ⊆ M` of least size with `cliqueSize G Sᶜ ≤ S.card`.
  set family : Finset (Finset V) :=
    M.powerset.filter (fun S : Finset V => cliqueSize G Sᶜ ≤ S.card) with hfamdef
  have hfam_mem : ∀ S : Finset V, S ∈ family ↔ (S ⊆ M ∧ cliqueSize G Sᶜ ≤ S.card) := by
    intro S; simp [hfamdef, Finset.mem_filter, Finset.mem_powerset]
  have hfam_ne : family.Nonempty := by
    refine ⟨M, (hfam_mem M).2 ⟨subset_refl _, ?_⟩⟩
    obtain ⟨s, _, hc, hcard⟩ := exists_clique_cliqueSize G Mᶜ
    have := hglobal s hc
    omega
  obtain ⟨S, hSfam, hSmin⟩ := family.exists_min_image Finset.card hfam_ne
  rw [hfam_mem] at hSfam
  obtain ⟨hSsub, hSle⟩ := hSfam
  by_cases heq : cliqueSize G Sᶜ = S.card
  · -- the two rooms `S` and `Sᶜ` already work
    refine ⟨S, ?_⟩
    have hScl : G.IsClique ((S : Finset V) : Set V) :=
      hMclique.subset (by exact_mod_cast hSsub)
    rw [cliqueSize_of_isClique hScl, heq]
  · -- otherwise, removing one competitor from `S` produces the "bad" configuration
    have hlt : cliqueSize G Sᶜ < S.card := lt_of_le_of_ne hSle heq
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨x, hx⟩ := hSne
    set M₁ : Finset V := S.erase x with hM₁def
    have hM₁sub : M₁ ⊆ M := (Finset.erase_subset x S).trans hSsub
    have hM₁card : M₁.card + 1 = S.card := by
      rw [hM₁def, Finset.card_erase_of_mem hx]
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨x, hx⟩
      omega
    have hnotfam : M₁ ∉ family := by
      intro h
      have := hSmin _ h
      omega
    have hgt : M₁.card < cliqueSize G M₁ᶜ := by
      by_contra hcon
      exact hnotfam ((hfam_mem M₁).2 ⟨hM₁sub, by omega⟩)
    have hcompl : M₁ᶜ = insert x Sᶜ := by
      rw [hM₁def]
      ext w
      simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert, not_and]
      by_cases hwx : w = x <;> simp [hwx]
    have hle : cliqueSize G M₁ᶜ ≤ M₁.card + 1 := by
      rw [hcompl]
      have := cliqueSize_insert_le (G := G) x Sᶜ
      omega
    exact repair hMclique hMcard hglobal hM₁sub rfl (by omega)
