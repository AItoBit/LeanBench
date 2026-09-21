by
  -- Step 1: the sum counts all fixed points of all permutations.
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin n))), numFixed σ ∈ range (n + 1) := by
    intro σ _
    rw [mem_range]
    unfold numFixed
    exact Nat.lt_succ_of_le ((card_filter_le _ _).trans_eq (card_fin n))
  have h1 : ∑ k ∈ range (n + 1), k * p n k = ∑ σ : Equiv.Perm (Fin n), numFixed σ := by
    rw [← sum_fiberwise_of_maps_to hmaps numFixed]
    refine sum_congr rfl fun k _ => ?_
    have hk : ∀ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin n) => numFixed σ = k),
        numFixed σ = k :=
      fun σ hσ => (mem_filter.mp hσ).2
    rw [sum_const_nat hk, p, mul_comm]
  -- Step 2: swap the order of summation.
  have h2 : ∑ σ : Equiv.Perm (Fin n), numFixed σ =
      ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card := by
    simp only [numFixed, card_filter]
    exact sum_comm
  -- Step 3: each point is fixed by the same number of permutations; total is `n!`.
  have h3 : ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card = n ! := by
    have a : Fin n := ⟨0, by omega⟩
    calc ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ i = i).card
        = ∑ i : Fin n, (univ.filter fun σ : Equiv.Perm (Fin n) => σ a = i).card :=
          sum_congr rfl fun i _ => card_fix_eq n a i
      _ = (univ : Finset (Equiv.Perm (Fin n))).card :=
          (card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) => σ a)
            (s := univ) (t := univ) (by intro σ _; simp)).symm
      _ = n ! := by simp [Fintype.card_perm]
  exact h1.trans (h2.trans h3)
