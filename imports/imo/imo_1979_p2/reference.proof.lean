by
  refine ⟨a 0, a_const hA hB, fun j => ?_⟩
  rw [b_const hA hB j]
  -- it remains to show that the two pentagons have the same colour
  by_contra hne
  set A : Bool := a 0 with hAdef
  have hb0 : b 0 = !A := by cases h1 : b 0 <;> cases h2 : A <;> simp_all
  -- in each "column" `j`, no two adjacent `Aᵢ B_j`, `Aᵢ₊₁ B_j` are of colour `A`
  have hred : ∀ j : Fin 5, (∑ i : Fin 5, if c i j = A then 1 else 0) ≤ 2 := by
    intro j
    have := indep_le_two (fun i => decide (c i j = A)) (by
      intro i ⟨h1, h2⟩
      simp only [decide_eq_true_eq] at h1 h2
      exact hA i j ⟨by rw [h1, a_const hA hB i], by rw [h2, a_const hA hB i]⟩)
    simpa using this
  -- in each "row" `i`, no two adjacent `Aᵢ B_j`, `Aᵢ B_{j+1}` are of colour `!A`
  have hblue : ∀ i : Fin 5, (∑ j : Fin 5, if c i j = A then 0 else 1) ≤ 2 := by
    intro i
    have := indep_le_two (fun j => !decide (c i j = A)) (by
      intro j ⟨h1, h2⟩
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2
      refine hB i j ⟨?_, ?_⟩
      · rw [b_const hA hB j, hb0]
        cases h : c i j <;> cases h' : A <;> simp_all
      · rw [b_const hA hB j, hb0]
        cases h : c i (j + 1) <;> cases h' : A <;> simp_all)
    simpa using this
  -- counting: there are 25 segments, at most 10 of each colour
  have hsum1 : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 1 else 0) ≤ 10 := by
    rw [Finset.sum_comm]
    calc (∑ j : Fin 5, ∑ i : Fin 5, if c i j = A then 1 else 0)
        ≤ ∑ _j : Fin 5, 2 := Finset.sum_le_sum (fun j _ => hred j)
      _ = 10 := by simp
  have hsum2 : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1) ≤ 10 := by
    calc (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1)
        ≤ ∑ _i : Fin 5, 2 := Finset.sum_le_sum (fun i _ => hblue i)
      _ = 10 := by simp
  have htot : (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 1 else 0)
      + (∑ i : Fin 5, ∑ j : Fin 5, if c i j = A then 0 else 1) = 25 := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i : Fin 5, ((∑ j : Fin 5, if c i j = A then 1 else 0)
        + ∑ j : Fin 5, if c i j = A then 0 else 1) = 5 := by
      intro i
      rw [← Finset.sum_add_distrib]
      have : ∀ j : Fin 5, ((if c i j = A then 1 else 0) + (if c i j = A then 0 else 1)) = 1 := by
        intro j; by_cases h : c i j = A <;> simp [h]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  omega
