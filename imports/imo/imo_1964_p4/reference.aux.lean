/-- Any finset with at least three elements contains three pairwise distinct elements. -/
private lemma exists_three_distinct {α : Type*} [DecidableEq α] {B : Finset α}
    (h : 3 ≤ B.card) :
    ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have h1 : 2 ≤ (B.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < (B.erase x).card)
  have h2 : 1 ≤ ((B.erase x).erase y).card := by rw [Finset.card_erase_of_mem hy]; omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < ((B.erase x).erase y).card)
  have hzx : z ∈ B.erase x := Finset.mem_of_mem_erase hz
  exact ⟨x, hx, y, Finset.mem_of_mem_erase hy, z, Finset.mem_of_mem_erase hzx,
    (Finset.ne_of_mem_erase hy).symm, (Finset.ne_of_mem_erase hzx).symm,
    (Finset.ne_of_mem_erase hz).symm⟩

/-- In `Fin 3`, two colours that both avoid the same two distinct colours are equal. -/
private lemma fin3_eq_of_ne {t1 t2 c d : Fin 3} (h : t1 ≠ t2)
    (hc1 : c ≠ t1) (hc2 : c ≠ t2) (hd1 : d ≠ t1) (hd2 : d ≠ t2) : c = d := by
  revert h hc1 hc2 hd1 hd2
  revert t1 t2 c d
  decide

/-- A monochromatic triangle gives the required set of three people. -/
private lemma triangle_solution {topic : Sym2 (Fin 17) → Fin 3} {a b c : Fin 17} {t : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : topic s(a, b) = t) (h2 : topic s(a, c) = t) (h3 : topic s(b, c) = t) :
    ∃ (s : Finset (Fin 17)) (t : Fin 3),
      3 ≤ s.card ∧ ∀ x ∈ s, ∀ y ∈ s, ∀ (_ : x ≠ y), topic s(x, y) = t := by
  refine ⟨{a, b, c}, t, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | (rw [Sym2.eq_swap]; assumption)
