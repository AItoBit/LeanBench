by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro l M p hlen hpos hnd hcard hsum
    rcases Finset.eq_empty_or_nonempty (M.filter (fun m => p < m)) with hMp | hMp
    · -- no obstacle lies beyond `p`:  any order will do
      have hle : ∀ z ∈ M, z ≤ p := by
        intro z hz
        by_contra h
        have : z ∈ M.filter (fun m => p < m) := Finset.mem_filter.2 ⟨hz, by omega⟩
        rw [hMp] at this
        exact absurd this (Finset.notMem_empty z)
      refine ⟨l, List.Perm.refl _, ?_⟩
      rcases l with _ | ⟨b, v⟩
      · simp at hlen; omega
      · have hb : 0 < b := hpos b (by simp)
        refine ⟨fun hmem => by have := hle _ hmem; omega, ?_⟩
        exact safeFrom_of_all_lt M v (p + b) (fun z hz => by have := hle z hz; omega)
          (fun x hx => hpos x (List.mem_cons_of_mem _ hx))
    · -- there is an obstacle beyond `p`
      have hMpcard : 0 < (M.filter (fun m => p < m)).card := Finset.card_pos.2 hMp
      have hn : 2 ≤ n := by omega
      have hlne : l ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      obtain ⟨a, haL, hamax⟩ := exists_max_mem l hlne
      have ha0 : 0 < a := hpos a haL
      have hperm_l : l ~ a :: l.erase a := List.perm_cons_erase haL
      have hLlen : (l.erase a).length = n - 1 := by
        rw [List.length_erase_of_mem haL, hlen]
      have hLnd : (l.erase a).Nodup := hnd.erase a
      have hLmem : ∀ x ∈ l.erase a, x ∈ l ∧ x ≠ a := by
        intro x hx
        have := (List.Nodup.mem_erase_iff hnd).1 hx
        exact ⟨this.2, this.1⟩
      have hLpos : ∀ x ∈ l.erase a, 0 < x := fun x hx => hpos x (hLmem x hx).1
      have hLlt : ∀ x ∈ l.erase a, x < a := by
        intro x hx
        have := hamax x (hLmem x hx).1
        have := (hLmem x hx).2
        omega
      have hLsum : l.sum = a + (l.erase a).sum := by
        have := hperm_l.sum_eq
        simpa using this
      by_cases hA : p + a ∈ M
      · -- the largest jump is blocked
        have hpaMp : p + a ∈ M.filter (fun m => p < m) := Finset.mem_filter.2 ⟨hA, by omega⟩
        by_cases hB : ∀ b ∈ l.erase a, p + b ∉ M
        · -- no other single jump is blocked
          have hcard' : (M.filter (fun m => p + a < m)).card < n - 1 := by
            have hsub : M.filter (fun m => p + a < m) ⊆
                (M.filter (fun m => p < m)).erase (p + a) := by
              intro z hz
              rw [Finset.mem_filter] at hz
              exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨hz.1, by omega⟩⟩
            have h1 := Finset.card_le_card hsub
            have h2 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            omega
          obtain ⟨t, htperm, htsafe⟩ := IH (n - 1) (by omega) (l.erase a) M (p + a) hLlen
            hLpos hLnd hcard' (by rw [show p + a + (l.erase a).sum = p + l.sum by omega]; exact hsum)
          have htlen : t.length = n - 1 := by rw [htperm.length_eq, hLlen]
          rcases t with _ | ⟨b, v⟩
          · simp at htlen; omega
          · obtain ⟨h1, h2⟩ := htsafe
            have hbL : b ∈ l.erase a := htperm.mem_iff.1 (List.mem_cons_self ..)
            refine ⟨b :: a :: v, ?_, hB b hbL, ?_, ?_⟩
            · exact ((List.Perm.swap a b v).trans ((htperm.cons a).trans hperm_l.symm))
            · rw [show p + b + a = p + a + b by omega]; exact h1
            · rw [show p + b + a = p + a + b by omega]; exact h2
        · -- some other single jump is blocked
          push_neg at hB
          obtain ⟨b₀, hb₀L, hb₀M⟩ := hB
          have hb₀lt : b₀ < a := hLlt b₀ hb₀L
          have hb₀0 : 0 < b₀ := hLpos b₀ hb₀L
          have hb₀Mp : p + b₀ ∈ (M.filter (fun m => p < m)).erase (p + a) :=
            Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨hb₀M, by omega⟩⟩
          -- a pigeonhole argument produces a jump `b` with both `p + b` and `p + b + a` free
          obtain ⟨b, hbL, hbM1, hbM2⟩ : ∃ b ∈ l.erase a, p + b ∉ M ∧ p + b + a ∉ M := by
            by_contra hcon
            push_neg at hcon
            have hmap : ∀ x ∈ (l.erase a).toFinset,
                (fun b => if p + b ∈ M then p + b else p + b + a) x ∈
                  (M.filter (fun m => p < m)).erase (p + a) := by
              intro x hx
              rw [List.mem_toFinset] at hx
              have hx0 : 0 < x := hLpos x hx
              have hxa : x < a := hLlt x hx
              by_cases h : p + x ∈ M
              · simp only [h, if_pos]
                exact Finset.mem_erase.2 ⟨by omega, Finset.mem_filter.2 ⟨h, by omega⟩⟩
              · simp only [h, if_neg, if_false]
                exact Finset.mem_erase.2
                  ⟨by omega, Finset.mem_filter.2 ⟨hcon x hx h, by omega⟩⟩
            have hinj : Set.InjOn (fun b => if p + b ∈ M then p + b else p + b + a)
                ((l.erase a).toFinset : Set ℕ) := by
              intro x hx y hy hxy
              simp only [Finset.coe_sort_coe, Finset.mem_coe, List.mem_toFinset] at hx hy
              have hx0 : 0 < x := hLpos x hx
              have hxa : x < a := hLlt x hx
              have hy0 : 0 < y := hLpos y hy
              have hya : y < a := hLlt y hy
              by_cases h1 : p + x ∈ M <;> by_cases h2 : p + y ∈ M <;>
                simp only [h1, h2, if_pos, if_neg, if_false, if_true] at hxy <;> omega
            have hcard1 := Finset.card_le_card_of_injOn _ hmap hinj
            have hcard2 : ((l.erase a).toFinset).card = n - 1 := by
              rw [List.toFinset_card_of_nodup hLnd, hLlen]
            have hcard3 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            omega
          have hb0 : 0 < b := hLpos b hbL
          have hblt : b < a := hLlt b hbL
          have hEsum : (l.erase a).sum = b + ((l.erase a).erase b).sum := by
            have := (List.perm_cons_erase hbL).sum_eq
            simpa using this
          have hcard' : (M.filter (fun m => p + b + a < m)).card < n - 2 := by
            have hsub : M.filter (fun m => p + b + a < m) ⊆
                (((M.filter (fun m => p < m)).erase (p + a)).erase (p + b₀)) := by
              intro z hz
              rw [Finset.mem_filter] at hz
              refine Finset.mem_erase.2 ⟨by omega, Finset.mem_erase.2 ⟨by omega, ?_⟩⟩
              exact Finset.mem_filter.2 ⟨hz.1, by omega⟩
            have h1 := Finset.card_le_card hsub
            have h2 : ((M.filter (fun m => p < m)).erase (p + a)).card =
                (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hpaMp
            have h3 : (((M.filter (fun m => p < m)).erase (p + a)).erase (p + b₀)).card =
                ((M.filter (fun m => p < m)).erase (p + a)).card - 1 :=
              Finset.card_erase_of_mem hb₀Mp
            have h4 : 0 < ((M.filter (fun m => p < m)).erase (p + a)).card :=
              Finset.card_pos.2 ⟨p + b₀, hb₀Mp⟩
            omega
          obtain ⟨t, htperm, htsafe⟩ := IH (n - 2) (by omega) ((l.erase a).erase b) M (p + b + a)
            (by rw [List.length_erase_of_mem hbL, hLlen]; omega)
            (fun x hx => hLpos x (List.mem_of_mem_erase hx))
            (hLnd.erase b) hcard'
            (by rw [show p + b + a + ((l.erase a).erase b).sum = p + l.sum by omega]; exact hsum)
          refine ⟨b :: a :: t, ?_, hbM1, hbM2, htsafe⟩
          refine ((htperm.cons a).cons b).trans ?_
          refine (List.Perm.swap a b ((l.erase a).erase b)).trans ?_
          exact (((List.perm_cons_erase hbL).symm).cons a).trans hperm_l.symm
      · -- the largest jump is free:  use the repair lemma
        have hm₁mem := Finset.min'_mem _ hMp
        set m₁ := (M.filter (fun m => p < m)).min' hMp with hm₁def
        have hm₁M : m₁ ∈ M := (Finset.mem_filter.1 hm₁mem).1
        have hm₁p : p < m₁ := (Finset.mem_filter.1 hm₁mem).2
        have hgap : ∀ z ∈ M, z ≤ p ∨ m₁ ≤ z := by
          intro z hz
          by_cases h : p < z
          · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hz, h⟩))
          · exact Or.inl (by omega)
        have hcard' : ((M.erase m₁).filter (fun m => p + a < m)).card < n - 1 := by
          have hsub : (M.erase m₁).filter (fun m => p + a < m) ⊆
              (M.filter (fun m => p < m)).erase m₁ := by
            intro z hz
            rw [Finset.mem_filter, Finset.mem_erase] at hz
            exact Finset.mem_erase.2 ⟨hz.1.1, Finset.mem_filter.2 ⟨hz.1.2, by omega⟩⟩
          have h1 := Finset.card_le_card hsub
          have h2 : ((M.filter (fun m => p < m)).erase m₁).card =
              (M.filter (fun m => p < m)).card - 1 := Finset.card_erase_of_mem hm₁mem
          omega
        obtain ⟨t, htperm, htsafe⟩ := IH (n - 1) (by omega) (l.erase a) (M.erase m₁) (p + a)
          hLlen hLpos hLnd hcard'
          (by
            rw [show p + a + (l.erase a).sum = p + l.sum by omega]
            exact fun hmem => hsum (Finset.mem_of_mem_erase hmem))
        have htsum : t.sum = (l.erase a).sum := htperm.sum_eq
        obtain ⟨t', hperm', hsafe'⟩ := repair M m₁ a t p
          (fun x hx => ⟨hLpos x (htperm.mem_iff.1 hx), hLlt x (htperm.mem_iff.1 hx)⟩)
          hgap
          ⟨fun hmem => hA (Finset.mem_of_mem_erase hmem), htsafe⟩
          (by rw [show p + a + t.sum = p + l.sum by omega]; exact hsum)
        exact ⟨t', hperm'.trans ((htperm.cons a).trans hperm_l.symm), hsafe'⟩
