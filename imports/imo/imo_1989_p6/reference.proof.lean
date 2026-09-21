by
  classical
  set A := (perms n).filter (fun l => l.IsChain (NotPair n)) with hA
  set B := (perms n).filter (fun l => ¬ l.IsChain (NotPair n)) with hB
  -- the forward map
  have hex : ∀ l : List ℕ, ∃ m : List ℕ, l ∈ A →
      m ∈ B ∧ ∃ a pre post, l = a :: (pre ++ ptn n a :: post) ∧
        m = pre ++ a :: ptn n a :: post ∧ pre ≠ [] ∧ a < 2 * n ∧
        (pre ++ [a]).IsChain (NotPair n) := by
    intro l
    by_cases hl : l ∈ A
    · rw [hA, Finset.mem_filter] at hl
      obtain ⟨hlp, hlc⟩ := hl
      obtain ⟨a, pre, post, hsplit, hprene, ha, hcpre⟩ :=
        split_data hn (mem_perms.1 hlp) hlc
      refine ⟨pre ++ a :: ptn n a :: post, fun _ => ⟨?_, a, pre, post, hsplit, rfl,
        hprene, ha, hcpre⟩⟩
      rw [hB, Finset.mem_filter]
      constructor
      · rw [mem_perms]
        refine List.Perm.trans ?_ (mem_perms.1 hlp)
        rw [hsplit]
        exact List.perm_middle
      · intro hc
        exact (isChain_append_cons_cons.1 hc).2.1 (pair_ptn hn ha)
    · exact ⟨[], fun h => absurd h hl⟩
  choose f hf using hex
  -- `f` maps `A` into `B`
  have hmaps : ∀ l ∈ A, f l ∈ B := fun l hl => (hf l hl).1
  -- `f` is injective on `A`
  have hinj : Set.InjOn f (A : Set (List ℕ)) := by
    intro l₁ hl₁ l₂ hl₂ heq
    obtain ⟨-, a₁, pre₁, post₁, hl₁eq, hm₁, -, ha₁, hc₁⟩ := hf l₁ hl₁
    obtain ⟨-, a₂, pre₂, post₂, hl₂eq, hm₂, -, ha₂, hc₂⟩ := hf l₂ hl₂
    have hmeq : f l₁ = pre₂ ++ a₂ :: ptn n a₂ :: post₂ := by rw [heq]; exact hm₂
    obtain ⟨hpre, ha, -, hpost⟩ :=
      junction_unique hm₁ hmeq hc₁ hc₂ (pair_ptn hn ha₁) (pair_ptn hn ha₂)
    rw [hl₁eq, hl₂eq, hpre, ha, hpost]
  -- the image misses a listing whose *first* adjacent pair is an `n`-pair
  have h0 : (0 : ℕ) ∈ List.range (2 * n) := List.mem_range.2 (by omega)
  have hnmem : n ∈ (List.range (2 * n)).erase 0 := by
    rw [List.mem_erase_of_ne (by omega)]
    exact List.mem_range.2 (by omega)
  set t := ((List.range (2 * n)).erase 0).erase n with ht
  have hm₀perm : (0 :: n :: t) ~ List.range (2 * n) :=
    ((List.perm_cons_erase h0).trans ((List.perm_cons_erase hnmem).cons 0)).symm
  have hm₀B : (0 :: n :: t) ∈ B := by
    rw [hB, Finset.mem_filter]
    refine ⟨mem_perms.2 hm₀perm, ?_⟩
    intro hc
    exact (isChain_cons_cons.1 hc).1 (Or.inl (by omega))
  have hm₀not : (0 :: n :: t) ∉ A.image f := by
    rw [Finset.mem_image]
    rintro ⟨l, hl, hfl⟩
    obtain ⟨-, a, pre, post, -, hm, hprene, -, hc⟩ := hf l hl
    rw [hm] at hfl
    obtain ⟨c, pre', rfl⟩ : ∃ c pre', pre = c :: pre' := by
      cases pre with
      | nil => exact absurd rfl hprene
      | cons c pre' => exact ⟨c, pre', rfl⟩
    rw [List.cons_append, List.cons.injEq] at hfl
    obtain ⟨hc0, htail⟩ := hfl
    subst hc0
    -- the head of what follows `0` is `n`
    have hhead : (pre' ++ [a]).head? = some n := by
      cases pre' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at htail ⊢
        rw [htail.1]
        simp
      | cons d pre'' =>
        simp only [List.cons_append, List.cons.injEq] at htail ⊢
        rw [htail.1]
        simp
    rw [List.cons_append] at hc
    exact (isChain_cons.1 hc).1 n hhead (Or.inl (by omega))
  -- conclude
  have hsub : A.image f ⊆ B := by
    intro m hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
    exact hmaps l hl
  have hss : A.image f ⊂ B := (Finset.ssubset_iff_of_subset hsub).2 ⟨_, hm₀B, hm₀not⟩
  calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ < B.card := Finset.card_lt_card hss
