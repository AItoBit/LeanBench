by
  induction m with
  | zero =>
    refine ⟨{0}, ?_⟩
    intro A hA
    rw [Finset.mem_singleton] at hA
    subst hA
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    simp
  | succ n ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨u, hu, hgood⟩ := exists_good S
    have hu0 : u ≠ 0 := by
      intro h
      rw [h] at hu
      simp at hu
    -- the translate `x ↦ x + u` is injective and moves `S` off itself
    have hinj : Function.Injective (fun z : ℂ => z + u) := fun a b hab => by
      simpa using hab
    have hdisj : Disjoint S (S.image (fun z => z + u)) := by
      rw [Finset.disjoint_right]
      rintro x hx hxS
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hxy : y + u ≠ y := fun h => hu0 (by linear_combination h)
      exact (hgood (y + u) hxS y hy hxy).2 (by ring)
    -- distance to a translated point
    have hdu : ∀ a : ℂ, dist a (a + u) = 1 := by
      intro a
      rw [← dist_shift a a u, sub_self, dist_comm]
      exact hu
    refine ⟨S ∪ S.image (fun z => z + u), ?_⟩
    intro A hA
    rw [Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    rcases Finset.mem_union.mp hA with hA' | hA'
    · -- `A ∈ S` : `n` old neighbours plus the single new one `A + u`
      have h1 : (S.filter (fun B => dist A B = 1)).card = n := hS A hA'
      have h2 : (S.image (fun z => z + u)).filter (fun B => dist A B = 1) = {A + u} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hb⟩
          rcases eq_or_ne A y with h' | h'
          · rw [h']
          · exact absurd (by rw [dist_shift]; exact hb) (hgood A hA' y hy h').1
        · rintro rfl
          exact ⟨⟨A, hA', rfl⟩, hdu A⟩
      rw [h1, h2, Finset.card_singleton]
    · -- `A = x + u` : the single old neighbour `x` plus `n` translated ones
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA'
      have h1 : S.filter (fun B => dist (x + u) B = 1) = {x} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hb, hd⟩
          rcases eq_or_ne b x with h' | h'
          · exact h'
          · exact absurd (by rw [dist_shift]; rw [dist_comm] at hd; exact hd)
              (hgood b hb x hx h').1
        · rintro rfl
          exact ⟨hx, by rw [dist_comm]; exact hdu b⟩
      have h2 : (S.image (fun z => z + u)).filter (fun B => dist (x + u) B = 1)
          = (S.filter (fun B => dist x B = 1)).image (fun z => z + u) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨y, hy, rfl⟩, hb⟩
          exact ⟨y, ⟨hy, by rwa [dist_add_right] at hb⟩, rfl⟩
        · rintro ⟨y, ⟨hy, hby⟩, rfl⟩
          exact ⟨⟨y, hy, rfl⟩, by rwa [dist_add_right]⟩
      rw [h1, h2, Finset.card_singleton, Finset.card_image_of_injective _ hinj,
        hS x hx]
      omega
