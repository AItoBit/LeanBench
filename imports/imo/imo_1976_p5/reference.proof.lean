by
  classical
  -- the box of candidate vectors, encoded as functions into `Fin (q+1)`
  set S : Finset (Fin q → Fin (q + 1)) := Finset.univ with hS
  set f : (Fin q → Fin (q + 1)) → (Fin p → ℤ) :=
    fun x i => ∑ j : Fin q, a i j * ((x j : ℕ) : ℤ) with hf
  set T : Finset (Fin p → ℤ) :=
    Fintype.piFinset fun i : Fin p =>
      Finset.Icc (-(q : ℤ) * negCount a i) (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2) with hT
  have hmaps : ∀ x ∈ S, f x ∈ T := by
    intro x _
    rw [hT, Fintype.mem_piFinset]
    intro i
    have hb : ∀ j : Fin q, ((x j : ℕ) : ℤ) ≤ (q : ℤ) := by
      intro j
      exact_mod_cast Nat.lt_succ_iff.mp (x j).isLt
    have h0 : ∀ j : Fin q, (0 : ℤ) ≤ ((x j : ℕ) : ℤ) := fun j => Int.natCast_nonneg _
    exact row_sum_mem_Icc a ha (fun j => ((x j : ℕ) : ℤ)) h0 hb i
  have hTcard : T.card = (q ^ 2 + 1) ^ p := by
    rw [hT, Fintype.card_piFinset]
    have : ∀ i : Fin p,
        (Finset.Icc (-(q : ℤ) * negCount a i)
          (-(q : ℤ) * negCount a i + (q : ℤ) ^ 2)).card = q ^ 2 + 1 := by
      intro i
      rw [Int.card_Icc]
      have : -(q : ℤ) * negCount a i + (q : ℤ) ^ 2 + 1 - -(q : ℤ) * negCount a i
          = ((q ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [Finset.prod_congr rfl fun i _ => this i]
    simp
  have hScard : S.card = (q + 1) ^ q := by
    rw [hS]
    simp
  have hlt : T.card < S.card := by
    rw [hTcard, hScard, hq]
    have h2 : (2 * p + 1) ^ (2 * p) = ((2 * p + 1) ^ 2) ^ p := by
      rw [← pow_mul, mul_comm 2 p]
    rw [h2]
    apply Nat.pow_lt_pow_left _ hp.ne'
    nlinarith [hp]
  obtain ⟨u, -, v, -, huv, hfuv⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨fun j => ((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro i
    have := congrFun hfuv i
    rw [hf] at this
    simp only at this
    calc ∑ j : Fin q, a i j * (((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ))
        = (∑ j : Fin q, a i j * ((u j : ℕ) : ℤ)) - ∑ j : Fin q, a i j * ((v j : ℕ) : ℤ) := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this]; ring
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp huv
    refine ⟨j, ?_⟩
    show ((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ) ≠ 0
    have : ((u j : ℕ) : ℤ) ≠ ((v j : ℕ) : ℤ) := by
      simpa [Fin.val_inj] using fun h : (u j : ℕ) = (v j : ℕ) => hj (Fin.ext h)
    omega
  · intro j
    show |((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ)| ≤ (q : ℤ)
    have hu : ((u j : ℕ) : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (u j).isLt
    have hv : ((v j : ℕ) : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (v j).isLt
    have hu0 : (0 : ℤ) ≤ ((u j : ℕ) : ℤ) := Int.natCast_nonneg _
    have hv0 : (0 : ℤ) ≤ ((v j : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [abs_le]
    omega
