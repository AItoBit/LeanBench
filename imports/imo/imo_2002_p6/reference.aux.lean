theorem le_arcsin_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.arcsin x := by
  rcases eq_or_lt_of_le hx0 with h | h
  · simp [← h]
  · have hpos : 0 < Real.arcsin x := Real.arcsin_pos.2 h
    have hlt := Real.sin_lt hpos
    rw [Real.sin_arcsin (by linarith) hx1] at hlt
    linarith

/-- The tangents from a point at distance `d ≥ 1` to a unit circle subtend an angle
`2 arcsin (1/d)`, which is at least `2/d`. -/
theorem two_div_le_tangent_angle {d : ℝ} (hd : 1 ≤ d) : 2 / d ≤ 2 * Real.arcsin (1 / d) := by
  have hd0 : (0:ℝ) < d := by linarith
  have h0 : (0:ℝ) ≤ 1 / d := by positivity
  have h1 : 1 / d ≤ 1 := by rw [div_le_one hd0]; exact hd
  have h2 := le_arcsin_self h0 h1
  have h3 : 2 / d = 2 * (1 / d) := by ring
  rw [h3]
  linarith

/-! ### The counting core -/

/-- The counting core of IMO 2002 P6. -/
theorem core (n : ℕ) (hn : 3 ≤ n) (d : Fin n → Fin n → ℝ)
    (H : Finset (Fin n)) (hH3 : 3 ≤ H.card)
    (far : Fin n → Fin n) (θ : Fin n → ℝ)
    (hfar : ∀ i ∈ H, far i ≠ i)
    (hfarmin : ∀ i ∈ H, ∀ j : Fin n, j ≠ i → 2 / d i (far i) ≤ 2 / d i j)
    (hhull : ∀ i ∈ H, ∑ j ∈ (univ.erase i).erase (far i), 2 / d i j ≤ θ i)
    (hθ : ∑ i ∈ H, θ i = ((H.card : ℝ) - 2) * Real.pi)
    (hinner : ∀ i ∈ Hᶜ, ∑ j ∈ univ.erase i, 2 / d i j ≤ Real.pi) :
    ∑ i : Fin n, ∑ j ∈ univ.erase i, 2 / d i j ≤ ((n : ℝ) - 1) * Real.pi := by
  classical
  have hcard_univ : (univ : Finset (Fin n)).card = n := by simp
  have hmn : H.card ≤ n := by
    have hle := Finset.card_le_card (Finset.subset_univ H)
    rwa [hcard_univ] at hle
  have hnR : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmR3 : (3:ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hH3
  have hmnR : (H.card : ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hn2 : (0:ℝ) < (n:ℝ) - 2 := by linarith
  have hpi : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  set F : Fin n → ℝ := fun i => ∑ j ∈ univ.erase i, 2 / d i j with hF
  -- a hull vertex: recover the dropped term by averaging
  have step1 : ∀ i ∈ H, ((n:ℝ) - 2) * F i ≤ ((n:ℝ) - 1) * θ i := by
    intro i hi
    have hfi : far i ∈ univ.erase i := Finset.mem_erase.2 ⟨hfar i hi, Finset.mem_univ _⟩
    have hsplit : F i = 2 / d i (far i) + ∑ j ∈ (univ.erase i).erase (far i), 2 / d i j := by
      rw [hF]
      exact (Finset.add_sum_erase _ _ hfi).symm
    have hcardT : ((univ.erase i).erase (far i)).card = n - 2 := by
      rw [Finset.card_erase_of_mem hfi, Finset.card_erase_of_mem (Finset.mem_univ i),
        hcard_univ]
      omega
    have hlow : ∀ j ∈ (univ.erase i).erase (far i), 2 / d i (far i) ≤ 2 / d i j := by
      intro j hj
      exact hfarmin i hi j (Finset.mem_erase.1 (Finset.mem_of_mem_erase hj)).1
    have hb := Finset.card_nsmul_le_sum _ _ _ hlow
    rw [hcardT, nsmul_eq_mul] at hb
    have hcast : ((n - 2 : ℕ) : ℝ) = (n:ℝ) - 2 := by
      have h2n : (2:ℕ) ≤ n := by omega
      rw [Nat.cast_sub h2n]
      norm_num
    rw [hcast] at hb
    have hS := hhull i hi
    have hextra : (0:ℝ)
        ≤ ((n:ℝ) - 1) * (θ i - ∑ j ∈ (univ.erase i).erase (far i), 2 / d i j) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hsplit]
    linarith [hb, hextra]
  -- sum over the hull vertices
  have hHsum : ((n:ℝ) - 2) * (∑ i ∈ H, F i)
      ≤ ((n:ℝ) - 1) * (((H.card : ℝ) - 2) * Real.pi) := by
    rw [Finset.mul_sum, ← hθ, Finset.mul_sum]
    exact Finset.sum_le_sum step1
  -- sum over the remaining centres
  have hCsum : ∑ i ∈ Hᶜ, F i ≤ ((n:ℝ) - (H.card:ℝ)) * Real.pi := by
    have h1 := Finset.sum_le_card_nsmul Hᶜ F Real.pi hinner
    rw [Finset.card_compl, Fintype.card_fin, nsmul_eq_mul] at h1
    have hcast : ((n - H.card : ℕ) : ℝ) = (n:ℝ) - (H.card:ℝ) := by
      rw [Nat.cast_sub hmn]
    rwa [hcast] at h1
  -- combine
  have htotal : (∑ i ∈ H, F i) + (∑ i ∈ Hᶜ, F i) = ∑ i : Fin n, F i :=
    Finset.sum_add_sum_compl H F
  have h2 : ((n:ℝ) - 2) * (∑ i ∈ Hᶜ, F i)
      ≤ ((n:ℝ) - 2) * (((n:ℝ) - (H.card:ℝ)) * Real.pi) :=
    mul_le_mul_of_nonneg_left hCsum (by linarith)
  have h3 : (0:ℝ) ≤ ((n:ℝ) - (H.card:ℝ)) * Real.pi := mul_nonneg (by linarith) hpi
  have hfinal : ((n:ℝ) - 2) * (∑ i : Fin n, F i)
      ≤ ((n:ℝ) - 2) * (((n:ℝ) - 1) * Real.pi) := by
    rw [← htotal, mul_add]
    linarith [hHsum, h2, h3]
  exact le_of_mul_le_mul_left hfinal hn2

/-! ### From the double sum to the sum over pairs -/

theorem sum_erase_eq_two_mul (n : ℕ) (f : Fin n → Fin n → ℝ) (hsymm : ∀ i j, f i j = f j i) :
    ∑ i : Fin n, ∑ j ∈ univ.erase i, f i j
      = 2 * ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f i j := by
  classical
  have hsp : ∀ i : Fin n, ∑ j ∈ univ.erase i, f i j
      = (∑ j ∈ univ.filter (fun j => i < j), f i j)
        + ∑ j ∈ univ.filter (fun j => j < i), f i j := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not (univ.erase i) (fun j => i < j)]
    congr 1
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨-, h⟩
        exact ⟨Finset.mem_univ j, h⟩
      · rintro ⟨-, h⟩
        refine ⟨⟨?_, Finset.mem_univ j⟩, h⟩
        intro hji
        rw [hji] at h
        exact lt_irrefl i h
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, -⟩, h⟩
        exact ⟨Finset.mem_univ j, lt_of_le_of_ne (not_lt.1 h) hne⟩
      · rintro ⟨-, h⟩
        exact ⟨⟨ne_of_lt h, Finset.mem_univ j⟩, not_lt.2 h.le⟩
  have hswap : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => j < i), f i j
      = ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f i j := by
    have h1 : ∀ i : Fin n, ∑ j ∈ univ.filter (fun j => j < i), f i j
        = ∑ j ∈ univ.filter (fun j => j < i), f j i :=
      fun i => Finset.sum_congr rfl fun j _ => hsymm i j
    simp only [h1]
    exact Finset.sum_comm' (by intro x y; simp)
  simp only [hsp, Finset.sum_add_distrib, hswap]
  ring
