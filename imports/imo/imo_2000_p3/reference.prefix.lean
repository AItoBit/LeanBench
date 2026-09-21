namespace Imo2000P3

variable {N : ℕ}

/-- A division lemma, isolated so the proof never names an order-field division lemma. -/
theorem div_le_of_mul_le {a b c : ℝ} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  have h1 : a / c * c = a := by field_simp
  nlinarith [h1, hc, h]

/-- One move: coordinate `i` jumps over coordinate `j`, which lies strictly to its right. -/
def Move (k : ℝ) (x y : Fin N → ℝ) : Prop :=
  ∃ i j : Fin N, x i < x j ∧ y = Function.update x i (x j + k * (x j - x i))

/-- Reachability by finitely many moves. -/
def Reach (k : ℝ) : (Fin N → ℝ) → (Fin N → ℝ) → Prop := Relation.ReflTransGen (Move k)

theorem Reach.refl (k : ℝ) (x : Fin N → ℝ) : Reach k x x := Relation.ReflTransGen.refl

theorem Reach.trans {k : ℝ} {x y z : Fin N → ℝ} (h₁ : Reach k x y) (h₂ : Reach k y z) :
    Reach k x z := Relation.ReflTransGen.trans h₁ h₂

theorem Reach.head {k : ℝ} {x y z : Fin N → ℝ} (h₁ : Move k x y) (h₂ : Reach k y z) :
    Reach k x z := Relation.ReflTransGen.head h₁ h₂

/-! ### Update lemmas -/

theorem upd_self (x : Fin N → ℝ) (i : Fin N) (v : ℝ) : Function.update x i v i = v := by
  simp

theorem upd_ne (x : Fin N → ℝ) {i l : Fin N} (h : l ≠ i) (v : ℝ) :
    Function.update x i v l = x l := by
  simp [h]

theorem sum_update (x : Fin N → ℝ) (i : Fin N) (v : ℝ) :
    ∑ l, Function.update x i v l = (∑ l, x l) + (v - x i) := by
  have h : ∀ l, Function.update x i v l = x l + (if l = i then v - x i else 0) := by
    intro l
    by_cases hl : l = i
    · rw [hl, upd_self]; simp
    · rw [upd_ne x hl]; simp [hl]
  simp only [h, Finset.sum_add_distrib]
  congr 1
  simp

/-! ### The potentials `R` and `X` -/

section Potential

variable [Nonempty (Fin N)]

/-- The rightmost position. -/
noncomputable def Rmax (x : Fin N → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

/-- The leftmost position. -/
noncomputable def Lmin (x : Fin N → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty x

theorem le_Rmax (x : Fin N → ℝ) (i : Fin N) : x i ≤ Rmax x :=
  Finset.le_sup' x (Finset.mem_univ i)

theorem Rmax_le {x : Fin N → ℝ} {c : ℝ} (h : ∀ i, x i ≤ c) : Rmax x ≤ c :=
  Finset.sup'_le _ _ fun i _ => h i

theorem exists_Rmax (x : Fin N → ℝ) : ∃ i, x i = Rmax x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty) x
  exact ⟨i, hi.symm⟩

theorem Lmin_le (x : Fin N → ℝ) (i : Fin N) : Lmin x ≤ x i :=
  Finset.inf'_le x (Finset.mem_univ i)

theorem exists_Lmin (x : Fin N → ℝ) : ∃ i, x i = Lmin x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty) x
  exact ⟨i, hi.symm⟩

/-- The spread `X x = Σ (R x - x l)`. -/
noncomputable def Xpot (x : Fin N → ℝ) : ℝ := (N : ℝ) * Rmax x - ∑ l, x l

theorem Xpot_eq_sum (x : Fin N → ℝ) : Xpot x = ∑ l, (Rmax x - x l) := by
  rw [Finset.sum_sub_distrib]
  simp [Xpot]

theorem Xpot_nonneg (x : Fin N → ℝ) : 0 ≤ Xpot x := by
  rw [Xpot_eq_sum]
  exact Finset.sum_nonneg fun l _ => sub_nonneg.2 (le_Rmax x l)

/-- After a legal move the new rightmost position is `max (R x) v`. -/
theorem Rmax_update (x : Fin N → ℝ) {i j : Fin N} (hij : x i < x j) (v : ℝ) :
    Rmax (Function.update x i v) = max (Rmax x) v := by
  have hji : j ≠ i := by
    intro h
    rw [h] at hij
    exact lt_irrefl _ hij
  apply le_antisymm
  · apply Rmax_le
    intro l
    by_cases hl : l = i
    · rw [hl, upd_self]
      exact le_max_right _ _
    · rw [upd_ne x hl]
      exact le_trans (le_Rmax x l) (le_max_left _ _)
  · apply max_le
    · apply Rmax_le
      intro l
      by_cases hl : l = i
      · have h1 : x j ≤ Rmax (Function.update x i v) := by
          rw [← upd_ne x hji v]
          exact le_Rmax _ j
        rw [hl]
        linarith
      · rw [← upd_ne x hl v]
        exact le_Rmax _ l
    · have h1 : Function.update x i v i ≤ Rmax (Function.update x i v) := le_Rmax _ i
      rwa [upd_self] at h1

end Potential

/-! ### Direction 1: `k < 1/(N-1)` keeps everything bounded -/

section Bounded

variable [Nonempty (Fin N)]

/-- One move does not increase `R + X/k₀`. -/
theorem phi_step {k k0 : ℝ} (hk : 0 < k) (hk0 : 0 < k0) (hdef : k0 = 1 / k - ((N : ℝ) - 1))
    {x y : Fin N → ℝ} (h : Move k x y) :
    Rmax y + Xpot y / k0 ≤ Rmax x + Xpot x / k0 := by
  obtain ⟨i, j, hij, rfl⟩ := h
  set d : ℝ := x j - x i with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hkd : 0 < k * d := mul_pos hk hdpos
  set v : ℝ := x j + k * d with hv
  have hR : Rmax (Function.update x i v) = max (Rmax x) v := Rmax_update x hij v
  set z : ℝ := Rmax (Function.update x i v) - Rmax x with hz
  have hz0 : 0 ≤ z := by
    rw [hz, hR, sub_nonneg]
    exact le_max_left _ _
  have hzkd : z ≤ k * d := by
    rw [hz, hR, sub_le_iff_le_add]
    apply max_le
    · linarith
    · have hjR : x j ≤ Rmax x := le_Rmax x j
      rw [hv]
      linarith
  have hXdiff : Xpot (Function.update x i v) - Xpot x = (N : ℝ) * z - (1 + k) * d := by
    simp only [Xpot]
    rw [sum_update, hz, hR]
    have hvi : v - x i = (1 + k) * d := by rw [hv, hd]; ring
    rw [hvi]
    ring
  have hkey : z * k0 + (Xpot (Function.update x i v) - Xpot x) ≤ 0 := by
    rw [hXdiff, hdef]
    have hrw : z * (1 / k - ((N : ℝ) - 1)) + ((N : ℝ) * z - (1 + k) * d)
        = (1 + k) * (z - k * d) / k := by field_simp; ring
    rw [hrw]
    apply div_nonpos_of_nonpos_of_nonneg _ hk.le
    nlinarith [hzkd, hk]
  have h2 : (Xpot (Function.update x i v) - Xpot x) / k0 ≤ -z :=
    div_le_of_mul_le hk0 (by nlinarith [hkey])
  have hsplit : Xpot (Function.update x i v) / k0 - Xpot x / k0
      = (Xpot (Function.update x i v) - Xpot x) / k0 := by ring
  rw [hz] at h2
  linarith [h2, hsplit]

/-- Hence `R + X/k₀` never increases along a sequence of moves. -/
theorem phi_reach {k k0 : ℝ} (hk : 0 < k) (hk0 : 0 < k0) (hdef : k0 = 1 / k - ((N : ℝ) - 1))
    {x y : Fin N → ℝ} (h : Reach k x y) :
    Rmax y + Xpot y / k0 ≤ Rmax x + Xpot x / k0 := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans (phi_step hk hk0 hdef hstep) ih

end Bounded

/-! ### Direction 2: `k ≥ 1/(N-1)` pushes everything right -/

section Unbounded

variable [Nonempty (Fin N)]

/-- Jumping the leftmost point over the rightmost: `X` does not drop and `R` gains at least
`k · X x / N`. -/
theorem advance {k : ℝ} (hk : 0 < k) (hNr : (2 : ℝ) ≤ (N : ℝ))
    (hkN : 1 ≤ ((N : ℝ) - 1) * k) (x : Fin N → ℝ) (hX : 0 < Xpot x) :
    ∃ y, Move k x y ∧ Xpot x ≤ Xpot y ∧ Rmax x + k * Xpot x / (N : ℝ) ≤ Rmax y := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  obtain ⟨j, hj⟩ := exists_Rmax x
  obtain ⟨i, hi⟩ := exists_Lmin x
  have hlt : Lmin x < Rmax x := by
    by_contra hcon
    push Not at hcon
    have hnp : Xpot x ≤ 0 := by
      rw [Xpot_eq_sum]
      refine Finset.sum_nonpos fun l _ => ?_
      have h1 : Lmin x ≤ x l := Lmin_le x l
      linarith
    linarith
  have hij : x i < x j := by rw [hi, hj]; exact hlt
  have hdpos : 0 < x j - x i := by linarith
  have hkd : 0 < k * (x j - x i) := mul_pos hk hdpos
  have hR : Rmax (Function.update x i (x j + k * (x j - x i))) = x j + k * (x j - x i) := by
    rw [Rmax_update x hij]
    apply max_eq_right
    rw [← hj]
    linarith
  refine ⟨_, ⟨i, j, hij, rfl⟩, ?_, ?_⟩
  · -- the spread does not decrease
    have hprod : 0 ≤ (x j - x i) * (((N : ℝ) - 1) * k - 1) :=
      mul_nonneg hdpos.le (by linarith)
    simp only [Xpot]
    rw [hR, sum_update, ← hj]
    nlinarith [hprod]
  · -- the rightmost point advances
    have hdX : Xpot x ≤ (N : ℝ) * (x j - x i) := by
      rw [Xpot_eq_sum]
      calc ∑ l, (Rmax x - x l) ≤ ∑ _l : Fin N, (x j - x i) := by
            refine Finset.sum_le_sum fun l _ => ?_
            have h1 : Lmin x ≤ x l := Lmin_le x l
            rw [hi, hj]
            linarith
        _ = (N : ℝ) * (x j - x i) := by
              simp [mul_comm]
              ring
    have hfin : k * Xpot x / (N : ℝ) ≤ k * (x j - x i) :=
      div_le_of_mul_le hNpos (by nlinarith [hdX, hk])
    rw [hR, ← hj]
    linarith

/-- Iterating `advance`. -/
theorem iterate {k : ℝ} (hk : 0 < k) (hNr : (2 : ℝ) ≤ (N : ℝ))
    (hkN : 1 ≤ ((N : ℝ) - 1) * k) (x : Fin N → ℝ) (hX : 0 < Xpot x) (n : ℕ) :
    ∃ y, Reach k x y ∧ Xpot x ≤ Xpot y ∧
      Rmax x + (n : ℝ) * (k * Xpot x / (N : ℝ)) ≤ Rmax y := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  induction n with
  | zero => exact ⟨x, Reach.refl k x, le_refl _, by simp⟩
  | succ n ih =>
      obtain ⟨y, hy, hXy, hRy⟩ := ih
      obtain ⟨w, hmove, hXw, hRw⟩ := advance hk hNr hkN y (lt_of_lt_of_le hX hXy)
      refine ⟨w, hy.trans (Relation.ReflTransGen.single hmove), le_trans hXy hXw, ?_⟩
      have hmono : k * Xpot x / (N : ℝ) ≤ k * Xpot y / (N : ℝ) := by
        have h1 : k * Xpot y / (N : ℝ) - k * Xpot x / (N : ℝ)
            = k * (Xpot y - Xpot x) / (N : ℝ) := by ring
        have h2 : 0 ≤ k * (Xpot y - Xpot x) / (N : ℝ) :=
          div_nonneg (mul_nonneg hk.le (by linarith)) hNpos.le
        linarith
      push_cast
      nlinarith [hRy, hRw, hmono]

/-- Once the rightmost point is past `M`, finitely many jumps bring every point past `M`. -/
theorem cleanup {k : ℝ} (hk : 0 < k) (M : ℝ) :
    ∀ (n : ℕ) (x : Fin N → ℝ), ({i | x i ≤ M} : Finset (Fin N)).card ≤ n → M < Rmax x →
      ∃ y, Reach k x y ∧ ∀ i, M < y i := by
  intro n
  induction n with
  | zero =>
      intro x hcard _
      refine ⟨x, Reach.refl k x, fun i => ?_⟩
      by_contra hcon
      push Not at hcon
      have hmem : i ∈ ({i | x i ≤ M} : Finset (Fin N)) := by simpa using hcon
      have := Finset.card_pos.2 ⟨i, hmem⟩
      omega
  | succ n ih =>
      intro x hcard hM
      by_cases hall : ∀ i, M < x i
      · exact ⟨x, Reach.refl k x, hall⟩
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨j, hj⟩ := exists_Rmax x
        have hij : x i < x j := by rw [hj]; linarith
        have hkd : 0 < k * (x j - x i) := mul_pos hk (by linarith)
        have hvR : Rmax x < x j + k * (x j - x i) := by rw [← hj]; linarith
        have hR : Rmax (Function.update x i (x j + k * (x j - x i)))
            = x j + k * (x j - x i) := by
          rw [Rmax_update x hij]
          exact max_eq_right hvR.le
        have hsub : ({l | Function.update x i (x j + k * (x j - x i)) l ≤ M} : Finset (Fin N))
            ⊆ ({l | x l ≤ M} : Finset (Fin N)).erase i := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          have hli : l ≠ i := by
            intro h
            rw [h, upd_self] at hl
            linarith
          rw [upd_ne x hli] at hl
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hli, hl⟩
        have himem : i ∈ ({l | x l ≤ M} : Finset (Fin N)) := by simpa using hi
        have hcard' :
            ({l | Function.update x i (x j + k * (x j - x i)) l ≤ M} : Finset (Fin N)).card
              ≤ n := by
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem himem] at h1
          omega
        obtain ⟨z, hz1, hz2⟩ := ih _ hcard' (by rw [hR]; linarith)
        exact ⟨z, Reach.head ⟨i, j, hij, rfl⟩ hz1, hz2⟩

end Unbounded

/-! ### The theorem -/
