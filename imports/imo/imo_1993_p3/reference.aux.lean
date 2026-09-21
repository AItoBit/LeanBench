/-- Of three squares carrying the three different colours, exactly one has colour `c`. -/
theorem colors_sum (e : ZMod 3) (he : e = 1 ∨ e = 2) (x c : ZMod 3) :
    (if x = c then (1 : ZMod 2) else 0) + (if x + e = c then 1 else 0)
      + (if x + 2 * e = c then 1 else 0) = 1 := by
  rcases he with rfl | rfl <;> revert x c <;> decide

/-- Every colour parity flips on each jump. -/
theorem w_move {S T : Finset Pos} (h : Move S T) (c : ZMod 3) : w c T = w c S + 1 := by
  obtain ⟨p, d, hd, hp, hq, hr, rfl⟩ := h
  have hcq : color (p.1 + d.1, p.2 + d.2) = color p + ((d.1 + d.2 : ℤ) : ZMod 3) := by
    simp only [color]
    push_cast
    ring
  have hcr : color (p.1 + 2 * d.1, p.2 + 2 * d.2)
      = color p + 2 * ((d.1 + d.2 : ℤ) : ZMod 3) := by
    simp only [color]
    push_cast
    ring
  have he : ((d.1 + d.2 : ℤ) : ZMod 3) = 1 ∨ ((d.1 + d.2 : ℤ) : ZMod 3) = 2 := by
    rcases hd with rfl | rfl | rfl | rfl <;> norm_num <;> decide
  have hqp : (p.1 + d.1, p.2 + d.2) ≠ p := by
    intro hcon
    rcases hd with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff] at hcon
  have hqmem : (p.1 + d.1, p.2 + d.2) ∈ S.erase p := Finset.mem_erase.2 ⟨hqp, hq⟩
  have hrmem : (p.1 + 2 * d.1, p.2 + 2 * d.2)
      ∉ (S.erase p).erase (p.1 + d.1, p.2 + d.2) := by
    intro hcon
    exact hr (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcon))
  unfold w
  rw [Finset.sum_insert hrmem]
  have e1 := Finset.add_sum_erase S (fun x : Pos => if color x = c then (1 : ZMod 2) else 0) hp
  have e2 := Finset.add_sum_erase (S.erase p)
    (fun x : Pos => if color x = c then (1 : ZMod 2) else 0) hqmem
  have hsum := colors_sum _ he (color p) c
  rw [hcq] at e2
  rw [hcr]
  have hchar : ∀ z : ZMod 2, z + z = 0 := by decide
  linear_combination e1 + e2 + hsum
    - hchar (if color p = c then (1 : ZMod 2) else 0)
    - hchar (if color p + ((d.1 + d.2 : ℤ) : ZMod 3) = c then (1 : ZMod 2) else 0)

theorem color_nat (i j : ℕ) : color ((i : ℤ), (j : ℤ)) = ((i + j : ℕ) : ZMod 3) := by
  simp only [color]
  push_cast
  ring

/-- Each row of length `3m` contains `m` squares of each colour. -/
theorem row_sum (m i : ℕ) (c : ZMod 3) :
    ∑ j ∈ Finset.range (3 * m), (if ((i + j : ℕ) : ZMod 3) = c then (1 : ZMod 2) else 0)
      = (m : ZMod 2) := by
  have h30 : (3 : ZMod 3) = 0 := by decide
  induction m with
  | zero => simp
  | succ m ih =>
    have h3 : 3 * (m + 1) = 3 * m + 1 + 1 + 1 := by ring
    rw [h3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have c0 : ((i + 3 * m : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) := by
      push_cast
      rw [h30]
      ring
    have c1 : ((i + (3 * m + 1) : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) + 1 := by
      push_cast
      rw [h30]
      ring
    have c2 : ((i + (3 * m + 1 + 1) : ℕ) : ZMod 3) = ((i : ℕ) : ZMod 3) + 2 * 1 := by
      push_cast
      rw [h30]
      ring
    rw [c0, c1, c2]
    have hsum := colors_sum 1 (Or.inl rfl) ((i : ℕ) : ZMod 3) c
    push_cast
    linear_combination hsum

theorem w_board (m : ℕ) (c : ZMod 3) : w c (board (3 * m)) = ((3 * m * m : ℕ) : ZMod 2) := by
  unfold w board
  rw [Finset.sum_image (by intro x _ y _ hxy; simpa [Prod.ext_iff] using hxy)]
  rw [Finset.sum_product]
  have hrow : ∀ i ∈ Finset.range (3 * m),
      (∑ j ∈ Finset.range (3 * m),
        (if color (((i : ℕ) : ℤ), ((j : ℕ) : ℤ)) = c then (1 : ZMod 2) else 0))
      = (m : ZMod 2) := by
    intro i _
    rw [← row_sum m i c]
    exact Finset.sum_congr rfl fun j _ => by rw [color_nat]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring
