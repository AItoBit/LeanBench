by
  let u := B - A
  let v := D - A
  have hi : LinearIndependent ℝ ![u, v] := hnd
  have hspan : Submodule.span ℝ ({u, v} : Set Plane) = ⊤ := by
    simpa [Set.pair_comm] using hi.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : E - A ∈ Submodule.span ℝ ({u, v} : Set Plane) := by
    rw [hspan]
    trivial
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hmem
  have he : E - A = (1 + (p - 1)) • u + (1 + (q - 1)) • v := by
    calc
      _ = p • u + q • v := hpq.symm
      _ = _ := by module
  obtain ⟨t, ht, ht1, hFt⟩ := hF
  obtain ⟨s, hGs⟩ := hG
  obtain ⟨k, hk⟩ := hline
  obtain ⟨O, R, hBO, hCO, hDO, hEO⟩ := hcyclic
  have hc : C - A = u + v := by
    rw [hpar]
    dsimp [u, v]
    abel
  have hf : F - A = v + t • u := by
    rw [hFt, hpar]
    dsimp [u, v]
    module
  have hg : G - A = u + s • v := by
    rw [hGs, hpar]
    dsimp [u, v]
    module
  rw [hg, hf] at hk
  have circle_eq (X : Plane) (hX : dist X O = R) :
      ‖(X - A) - (O - A)‖ ^ 2 = R ^ 2 := by
    have hh : (X - A) - (O - A) = X - O := by abel
    rw [hh]
    simpa only [dist_eq_norm] using congrArg (fun a : ℝ => a ^ 2) hX
  have distance_eq (X Y Z : Plane) (h : dist X Y = dist X Z) :
      ‖(X - A) - (Y - A)‖ ^ 2 = ‖(X - A) - (Z - A)‖ ^ 2 := by
    have hy : (X - A) - (Y - A) = X - Y := by abel
    have hz : (X - A) - (Z - A) = X - Z := by abel
    rw [hy, hz]
    simpa only [dist_eq_norm] using congrArg (fun a : ℝ => a ^ 2) h
  have hBC := circle_eq B hBO
  have hDC := circle_eq D hDO
  have hCC := circle_eq C hCO
  have hEC := circle_eq E hEO
  have hFC := distance_eq E F C hEF
  have hGC := distance_eq E G C hEG
  rw [hc] at hCC
  rw [he] at hEC
  rw [he, hf, hc] at hFC
  rw [he, hg, hc] at hGC
  have hresult := core u v (O - A) (p - 1) (q - 1) t s k R
    hi ht ht1 hk hBC hDC hCC hEC hFC hGC
  change InnerProductGeometry.angle v (F - A) = InnerProductGeometry.angle (F - A) u
  rw [hf]
  exact hresult
