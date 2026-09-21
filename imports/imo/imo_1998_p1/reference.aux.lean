/-- With the diagonal intersection as origin and the diagonals as axes,
    the vertices are (a,0), (0,b), (-c,0), (0,-d). -/
theorem cyclic_iff (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Cyclic (a,0) (0,b) (-c,0) (0,-d) ↔ a*c = b*d := by
  constructor
  · rintro ⟨⟨u,v⟩, r, _, hA, hB, hC, hD⟩
    dsimp [sqDist] at hA hB hC hD
    have hu : 2*u = a-c := by
      have h : (a+c) * (2*u-a+c) = 0 := by nlinarith [hA, hC]
      have hn : a+c ≠ 0 := ne_of_gt (add_pos ha hc)
      have := (mul_eq_zero.mp h).resolve_left hn
      linarith
    have hBD : (b+d) * (2*v-b+d) = 0 := by nlinarith [hB, hD]
    have hv : 2*v = b-d := by
      have hn : b+d ≠ 0 := ne_of_gt (add_pos hb hd)
      have := (mul_eq_zero.mp hBD).resolve_left hn
      linarith
    nlinarith [hA, hB]
  · intro h
    refine ⟨((a-c)/2, (b-d)/2),
      sqDist (a,0) ((a-c)/2, (b-d)/2), ?_, rfl, ?_, ?_, ?_⟩
    · dsimp [sqDist]
      have : 0 < a - (a-c)/2 := by linarith
      nlinarith [sq_pos_of_pos this, sq_nonneg ((0:ℝ)-(b-d)/2)]
    all_goals dsimp [sqDist]; nlinarith
