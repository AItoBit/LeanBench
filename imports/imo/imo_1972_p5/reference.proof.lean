by
  -- the set of values `|f x|` is nonempty and bounded above
  have hbdd : BddAbove (Set.range fun x => |f x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hf1 x
  have hSne : (Set.range fun x => |f x|).Nonempty := ⟨|f 0|, ⟨0, rfl⟩⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = sSup (Set.range fun x => |f x|) := ⟨_, rfl⟩
  have hub : ∀ x, |f x| ≤ u := by
    intro x
    rw [hu]
    exact le_csSup hbdd ⟨x, rfl⟩
  -- `u` is positive because `f` is not identically zero
  obtain ⟨x₀, hx₀⟩ := hnz
  have hupos : 0 < u := lt_of_lt_of_le (abs_pos.mpr hx₀) (hub x₀)
  -- `abs_add` no longer exists under that name; prove it locally from stable lemmas
  have habs : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := by
    intro a b
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [neg_abs_le a, neg_abs_le b]
    · linarith [le_abs_self a, le_abs_self b]
  -- the main estimate
  have key : ∀ x y, |f x| * |g y| ≤ u := by
    intro x y
    have h1 : |f (x + y) + f (x - y)| = 2 * (|f x| * |g y|) := by
      rw [hfg x y, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      ring
    have h2 : 2 * (|f x| * |g y|) ≤ |f (x + y)| + |f (x - y)| := by
      rw [← h1]
      exact habs _ _
    have h3 := hub (x + y)
    have h4 := hub (x - y)
    linarith
  -- conclusion
  intro y
  by_contra hy'
  have hy : 1 < |g y| := not_le.mp hy'
  have hgpos : (0 : ℝ) < |g y| := lt_trans one_pos hy
  have hne0 : |g y| ≠ 0 := hgpos.ne'
  have hbound : ∀ z ∈ (Set.range fun x => |f x|), z ≤ u * (|g y|)⁻¹ := by
    rintro _ ⟨x, rfl⟩
    calc |f x| = |f x| * |g y| * (|g y|)⁻¹ := (mul_inv_cancel_right₀ hne0 (|f x|)).symm
      _ ≤ u * (|g y|)⁻¹ :=
          mul_le_mul_of_nonneg_right (key x y) (inv_nonneg.mpr hgpos.le)
  have h5 : u ≤ u * (|g y|)⁻¹ := by
    have h := csSup_le hSne hbound
    rwa [← hu] at h
  have h6 : u * |g y| ≤ u := by
    have h := mul_le_mul_of_nonneg_right h5 hgpos.le
    rwa [inv_mul_cancel_right₀ hne0 u] at h
  nlinarith [mul_pos hupos (show (0 : ℝ) < |g y| - 1 by linarith)]
