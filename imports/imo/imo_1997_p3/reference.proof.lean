by
  set c : ℝ := ((n : ℝ) + 1) / 2 with hcdef
  have hc : 0 ≤ c := by positivity
  by_contra hcon
  have hcon' : ∀ y : List ℝ, List.Perm y x → ¬ (|f y| ≤ c) := by
    intro y hy hle
    exact hcon ⟨y, hy, hle⟩
  have hrev : Relation.ReflTransGen (AdjSwap c) x x.reverse := reach_reverse x hbd
  have hno : ∀ z, Relation.ReflTransGen (AdjSwap c) x z → ¬ (|f z| ≤ c) :=
    fun z hz => hcon' z (reach_perm hz)
  have hkey : f x + f x.reverse = ((n : ℝ) + 1) * x.sum := by
    rw [f_add_reverse, hlen]
  have hx := hno x Relation.ReflTransGen.refl
  have hrv := hno _ hrev
  rw [not_le] at hx hrv
  have hsum2 : f x + f x.reverse = 2 * c ∨ f x + f x.reverse = -(2 * c) := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).1 hsum with hh | hh
    · left; rw [hkey, hh, hcdef]; ring
    · right; rw [hkey, hh, hcdef]; ring
  rw [lt_abs] at hx hrv
  rcases hx with hx | hx
  · -- `c < f x` : run the argument for `f`
    have hrvneg : f x.reverse < -c := by
      rcases hsum2 with hh | hh
      · rcases hrv with hr | hr
        · linarith
        · linarith
      · linarith
    have hfinal : c < f x.reverse :=
      ivt' f (fun l l' hsw => adjSwap_f hsw) hrev hno hx
    linarith
  · -- `c < -(f x)` : run the argument for `-f`
    have hrvpos : c < f x.reverse := by
      rcases hsum2 with hh | hh
      · linarith
      · rcases hrv with hr | hr
        · exact hr
        · linarith
    have hs' : ∀ l l', AdjSwap c l l' → |(-f l) - (-f l')| ≤ 2 * c := by
      intro l l' hsw
      have hb := adjSwap_f hsw
      rw [show -f l - -f l' = -(f l - f l') by ring, abs_neg]
      exact hb
    have hno' : ∀ z, Relation.ReflTransGen (AdjSwap c) x z → ¬ (|(-f z)| ≤ c) := by
      intro z hz hle
      exact hno z hz (by rwa [abs_neg] at hle)
    have hfinal : c < -(f x.reverse) := ivt' (fun l => -f l) hs' hrev hno' hx
    linarith
