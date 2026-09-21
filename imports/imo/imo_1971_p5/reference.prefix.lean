namespace Imo1971P5

/-! ### Distance in coordinates -/

private lemma dist_eq_one_iff (z w : ℂ) :
    dist z w = 1 ↔ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1 := by
  rw [Complex.dist_eq_re_im]
  constructor
  · intro h
    have h2 : Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) ^ 2 = 1 ^ 2 := by rw [h]
    rwa [Real.sq_sqrt (by positivity), one_pow] at h2
  · intro h
    rw [h, Real.sqrt_one]

private lemma conj_eq_one_of_dist {z : ℂ} (h : dist z 0 = 1) :
    z * (starRingEnd ℂ) z = 1 := by
  rw [dist_eq_one_iff] at h
  simp only [Complex.zero_re, Complex.zero_im, sub_zero] at h
  rw [Complex.mul_conj, show Complex.normSq z = z.re ^ 2 + z.im ^ 2 by
    rw [Complex.normSq_apply]; ring, h]
  norm_num

private lemma dist_shift (a b c : ℂ) : dist (a - b) c = dist a (b + c) := by
  rw [dist_eq_norm, dist_eq_norm, sub_sub]

/-! ### Two unit circles meet in finitely many points -/

/-- A quadratic with nonzero leading coefficient has finitely many roots:
if `u₀` is one root, every root is `u₀` or `a⁻¹ * (-b - a * u₀)`. -/
private lemma quad_finite {a b c : ℂ} (ha : a ≠ 0) :
    {u : ℂ | a * u ^ 2 + b * u + c = 0}.Finite := by
  rcases Set.eq_empty_or_nonempty {u : ℂ | a * u ^ 2 + b * u + c = 0} with h | h
  · rw [h]; exact Set.finite_empty
  · obtain ⟨u₀, hu₀⟩ := h
    refine Set.Finite.subset
      (Set.Finite.insert u₀ (Set.finite_singleton (a⁻¹ * (-b - a * u₀)))) ?_
    intro v hv
    have hv' : a * v ^ 2 + b * v + c = 0 := hv
    have hu₀' : a * u₀ ^ 2 + b * u₀ + c = 0 := hu₀
    rcases eq_or_ne v u₀ with h' | h'
    · exact Set.mem_insert_iff.mpr (Or.inl h')
    · refine Set.mem_insert_iff.mpr (Or.inr ?_)
      have hne : v - u₀ ≠ 0 := sub_ne_zero.mpr h'
      have hd : (v - u₀) * (a * (v + u₀) + b) = 0 := by linear_combination hv' - hu₀'
      have h2 : a * (v + u₀) + b = 0 := by
        rcases mul_eq_zero.mp hd with h'' | h''
        · exact absurd h'' hne
        · exact h''
      have h3 : a * v = -b - a * u₀ := by linear_combination h2
      show v = a⁻¹ * (-b - a * u₀)
      calc v = a⁻¹ * (a * v) := (inv_mul_cancel_left₀ ha v).symm
        _ = a⁻¹ * (-b - a * u₀) := by rw [h3]

/-- A point on both unit circles (centred at `0` and at `d`) is a root of an
explicit quadratic. -/
private lemma quad_root {d u : ℂ} (hu : dist u 0 = 1) (hud : dist u d = 1) :
    (starRingEnd ℂ) d * u ^ 2 - (d * (starRingEnd ℂ) d) * u + d = 0 := by
  have h1 : u * (starRingEnd ℂ) u = 1 := conj_eq_one_of_dist hu
  have hd1 : dist (u - d) 0 = 1 := by
    rw [dist_eq_one_iff] at hud ⊢
    simpa using hud
  have h2 : (u - d) * ((starRingEnd ℂ) u - (starRingEnd ℂ) d) = 1 := by
    have h := conj_eq_one_of_dist hd1
    rwa [map_sub] at h
  linear_combination (u - d) * h1 - u * h2

private lemma two_circles_finite {d : ℂ} (hd : d ≠ 0) :
    {v : ℂ | dist v d = 1 ∧ dist v 0 = 1}.Finite := by
  have hcd : (starRingEnd ℂ) d ≠ 0 := by
    intro h
    apply hd
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  refine Set.Finite.subset
    (quad_finite (a := (starRingEnd ℂ) d) (b := -(d * (starRingEnd ℂ) d)) (c := d) hcd) ?_
  intro v hv
  have h := quad_root hv.2 hv.1
  show (starRingEnd ℂ) d * v ^ 2 + -(d * (starRingEnd ℂ) d) * v + d = 0
  linear_combination h

/-! ### The unit circle is infinite -/

private lemma circle_infinite : {z : ℂ | dist z 0 = 1}.Infinite := by
  have hre : ∀ t : ℝ, ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I).re = Real.cos t := by
    intro t
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : ∀ t : ℝ, ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I).im = Real.sin t := by
    intro t
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hinj : Set.InjOn (fun t : ℝ => (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)
      (Set.Icc 0 1) := by
    intro a ha b hb hab
    have hc : Real.cos a = Real.cos b := by
      rw [← hre a, ← hre b]
      exact congrArg Complex.re hab
    exact Real.injOn_cos ⟨ha.1, ha.2.trans hpi⟩ ⟨hb.1, hb.2.trans hpi⟩ hc
  refine Set.Infinite.mono ?_ ((Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image hinj)
  rintro z ⟨t, -, rfl⟩
  show dist ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) 0 = 1
  rw [dist_eq_one_iff, hre, him]
  simp [Real.cos_sq_add_sin_sq]

/-! ### Choosing the new direction -/

private lemma exists_good (S : Finset ℂ) :
    ∃ u : ℂ, dist u 0 = 1 ∧
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist (x - y) u ≠ 1 ∧ u ≠ x - y := by
  classical
  obtain ⟨D, hDmem⟩ :
      ∃ D : Finset ℂ, ∀ d : ℂ, d ∈ D ↔ (d ≠ 0 ∧ ∃ x ∈ S, ∃ y ∈ S, d = x - y) := by
    refine ⟨((S ×ˢ S).image (fun p => p.1 - p.2)).erase 0, ?_⟩
    intro d
    constructor
    · intro h
      rw [Finset.mem_erase] at h
      obtain ⟨h0, hi⟩ := h
      obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp hi
      rw [Finset.mem_product] at hp
      exact ⟨h0, p.1, hp.1, p.2, hp.2, hpd.symm⟩
    · rintro ⟨h0, x, hx, y, hy, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨h0, Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
  have hBadFin :
      (⋃ d ∈ (D : Set ℂ), ({v : ℂ | dist v d = 1 ∧ dist v 0 = 1} ∪ {d})).Finite := by
    refine Set.Finite.biUnion D.finite_toSet ?_
    intro d hd
    have hd0 : d ≠ 0 := ((hDmem d).mp (Finset.mem_coe.mp hd)).1
    exact (two_circles_finite hd0).union (Set.finite_singleton d)
  obtain ⟨u, hu⟩ :=
    (Set.Infinite.sdiff circle_infinite hBadFin).nonempty
  refine ⟨u, hu.1, ?_⟩
  intro x hx y hy hxy
  have hdmem : x - y ∈ (D : Set ℂ) :=
    Finset.mem_coe.mpr ((hDmem _).mpr ⟨sub_ne_zero.mpr hxy, x, hx, y, hy, rfl⟩)
  constructor
  · intro hcon
    refine hu.2 (Set.mem_biUnion hdmem (Or.inl ⟨?_, hu.1⟩))
    rwa [dist_comm] at hcon
  · intro hcon
    exact hu.2 (Set.mem_biUnion hdmem (Or.inr hcon))

/-! ### The theorem -/
