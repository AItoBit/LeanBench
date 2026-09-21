by
  -- a translation in `G` is the identity
  have htrans : ∀ h ∈ G, ∀ β : ℝ, (∀ x, h x = x + β) → β = 0 := by
    intro h hhG β hb
    obtain ⟨x, hx⟩ := hfix h hhG
    rw [hb] at hx
    linarith
  -- the key relation between the coefficients of any two elements
  have key : ∀ f ∈ G, ∀ g ∈ G, ∀ a₁ b₁ a₂ b₂ : ℝ, a₁ ≠ 0 → a₂ ≠ 0 →
      (∀ x, f x = a₁ * x + b₁) → (∀ x, g x = a₂ * x + b₂) →
      a₂ * b₁ + b₂ - a₁ * b₂ - b₁ = 0 := by
    intro f hfG g hgG a₁ b₁ a₂ b₂ ha₁ ha₂ hf hg
    have hFG : (f ∘ g) ∈ G := hcomp f hfG g hgG
    have hKG : (g ∘ f) ∈ G := hcomp g hgG f hfG
    obtain ⟨Finv, hFinvG, hR, -⟩ := hinv (f ∘ g) hFG
    have hhG : (Finv ∘ (g ∘ f)) ∈ G := hcomp Finv hFinvG (g ∘ f) hKG
    obtain ⟨α, β, hα, hh⟩ := hform _ hhG
    -- `(f ∘ g) (h x) = (g ∘ f) x`, written out in coefficients
    have hExp : ∀ x : ℝ,
        a₁ * (a₂ * (α * x + β) + b₂) + b₁ = a₂ * (a₁ * x + b₁) + b₂ := by
      intro x
      have h := hR ((g ∘ f) x)
      have hval := hh x
      simp only [Function.comp_apply] at h hval
      rw [hval] at h
      simp only [hf, hg] at h
      exact h
    have h0 := hExp 0
    have h1 := hExp 1
    -- the linear coefficient of `h` is `1`
    have hprod : a₁ * a₂ * (α - 1) = 0 := by linear_combination h1 - h0
    have hα1 : α = 1 := by
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' ha₁
        · exact absurd h' ha₂
      · linarith
    -- so `h` is a translation, hence its constant term vanishes
    have hβ : β = 0 := by
      refine htrans _ hhG β ?_
      intro x
      rw [hh, hα1]
      ring
    rw [hβ] at h0
    linear_combination -h0
  -- either every element is the identity, or we can pick a non-identity one
  by_cases hex : ∃ f₀ ∈ G, ∃ y, f₀ y ≠ y
  · obtain ⟨f₀, hf₀G, y, hy⟩ := hex
    obtain ⟨a₀, b₀, ha₀0, hf₀⟩ := hform f₀ hf₀G
    have ha₀ : a₀ ≠ 1 := by
      intro h
      apply hy
      have hb₀ : b₀ = 0 := by
        refine htrans f₀ hf₀G b₀ ?_
        intro x
        rw [hf₀, h]
        ring
      rw [hf₀, h, hb₀]
      ring
    obtain ⟨x₀, hx₀⟩ := hfix f₀ hf₀G
    rw [hf₀] at hx₀
    refine ⟨x₀, ?_⟩
    intro f hfG
    obtain ⟨a, b, ha0, hf⟩ := hform f hfG
    have hrel := key f hfG f₀ hf₀G a b a₀ b₀ ha0 ha₀0 hf hf₀
    have h1 : (1 : ℝ) - a₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm ha₀)
    have hfact : (1 - a₀) * (x₀ * (1 - a) - b) = 0 := by
      linear_combination hrel - (1 - a) * hx₀
    have h2 : x₀ * (1 - a) - b = 0 := by
      rcases mul_eq_zero.mp hfact with h | h
      · exact absurd h h1
      · exact h
    rw [hf]
    linear_combination -h2
  · refine ⟨0, ?_⟩
    intro f hfG
    by_contra hcon
    exact hex ⟨f, hfG, 0, hcon⟩
