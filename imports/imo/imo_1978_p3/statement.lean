namespace Imo1978P3

/-- **IMO 1978, Problem 3.** -/

theorem candidate (f g : ℕ → ℕ)
    (hfmono : ∀ a b, 1 ≤ a → a < b → f a < f b)
    (hgmono : ∀ a b, 1 ≤ a → a < b → g a < g b)
    (hfpos : ∀ n, 1 ≤ n → 1 ≤ f n)
    (hgpos : ∀ n, 1 ≤ n → 1 ≤ g n)
    (hdisj : ∀ a b, 1 ≤ a → 1 ≤ b → f a ≠ g b)
    (hcover : ∀ m, 1 ≤ m → (∃ k, 1 ≤ k ∧ f k = m) ∨ (∃ k, 1 ≤ k ∧ g k = m))
    (hgf : ∀ n, 1 ≤ n → g n = f (f n) + 1) :
    f 240 = 388 :=
