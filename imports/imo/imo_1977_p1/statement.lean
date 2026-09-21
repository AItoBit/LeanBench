namespace Imo1977P1

/-- **IMO 1977, Problem 1.** -/

theorem candidate (o p A B C D K L M N : ℂ) (hp : p ≠ 0)
    (hA : A = o + p) (hB : B = o + Complex.I * p)
    (hC : C = o - p) (hD : D = o - Complex.I * p)
    (hK : K = (A + B) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I * (B - A))
    (hL : L = (B + C) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I * (C - B))
    (hM : M = (C + D) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I * (D - C))
    (hN : N = (D + A) / 2 + (Real.sqrt 3 : ℂ) / 2 * Complex.I * (A - D)) :
    ∃ w ζ : ℂ, w ≠ 0 ∧ ζ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 12) ∧
      (L + M) / 2 = o + w * ζ ^ 0 ∧
      (A + N) / 2 = o + w * ζ ^ 1 ∧
      (B + L) / 2 = o + w * ζ ^ 2 ∧
      (M + N) / 2 = o + w * ζ ^ 3 ∧
      (B + K) / 2 = o + w * ζ ^ 4 ∧
      (C + M) / 2 = o + w * ζ ^ 5 ∧
      (N + K) / 2 = o + w * ζ ^ 6 ∧
      (C + L) / 2 = o + w * ζ ^ 7 ∧
      (D + N) / 2 = o + w * ζ ^ 8 ∧
      (K + L) / 2 = o + w * ζ ^ 9 ∧
      (D + M) / 2 = o + w * ζ ^ 10 ∧
      (A + K) / 2 = o + w * ζ ^ 11 :=
