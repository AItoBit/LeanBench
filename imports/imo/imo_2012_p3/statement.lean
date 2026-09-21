/--
Abstract form of the potential strategy in IMO 2012 Problem 3(b).

If

* `g 0 < rho^(k+1)`,
* every next potential is at most `(N + rho*g m)/2`,
* `N < rho^(k+1)/1000`,

then

    g m < rho^(k+1)

for every step `m`.
-/
theorem candidate
    (N : ℝ)
    (k : ℕ)
    (g : ℕ → ℝ)
    (hg0 :
      g 0 < rho ^ (k + 1))
    (hstep :
      ∀ m : ℕ,
        g (m + 1)
          ≤
        (N + rho * g m) / 2)
    (hN :
      N < rho ^ (k + 1) / 1000) :
    ∀ m : ℕ,
      g m < rho ^ (k + 1) :=
