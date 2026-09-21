/-- **IMO 1976, Problem 5.**  For a homogeneous linear system of `p` equations in `q = 2p`
unknowns whose coefficients all lie in `{-1, 0, 1}`, there is a nontrivial integer solution
all of whose entries are bounded in absolute value by `q`. -/
theorem candidate (p q : ℕ) (hp : 0 < p) (hq : q = 2 * p)
    (a : Fin p → Fin q → ℤ) (ha : ∀ i j, a i j = -1 ∨ a i j = 0 ∨ a i j = 1) :
    ∃ x : Fin q → ℤ,
      (∀ i : Fin p, ∑ j : Fin q, a i j * x j = 0) ∧ (∃ j : Fin q, x j ≠ 0) ∧
        (∀ j : Fin q, |x j| ≤ (q : ℤ)) :=
