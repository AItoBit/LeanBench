namespace Imo2000P3

variable {N : ℕ}

/-- One move: coordinate `i` jumps over coordinate `j`, which lies strictly to its right. -/
def Move (k : ℝ) (x y : Fin N → ℝ) : Prop :=
  ∃ i j : Fin N, x i < x j ∧ y = Function.update x i (x j + k * (x j - x i))

/-- Reachability by finitely many moves. -/
def Reach (k : ℝ) : (Fin N → ℝ) → (Fin N → ℝ) → Prop := Relation.ReflTransGen (Move k)

section Potential

variable [Nonempty (Fin N)]

/-- The rightmost position. -/
noncomputable def Rmax (x : Fin N → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

/-- The leftmost position. -/
noncomputable def Lmin (x : Fin N → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty x

/-- The spread `X x = Σ (R x - x l)`. -/
noncomputable def Xpot (x : Fin N → ℝ) : ℝ := (N : ℝ) * Rmax x - ∑ l, x l

end Potential

/-! ### Direction 1: `k < 1/(N-1)` keeps everything bounded -/

section Bounded

variable [Nonempty (Fin N)]

end Bounded

/-! ### Direction 2: `k ≥ 1/(N-1)` pushes everything right -/

section Unbounded

variable [Nonempty (Fin N)]

end Unbounded

/-! ### The theorem -/
