namespace Imo1977P3

/-- `m` belongs to `Vₙ`. -/
def V (n m : ℕ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ m = 1 + j * n

/-- `m` is indecomposable in `Vₙ`. -/
def Indec (n m : ℕ) : Prop := V n m ∧ ¬ ∃ p q, V n p ∧ V n q ∧ m = p * q
