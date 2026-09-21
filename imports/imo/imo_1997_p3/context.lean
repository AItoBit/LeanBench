namespace Imo1997P3

/-- `f [x₁, …, xₙ] = x₁ + 2x₂ + ⋯ + n xₙ`. -/
noncomputable def f : List ℝ → ℝ
  | [] => 0
  | a :: t => a + f t + t.sum

/-- `l'` is `l` with two adjacent entries, both bounded by `B`, exchanged. -/
def AdjSwap (B : ℝ) (l l' : List ℝ) : Prop :=
  ∃ (pre post : List ℝ) (a b : ℝ), |a| ≤ B ∧ |b| ≤ B ∧
    l = pre ++ a :: b :: post ∧ l' = pre ++ b :: a :: post
