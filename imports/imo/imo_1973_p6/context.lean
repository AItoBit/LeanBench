namespace Imo1973P6

/-! ### Powers of `q` -/

/-- `dd k j = |k - j|`. -/
private def dd (k j : ℕ) : ℕ := (k - j) + (j - k)

/-- `cₖ = ∑ⱼ q^{|k-j|} aⱼ`. -/
private noncomputable def cc (n : ℕ) (q : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, q ^ dd k j * a j
