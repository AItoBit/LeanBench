namespace IMO2007P1

variable {n : ℕ}

noncomputable def prefixMax (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (Finset.Iic i).sup' ⟨i, by simp⟩ a

noncomputable def suffixMin (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  (Finset.Ici i).inf' ⟨i, by simp⟩ a

noncomputable def gap (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  prefixMax a i - suffixMin a i

noncomputable def d (a : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (gap a)

noncomputable def error (a x : Fin (n + 1) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |x i - a i|)

/-- The explicit optimal nondecreasing sequence. -/
noncomputable def optimal (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  prefixMax a i - d a / 2
