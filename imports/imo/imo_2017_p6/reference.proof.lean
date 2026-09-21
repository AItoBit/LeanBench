by

  obtain ⟨α, β, hαβ⟩ :=
    primitive_bezout hp

  let L : Poly :=
    MvPolynomial.C α * X +
    MvPolynomial.C β * Y

  refine
    ⟨MvPolynomial.C M * L ^ d, ?_⟩

  have hL :
      MvPolynomial.eval (pointVal p) L = 1 := by
    dsimp [L]
    simp [X, Y, pointVal]
    exact hαβ

  simp [L, hL]
