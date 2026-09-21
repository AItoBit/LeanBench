/-- The statement for points of `ℝ³`, with the projections onto the `yz`-, `zx`- and `xy`-planes
identified with their images in `ℝ²`. -/
theorem candidate (S : Finset (ℝ × ℝ × ℝ)) :
    S.card ^ 2
      ≤ (S.image fun p => (p.2.1, p.2.2)).card
        * (S.image fun p => (p.1, p.2.2)).card
        * (S.image fun p => (p.1, p.2.1)).card :=
