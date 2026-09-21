namespace Imo1999P5

/-- The Euclidean inner product on `ℂ`. -/
noncomputable def dot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im
