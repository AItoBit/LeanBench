/-- **IMO 1976, Problem 3.**  A box with positive integer sides `a`, `b`, `c` is filled with as
many cubes of volume `2` (i.e. of edge `∛2`) as possible, their edges parallel to the edges of the
box; the number of such cubes is `⌊a/∛2⌋ * ⌊b/∛2⌋ * ⌊c/∛2⌋`.  Exactly `40 %` of the volume of the
box is filled precisely when the sides are, in some order, `2, 3, 5` or `2, 5, 6`. -/
theorem candidate (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * ((⌊(a : ℝ) / cbrt2⌋₊ : ℝ) * (⌊(b : ℝ) / cbrt2⌋₊ : ℝ) * (⌊(c : ℝ) / cbrt2⌋₊ : ℝ))
        = (2 / 5) * ((a : ℝ) * (b : ℝ) * (c : ℝ)) ↔
      ({a, b, c} : Multiset ℕ) = {2, 3, 5} ∨ ({a, b, c} : Multiset ℕ) = {2, 5, 6} :=
