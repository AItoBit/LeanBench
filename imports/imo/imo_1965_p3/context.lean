noncomputable section

namespace IMO1965P3

/-- The linear scaling factor along the transversal segments `AD, BC, etc.` -/
def ratio (k : ℝ) : ℝ := k / (k + 1)

/-- Volume of the small tetrahedron `APWX`, scaled by `r³`. -/
def volTetra (k : ℝ) (V : ℝ) : ℝ :=
  (ratio k) ^ 3 * V

/-- Volume of the prism `WXPBYZ`.
    Its base `BYZ` has area scaled by `r²`, and its height relative to `ABCD`
    is `1 - r = 1 / (k + 1)`. Since a triangular prism of the same base and height
    as a tetrahedron has 3 times the tetrahedron's volume, its volume is
    `3 * r² * (1 - r) * V`. -/
def volPrism (k : ℝ) (V : ℝ) : ℝ :=
  3 * (ratio k) ^ 2 * (1 - ratio k) * V

/-- Volume of the solid `ABWXYZ` containing edge `AB`. -/
def volLower (k : ℝ) (V : ℝ) : ℝ :=
  volTetra k V + volPrism k V

/-- Volume of the complementary solid containing edge `CD`. -/
def volUpper (k : ℝ) (V : ℝ) : ℝ :=
  V - volLower k V

/-! ## The algebraic identities for the dissection -/
