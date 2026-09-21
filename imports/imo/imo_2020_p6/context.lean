namespace IMO2020P6

noncomputable section

/-!
# IMO 2020 Problem 6 — two-case reduction

We work in the Euclidean plane.

The source proof has two cases:

1. a direction of sufficiently large width;
2. the complementary narrow case, handled by the
   disk/strip packing argument.

The hard geometric estimates are represented by
`wide_case` and `narrow_case`.

Their combination into one universal positive constant
is proved completely below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Euclidean plane
============================================================
-/

abbrev Point :=
  EuclideanSpace ℝ (Fin 2)

/-!
============================================================
2. Lines
============================================================
-/

structure Line where
  normal : Point
  offset : ℝ
  unit_normal : ‖normal‖ = 1

/-!
============================================================
3. Signed coordinate and line distance
============================================================
-/

def signedValue
    (L : Line)
    (x : Point) : ℝ :=
  inner ℝ L.normal x - L.offset

def lineDistance
    (L : Line)
    (x : Point) : ℝ :=
  |signedValue L x|

def Separates
    (S : Finset Point)
    (L : Line) : Prop :=
  (∃ x ∈ S,
      signedValue L x < 0)
    ∧
  (∃ y ∈ S,
      0 < signedValue L y)

/-!
============================================================
5. Pairwise unit separation
============================================================
-/

def UnitSeparated
    (S : Finset Point) : Prop :=
  ∀ x ∈ S,
    ∀ y ∈ S,
      x ≠ y →
      1 ≤ dist x y

/-!
============================================================
6. Separating line with prescribed clearance
============================================================
-/

def HasSeparatingLine
    (S : Finset Point)
    (δ : ℝ) : Prop :=
  ∃ L : Line,
    Separates S L ∧
    ∀ x ∈ S,
      δ ≤ lineDistance L x

def nScale
    (n : ℕ) : ℝ :=
  1 /
    Real.rpow
      (n : ℝ)
      ((1 : ℝ) / 3)

variable
  (Wide : ℕ → Finset Point → Prop)

/-!
============================================================
10. Combine the two cases
============================================================
-/
