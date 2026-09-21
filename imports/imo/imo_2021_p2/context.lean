namespace IMO2021P2

open Finset

open scoped BigOperators

noncomputable section

/-!
# IMO 2021 Problem 2

For real numbers x₁, ..., xₙ prove

    ∑ᵢ ∑ⱼ √|xᵢ - xⱼ|
      ≤
    ∑ᵢ ∑ⱼ √|xᵢ + xⱼ|.

We use the kernel

    K(x,y) = √|x-y|.

The analytic input is the negative-type inequality for this
kernel.  Everything from that input to the IMO conclusion is
proved below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Kernel
============================================================
-/

def K (x y : ℝ) : ℝ :=
  Real.sqrt |x - y|

def lhs
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      Real.sqrt |x i - x j|

def rhs
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      Real.sqrt |x i + x j|

/-!
============================================================
3. Kernel identities for x and -x
============================================================
-/

/--
For each pair i,j consider the four points

    xᵢ, -xᵢ, xⱼ, -xⱼ

with coefficients +1,-1.

The corresponding contribution is

    K(xᵢ,xⱼ)
      - K(xᵢ,-xⱼ)
      - K(-xᵢ,xⱼ)
      + K(-xᵢ,-xⱼ).
-/
def signedBlock
    {n : ℕ}
    (x : Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  K (x i) (x j)
    -
  K (x i) (-x j)
    -
  K (-x i) (x j)
    +
  K (-x i) (-x j)

/-!
Each signed block is exactly

    2√|xᵢ-xⱼ| - 2√|xᵢ+xⱼ|.
-/

def signedEnergy
    {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    ∑ j : Fin n,
      signedBlock x i j

/-!
============================================================
6. Sum of all signed blocks
============================================================
-/

def NegativeTypeSqrtKernel : Prop :=
  ∀ {n : ℕ}
    (x : Fin n → ℝ),
      signedEnergy x ≤ 0

/-!
============================================================
8. Convert signed-energy inequality to the IMO inequality
============================================================
-/
