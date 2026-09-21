namespace IMO2017P4

/-
IMO 2017 Problem 4

The PDF's Solution 2 performs the following angle chase:

  ∠KST = ∠SRK + ∠SKR = ∠KRA

and, after introducing B as the reflection of A in S,

  ∠RBT = ∠RAT

which gives

  ∠KST + ∠KBT = 180°,

so SKBT is cyclic.

Then

  ∠SBK = ∠STK = ∠SAT,

which is exactly the tangent-chord criterion for KT
to be tangent to Γ at T.

Since Mathlib does not currently provide the required
minor-arc infrastructure conveniently, we encode directed
angles algebraically in ℝ / πℤ.
-/

abbrev Angle := AddCircle (Real.pi : ℝ)


/- ============================================================
   Basic angle infrastructure
   ============================================================ -/

/--
Two directed angles are supplementary exactly when their sum
is zero modulo π.

Since directed Euclidean angles naturally live modulo π,
180 degrees is identified with zero.
-/
def Supplementary (α β : Angle) : Prop :=
  α + β = 0

/--
Abstract tangent-chord criterion.

`TangentChord τ χ` means that the angle made by the proposed
tangent and chord equals the corresponding inscribed angle.
-/
def TangentChord (τ χ : Angle) : Prop :=
  τ = χ


/- ============================================================
   Elementary algebraic angle lemmas
   ============================================================ -/
