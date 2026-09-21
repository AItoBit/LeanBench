namespace IMO2003P1

open Finset

/-- The permitted shifts. -/
def S : Finset ℤ := Icc 1 1000000

/-- Translation of a finite set by an integer. -/
def translate (A : Finset ℤ) (x : ℤ) : Finset ℤ := A.image (fun a => a + x)

/-- All nonzero differences, together with zero. -/
def differences (A : Finset ℤ) : Finset ℤ :=
  insert 0 (A.offDiag.image (fun p => p.1 - p.2))

/-- The chosen translates are pairwise disjoint. -/
def Good (A T : Finset ℤ) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (translate A x) (translate A y)
