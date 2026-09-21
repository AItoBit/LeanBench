open BigOperators

namespace IMO2017P6

noncomputable section

abbrev Poly := MvPolynomial (Fin 2) ℤ

def Primitive (p : ℤ × ℤ) : Prop :=
  Int.gcd p.1 p.2 = 1

def pointVal (p : ℤ × ℤ) : Fin 2 → ℤ
  | ⟨0, _⟩ => p.1
  | ⟨1, _⟩ => p.2

def X : Poly :=
  MvPolynomial.X 0

def Y : Poly :=
  MvPolynomial.X 1

def linearForm (p : ℤ × ℤ) : Poly :=
  MvPolynomial.C p.2 * X -
  MvPolynomial.C p.1 * Y

/--
The polynomial used in the PDF to vanish at one old point.
-/
def vanishAt (p : ℤ × ℤ) : Poly :=
  linearForm p

/--
Product of the linear factors corresponding to a finite set.
-/
def vanishProduct
    (S : Finset (ℤ × ℤ)) : Poly :=
  ∏ p ∈ S, vanishAt p
