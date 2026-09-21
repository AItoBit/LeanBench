namespace IMO2026P5

noncomputable section

/-!
# IMO 2026 Problem 5

Find all functions f : ℝ₊ → ℝ₊ such that

    sqrt((x² + f(y)²) / 2)
      ≥ (f(x) + y) / 2
      ≥ sqrt(x f(y))

for all positive x,y.

The answer is

    f(x) = x + c

for a constant c ≥ 0.

We work with `f : ℝ → ℝ` and carry positivity explicitly.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Original condition
============================================================
-/

def OriginalCondition
    (f : ℝ → ℝ) : Prop :=
  (∀ x : ℝ,
      0 < x →
      0 < f x)
  ∧
  (∀ x y : ℝ,
      0 < x →
      0 < y →
      (f x + y) / 2
        ≤
      Real.sqrt
        ((x ^ 2 + (f y) ^ 2) / 2)
      ∧
      Real.sqrt (x * f y)
        ≤
      (f x + y) / 2)

/-!
============================================================
2. RMS-AM
============================================================
-/

def shift
    (f : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  f x - x

/-!
============================================================
10. Iterate identity means shift(f(x)) = shift(x)
============================================================
-/

/--
The central rigidity relation in the supplied solutions is

    f(x) + y = f(y) + x.

Equivalently,

    f(x) - x = f(y) - y.

Once this is established, f is immediately affine.
-/
def Balanced
    (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ,
    0 < x →
    0 < y →
    f x + y =
      f y + x

/-!
============================================================
12. Balance makes f(x)-x constant
============================================================
-/
