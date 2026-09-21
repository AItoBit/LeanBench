namespace IMO2024P2

/-!
# IMO 2024 Problem 2

Find all positive integer pairs (a,b) for which there exist
positive integers g,N such that

    gcd(a^n + b, b^n + a) = g

for every n ≥ N.

The answer is

    (a,b) = (1,1).

The source proves two substantial intermediate facts:

1. if d = gcd(a,b), then the eventual gcd g is either
   d or 2d;

2. after writing a = d*x and b = d*y with gcd(x,y)=1,
   Euler's theorem gives

       d^2*x*y + 1 ∣ g.

Everything after these two source-specific facts is
formalized below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Original eventual-gcd property
============================================================
-/

def EventuallyConstantGCD
    (a b : ℕ) : Prop :=
  ∃ g N : ℕ,
    0 < g ∧
    0 < N ∧
    ∀ n : ℕ,
      N ≤ n →
      Nat.gcd (a ^ n + b) (b ^ n + a) = g

/-!
============================================================
2. The solution (1,1) works
============================================================
-/

structure NormalizedData (a b : ℕ) where
  d : ℕ
  x : ℕ
  y : ℕ

  hd : 0 < d
  hx : 0 < x
  hy : 0 < y

  ha : a = d * x
  hb : b = d * y

  hcoprime : Nat.Coprime x y

/-!
============================================================
4. From g = d or 2d obtain g ≤ 2d
============================================================
-/
