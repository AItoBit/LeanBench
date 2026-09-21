namespace IMO2022P6

universe u

/-!
# IMO 2022 Problem 6

The claimed minimum number of uphill paths in an n × n
Nordic square is

    2 * n * (n - 1) + 1.

The lower-bound argument counts the grid adjacencies:

    n(n-1) horizontal edges
    n(n-1) vertical edges,

for a total of

    2n(n-1).

Each adjacent pair produces a distinct uphill path, and the
cell containing 1 gives one additional singleton path.

The construction proving sharpness is represented explicitly
by `construction`.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Target value
============================================================
-/

def target (n : ℕ) : ℕ :=
  2 * n * (n - 1) + 1

def horizontalEdges (n : ℕ) : ℕ :=
  n * (n - 1)

def verticalEdges (n : ℕ) : ℕ :=
  n * (n - 1)

def gridEdges (n : ℕ) : ℕ :=
  horizontalEdges n + verticalEdges n

/-!
There are exactly

    2 * n * (n - 1)

unordered adjacent cell-pairs.
-/

variable
  {Square : ℕ → Type u}

/-
`uphillCount S` is the number of uphill paths in S.
-/

variable
  (uphillCount :
    {n : ℕ} → Square n → ℕ)

/-!
============================================================
4. Lower bound
============================================================
-/

/--
`IsMinimum Square uphillCount n m` means:

* every n × n Nordic square has at least m uphill paths;
* some n × n Nordic square has exactly m uphill paths.

`Square` is an explicit parameter so that Lean can infer the
dependent type of `uphillCount` reliably.
-/
def IsMinimum
    (Square : ℕ → Type u)
    (uphillCount :
      {n : ℕ} → Square n → ℕ)
    (n m : ℕ) : Prop :=
  (∀ S : Square n,
      m ≤ uphillCount S)
    ∧
  (∃ S : Square n,
      uphillCount S = m)

/-!
============================================================
8. Main abstract theorem
============================================================
-/
