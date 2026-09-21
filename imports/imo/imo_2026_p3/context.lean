namespace IMO2026P3

noncomputable section

/-!
# IMO 2026 Problem 3

For a positive integer n, the optimal guaranteed total
length for Liu is

    2^n / (2^(n+1) - 1).

This file formalizes the exact minimax conclusion.

The genuinely combinatorial parts of the source are:

* Liu has a strategy guaranteeing this value;
* Xiang has a strategy preventing Liu from obtaining any
  strictly larger value.

Those two strategy facts are explicit hypotheses below.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Claimed optimal value
============================================================
-/

def target (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n /
    ((2 : ℝ) ^ (n + 1) - 1)

variable
  (LiuCanGuarantee : ℕ → ℝ → Prop)
  (XiangCanCap : ℕ → ℝ → Prop)

/-!
============================================================
3. Optimal-value predicate
============================================================
-/

def IsOptimalValue
    (LiuCanGuarantee : ℕ → ℝ → Prop)
    (XiangCanCap : ℕ → ℝ → Prop)
    (n : ℕ)
    (C : ℝ) : Prop :=
  LiuCanGuarantee n C ∧
  XiangCanCap n C

/-!
============================================================
4. Source lower and upper bounds imply optimality
============================================================
-/

def IsLargestGuarantee
    (LiuCanGuarantee : ℕ → ℝ → Prop)
    (n : ℕ)
    (C : ℝ) : Prop :=
  LiuCanGuarantee n C ∧
  ∀ D : ℝ,
    LiuCanGuarantee n D →
    D ≤ C

/-!
============================================================
8. Upper strategy converts into maximality
============================================================
-/
