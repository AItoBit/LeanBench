open Finset

namespace IMO1990P2

/-- No two selected vertices are consecutive in the cycle. -/
def StepFree {m : ℕ} (S : Finset (ZMod m)) : Prop :=
  ∀ x, x ∈ S → x + 1 ∉ S

/-- The injection sending `i` to `2i`. -/
def evenEmbedding (q : ℕ) :
    Fin q ↪ ZMod (2 * q + 1) where
  toFun i :=
    ((2 * i.1 : ℕ) : ZMod (2 * q + 1))
  inj' := by
    intro i j hij
    have hi : 2 * i.1 < 2 * q + 1 := by
      have hii := i.2
      omega
    have hj : 2 * j.1 < 2 * q + 1 := by
      have hjj := j.2
      omega
    have hv := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi] at hv
    rw [ZMod.val_natCast_of_lt hj] at hv
    apply Fin.ext
    omega

/-- The alternating set `{0, 2, ..., 2(q-1)}`. -/
def alternatingSet (q : ℕ) :
    Finset (ZMod (2 * q + 1)) :=
  Finset.univ.map (evenEmbedding q)

/-- Every selection of at least `k` vertices contains consecutive vertices. -/
def ForcesPairOddCycle (q k : ℕ) : Prop :=
  ∀ S : Finset (ZMod (2 * q + 1)),
    k ≤ S.card → ¬ StepFree S

/-- Independence in each of three disjoint cycles. -/
def ThreeStepFree
    {m : ℕ}
    (A B C : Finset (ZMod m)) : Prop :=
  StepFree A ∧ StepFree B ∧ StepFree C

def threeCard
    {m : ℕ}
    (A B C : Finset (ZMod m)) : ℕ :=
  A.card + B.card + C.card

def ForcesPairThreeCycles (q k : ℕ) : Prop :=
  ∀ A B C : Finset (ZMod (2 * q + 1)),
    k ≤ threeCard A B C →
    ¬ ThreeStepFree A B C

/-- The proposed numerical answer for the original problem. -/
def imoAnswer (n : ℕ) : ℕ :=
  if 3 ∣ 2 * n - 1 then n - 1 else n
