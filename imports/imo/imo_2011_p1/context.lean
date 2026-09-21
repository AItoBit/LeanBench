namespace IMO2011P1

/-- Sum of the four elements. -/
def total (a b c d : ℕ) : ℕ :=
  a + b + c + d

/-- `x,y` form a good pair when `x+y` divides the total. -/
def GoodPair
    (a b c d x y : ℕ) : Prop :=
  x + y ∣ total a b c d

/--
Explicit decidability instance.

This avoids instance-search problems when `GoodPair` appears
inside the indicator function below.
-/
instance instDecidableGoodPair
    (a b c d x y : ℕ) :
    Decidable (GoodPair a b c d x y) := by
  unfold GoodPair
  infer_instance

/-- Convert a proposition to `0` or `1`. -/
def indicator (P : Prop) [Decidable P] : ℕ :=
  if P then 1 else 0

/--
Number of good unordered pairs among

    (a,b), (a,c), (a,d),
    (b,c), (b,d), (c,d).
-/
def goodPairCount
    (a b c d : ℕ) : ℕ :=
  indicator (GoodPair a b c d a b) +
  indicator (GoodPair a b c d a c) +
  indicator (GoodPair a b c d a d) +
  indicator (GoodPair a b c d b c) +
  indicator (GoodPair a b c d b d) +
  indicator (GoodPair a b c d c d)

/-!
## Basic divisibility obstruction
-/
