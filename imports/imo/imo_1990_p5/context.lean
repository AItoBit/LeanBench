namespace IMO1990P5

/-- A chooses a number between `n` and `n²`. -/
def LegalA (n m : ℕ) : Prop :=
  n ≤ m ∧ m ≤ n ^ 2

/-- B divides by a positive power of a prime. -/
def LegalB (m k : ℕ) : Prop :=
  0 < k ∧
    ∃ p r : ℕ,
      Nat.Prime p ∧
      0 < r ∧
      m = k * p ^ r

/--
A has a well-founded winning strategy, with A to move.

Recursive occurrences are direct constructor arguments,
not nested inside conjunctions or disjunctions.
-/
inductive AWin : ℕ → Prop where
  | immediate {n : ℕ}
      (active : 1 < n)
      (legal : LegalA n 1990) :
      AWin n

  | step {n m : ℕ}
      (active : 1 < n)
      (legal : LegalA n m)
      (nonterminal : m ≠ 1990)
      (avoids_one :
        ∀ k : ℕ, LegalB m k → k ≠ 1)
      (continues :
        ∀ k : ℕ, LegalB m k → AWin k) :
      AWin n

/--
B has a well-founded winning strategy, with A to move.

`reply m` specifies B's response to A's choice `m`.
If the response is not 1, the strategy continues recursively.
-/
inductive BWin : ℕ → Prop where
  | step {n : ℕ}
      (active : 1 < n)
      (reply : ℕ → ℕ)
      (avoids_target :
        ∀ m : ℕ, LegalA n m → m ≠ 1990)
      (legal_reply :
        ∀ m : ℕ, LegalA n m → LegalB m (reply m))
      (continues :
        ∀ m : ℕ, LegalA n m →
          reply m ≠ 1 → BWin (reply m)) :
      BWin n

def Draw (n : ℕ) : Prop :=
  ¬ AWin n ∧ ¬ BWin n
