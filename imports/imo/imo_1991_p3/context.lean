namespace IMO1991P3

set_option maxHeartbeats 0

set_option maxRecDepth 100000

def domain : Finset ℕ := Finset.Icc 1 280

def PairwiseCoprime (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

def HasFive (S : Finset ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ T.card = 5 ∧ PairwiseCoprime T

/-- Every subset of exactly `k` elements has the required five numbers. -/
def ForcesFive (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ domain → S.card = k → HasFive S

/-- Nine explicit lists of pairwise coprime numbers to allow computational reduction. -/
def blockLists (i : Fin 9) : List ℕ :=
  match i.val with
  | 0 => [1, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277]
  | 1 => [121, 49, 25, 9, 4]
  | 2 => [143, 119, 95, 27, 8]
  | 3 => [169, 77, 85, 57, 16]
  | 4 => [187, 91, 115, 81, 32]
  | 5 => [209, 161, 65, 51, 58]
  | 6 => [221, 133, 55, 69, 62]
  | 7 => [247, 203, 125, 33, 34]
  | _ => [253, 217, 145, 39, 38]

/-- Convert the explicit lists to Finsets for subset logic. -/
def blocks (i : Fin 9) : Finset ℕ := (blockLists i).toFinset

def covered : Finset ℕ := Finset.univ.biUnion blocks

def remainder : Finset ℕ := domain \ covered

/-- Computable boolean checker for pairwise coprimality using lists. -/
def checkPairwiseCoprimeList (L : List ℕ) : Bool :=
  L.all fun a => L.all fun b => (a == b) || (Nat.gcd a b == 1)

/-- The extremal set: all multiples of 2, 3, 5, or 7 in the interval. -/
def bad : Finset ℕ :=
  domain.filter (fun n => n % 2 = 0 ∨ n % 3 = 0 ∨ n % 5 = 0 ∨ n % 7 = 0)

def color (n : ℕ) : Fin 4 :=
  if n % 2 = 0 then 0 else if n % 3 = 0 then 1 else if n % 5 = 0 then 2 else 3

def factor (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | _ => 7
