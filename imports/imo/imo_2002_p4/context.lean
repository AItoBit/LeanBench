def sumAdj : List ℕ → ℕ
  | [] => 0
  | _ :: [] => 0
  | a :: b :: tail => a * b + sumAdj (b :: tail)

-- The last element of a list, given a default starting value

def lastElem (a : ℕ) : List ℕ → ℕ
  | [] => a
  | b :: tail => lastElem b tail

-- The core property of adjacent divisors used in the telescoping proof

def DivChain (n : ℕ) : List ℕ → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: tail => a * b + n * a ≤ n * b ∧ DivChain n (b :: tail)

-- Part 1: Any two divisors a < b of n satisfy the required chain inequality
