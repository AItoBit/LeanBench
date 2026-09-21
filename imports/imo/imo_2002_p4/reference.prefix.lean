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

lemma divisor_pair_ineq {a b n ca cb : ℕ}
    (ha : n = a * ca) (hb : n = b * cb) (hab : a < b) (hn : 0 < n) :
    a * b + n * a ≤ n * b := by
  have hcb : 0 < cb := by
    cases cb with
    | zero => 
      simp at hb
      omega
    | succ _ => 
      exact Nat.zero_lt_succ _
  have H : cb < ca := by
    have h1 : a * cb < b * cb := Nat.mul_lt_mul_of_pos_right hab hcb
    have h2 : b * cb = a * ca := by omega
    have h3 : a * cb < a * ca := by omega
    exact Nat.lt_of_mul_lt_mul_left h3
  calc
    a * b + n * a = a * b + (b * cb) * a := by rw [hb]
    _ = b * (a * (1 + cb)) := by ring
    _ ≤ b * (a * ca) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      omega
    _ = b * n := by rw [← ha]
    _ = n * b := by ring

-- Part 2: Any sequence satisfying the chain inequality yields the sum bound

lemma sumAdj_bound (n : ℕ) :
    ∀ (l : List ℕ) (a : ℕ),
    DivChain n (a :: l) →
    sumAdj (a :: l) + n * a ≤ n * lastElem a l
  | [], a, hDiv => by
    change 0 + n * a ≤ n * a
    omega
  | b :: tail, a, hDiv => by
    have h1 : a * b + n * a ≤ n * b := hDiv.1
    have h2 : DivChain n (b :: tail) := hDiv.2
    have ih := sumAdj_bound n tail b h2
    change a * b + sumAdj (b :: tail) + n * a ≤ n * lastElem b tail
    omega

-- Part 3: The IMO 2002 Problem 4 main result
