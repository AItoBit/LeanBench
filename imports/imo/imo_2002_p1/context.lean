namespace Imo2002P1

open Finset

/-- The triangular board `{(h,k) : h + k < n}`. -/
def board (n : ℕ) : Finset (ℕ × ℕ) :=
  (range n ×ˢ range n).filter fun p => p.1 + p.2 < n

/-- The blue cells of column `h`, recorded by their second coordinate. -/
def colB (n : ℕ) (R : Finset (ℕ × ℕ)) (h : ℕ) : Finset ℕ :=
  (range (n - h)).filter fun k => (h, k) ∉ R

/-- The blue cells of row `k`, recorded by their first coordinate. -/
def rowB (n : ℕ) (R : Finset (ℕ × ℕ)) (k : ℕ) : Finset ℕ :=
  (range (n - k)).filter fun h => (h, k) ∉ R

/-- Type 1 subsets: `n` blue cells with distinct first coordinates. -/
def Type1 (n : ℕ) (R : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (board n \ R).powerset.filter fun T => T.card = n ∧ (T.image Prod.fst).card = n

/-- Type 2 subsets: `n` blue cells with distinct second coordinates. -/
def Type2 (n : ℕ) (R : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (board n \ R).powerset.filter fun T => T.card = n ∧ (T.image Prod.snd).card = n

/-! ### Counting the two kinds of subset -/
