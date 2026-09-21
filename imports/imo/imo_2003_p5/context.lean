namespace IMO2003P5

open Finset

/-- Each unordered pair occurs once; diagonal terms would be zero. -/
def spread (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, |x j - x i|

def energy (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range n, ∑ i ∈ range j, (x j - x i) ^ 2

def weight (n i : ℕ) : ℝ := 2 * (i : ℝ) + 1 - n

def IsArithmetic (n : ℕ) (x : ℕ → ℝ) : Prop :=
  ∃ a d : ℝ, ∀ i < n, x i = a + (i : ℝ) * d
