/-- **IMO 2008 Problem 5**: the ratio `N / M` equals `2 ^ (k - n)`. -/
theorem candidate {n k : ℕ} (hn : 0 < n) (hk : n ≤ k) (he : Even (k - n)) :
    ((Nset n k).card : ℚ) / (Mset n k).card = 2 ^ (k - n) :=
