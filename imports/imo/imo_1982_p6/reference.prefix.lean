namespace Imo1982P6

variable {P : Type*} [PseudoMetricSpace P]

/-- The length of the portion of the polygonal path `A` between indices `j` and
`k`. -/
noncomputable def plen (A : ℕ → P) (j k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico j k, dist (A i) (A (i + 1))

theorem plen_add (A : ℕ → P) {j m k : ℕ} (h1 : j ≤ m) (h2 : m ≤ k) :
    plen A j m + plen A m k = plen A j k :=
  Finset.sum_Ico_consecutive _ h1 h2

/-- A polygonal path is at least as long as the distance between its endpoints. -/
theorem dist_le_plen (A : ℕ → P) {j k : ℕ} (h : j ≤ k) :
    dist (A j) (A k) ≤ plen A j k := by
  induction k, h using Nat.le_induction with
  | base => simp [plen]
  | succ m hm ih =>
    have h1 : plen A j (m + 1) = plen A j m + dist (A m) (A (m + 1)) := by
      rw [plen, plen, Finset.sum_Ico_succ_top hm]
    calc dist (A j) (A (m + 1)) ≤ dist (A j) (A m) + dist (A m) (A (m + 1)) :=
          dist_triangle _ _ _
      _ ≤ plen A j m + dist (A m) (A (m + 1)) := by linarith
      _ = plen A j (m + 1) := h1.symm

/-- If `p` is within `1/2` of `Z`, `q` is within `1/2` of `B`, and `Z`, `B` are
at least `100` apart, then `p` and `q` are at least `99` apart. -/
private theorem far {p q Z B : P} (hp : dist p Z ≤ 1 / 2) (hq : dist q B ≤ 1 / 2)
    (h : 100 ≤ dist Z B) : 99 ≤ dist p q := by
  have t1 : dist Z B ≤ dist Z p + dist p B := dist_triangle _ _ _
  have t2 : dist p B ≤ dist p q + dist q B := dist_triangle _ _ _
  have e : dist Z p = dist p Z := dist_comm _ _
  linarith
