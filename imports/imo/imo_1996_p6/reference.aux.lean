/-- The heart of the problem, assuming `p` and `q` coprime. -/
theorem main (p q n : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : p + q < n)
    (hcop : Nat.Coprime p q) (x : ℕ → ℤ) (h0 : x 0 = 0) (hn : x n = 0)
    (hstep : ∀ i, i < n → x (i + 1) - x i = (p : ℤ) ∨ x (i + 1) - x i = -(q : ℤ)) :
    ∃ i, i + (p + q) ≤ n ∧ x i = x (i + (p + q)) := by
  classical
  set h : ℕ := p + q with hh
  have hhpos : 0 < h := by omega
  -- counting the two kinds of step
  obtain ⟨A, hAsub, hAmem⟩ : ∃ A : Finset ℕ, A ⊆ Finset.range n ∧
      ∀ i, i ∈ A ↔ (i ∈ Finset.range n ∧ x (i + 1) - x i = (p : ℤ)) :=
    ⟨(Finset.range n).filter (fun i => x (i + 1) - x i = (p : ℤ)),
      Finset.filter_subset _ _, fun i => Finset.mem_filter⟩
  have htel : ∑ i ∈ Finset.range n, (x (i + 1) - x i) = 0 := by
    rw [Finset.sum_range_sub, hn, h0, sub_zero]
  have hconst1 : ∀ i ∈ A, x (i + 1) - x i = (p : ℤ) := fun i hi => ((hAmem i).1 hi).2
  have hconst2 : ∀ i ∈ (Finset.range n) \ A, x (i + 1) - x i = -(q : ℤ) := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    rcases hstep i (Finset.mem_range.1 hi.1) with hstp | hstp
    · exact absurd ((hAmem i).2 ⟨hi.1, hstp⟩) hi.2
    · exact hstp
  have hsum1 : ∑ i ∈ A, (x (i + 1) - x i) = (A.card : ℤ) * p := by
    rw [Finset.sum_congr rfl hconst1, Finset.sum_const, nsmul_eq_mul]
  have hsum2 : ∑ i ∈ (Finset.range n) \ A, (x (i + 1) - x i)
      = (((Finset.range n) \ A).card : ℤ) * (-(q : ℤ)) := by
    rw [Finset.sum_congr rfl hconst2, Finset.sum_const, nsmul_eq_mul]
  have hsplit : ∑ i ∈ (Finset.range n) \ A, (x (i + 1) - x i) + ∑ i ∈ A, (x (i + 1) - x i)
      = ∑ i ∈ Finset.range n, (x (i + 1) - x i) := Finset.sum_sdiff hAsub
  have hcards : A.card + ((Finset.range n) \ A).card = n := by
    have hle := Finset.card_le_card hAsub
    rw [Finset.card_range] at hle
    rw [Finset.card_sdiff_of_subset hAsub, Finset.card_range]
    omega
  have hZ : (A.card : ℤ) * p = (((Finset.range n) \ A).card : ℤ) * q := by
    rw [hsum1, hsum2] at hsplit
    rw [htel] at hsplit
    linarith
  have hN : A.card * h = n * q := by
    have : (A.card : ℤ) * (h : ℤ) = (n : ℤ) * q := by
      have hc : ((A.card : ℤ)) + (((Finset.range n) \ A).card : ℤ) = (n : ℤ) := by
        exact_mod_cast hcards
      push_cast [hh]
      nlinarith [hZ, hc]
    exact_mod_cast this
  have hcop2 : Nat.Coprime h q := by
    have hg : Nat.gcd h q = Nat.gcd p q := by
      rw [Nat.gcd_comm h q, Nat.gcd_comm p q, hh]
      exact Nat.gcd_add_self_right q p
    rw [Nat.Coprime, hg]
    exact hcop
  have hdvd : h ∣ n := hcop2.dvd_of_dvd_mul_right ⟨A.card, by rw [← hN]; ring⟩
  obtain ⟨m, hm⟩ := hdvd
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m <;> omega
    · exact hge
  -- every step is `≡ p` modulo `h`
  have hcong : ∀ i k, i + k ≤ n → (h : ℤ) ∣ (x (i + k) - x i - (k : ℤ) * p) := by
    intro i k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hle
      have hk : i + k ≤ n := by omega
      have hlt : i + k < n := by omega
      have hd := ih hk
      have hre : x (i + (k + 1)) - x i - ((k : ℤ) + 1) * p
          = (x ((i + k) + 1) - x (i + k) - (p : ℤ)) + (x (i + k) - x i - (k : ℤ) * p) := by
        have hidx : i + (k + 1) = (i + k) + 1 := by omega
        rw [hidx]; ring
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring, hre]
      refine dvd_add ?_ hd
      rcases hstep (i + k) hlt with hs | hs
      · rw [hs]; simp
      · exact ⟨-1, by rw [hs, hh]; push_cast; ring⟩
  have hdvd_d : ∀ i, i + h ≤ n → (h : ℤ) ∣ (x (i + h) - x i) := by
    intro i hle
    have h1 := hcong i h hle
    have h2 : (h : ℤ) ∣ (h : ℤ) * p := Dvd.intro _ rfl
    have := dvd_add h1 h2
    simpa using this
  -- consecutive values of `d` differ by `0`, `h` or `-h`
  have hjump : ∀ i, i + h + 1 ≤ n →
      (x (i + 1 + h) - x (i + 1)) - (x (i + h) - x i) = 0 ∨
      (x (i + 1 + h) - x (i + 1)) - (x (i + h) - x i) = (h : ℤ) ∨
      (x (i + 1 + h) - x (i + 1)) - (x (i + h) - x i) = -(h : ℤ) := by
    intro i hle
    have e1 : i + 1 + h = (i + h) + 1 := by omega
    have hlt1 : i + h < n := by omega
    have hlt2 : i < n := by omega
    rw [e1]
    rcases hstep (i + h) hlt1 with s1 | s1 <;> rcases hstep i hlt2 with s2 | s2
    · left; linarith
    · right; left; rw [hh]; push_cast; linarith
    · right; right; rw [hh]; push_cast; linarith
    · left; linarith
  by_contra hcon
  push Not at hcon
  have hne : ∀ i, i + h ≤ n → x (i + h) - x i ≠ 0 := by
    intro i hle heq
    exact hcon i hle (by linarith)
  -- all the `d i` share a sign
  have hpos : ∀ i, i + h ≤ n → 0 < x (0 + h) - x 0 → 0 < x (i + h) - x i := by
    intro i
    induction i with
    | zero => intro _ hh0; exact hh0
    | succ i ih =>
      intro hle hh0
      have hle' : i + h ≤ n := by omega
      have hdi := ih hle' hh0
      have hge : (h : ℤ) ≤ x (i + h) - x i := Int.le_of_dvd hdi (hdvd_d i hle')
      rcases hjump i (by omega) with hj | hj | hj
      · linarith
      · linarith
      · have hnz := hne (i + 1) hle
        have : 0 ≤ x (i + 1 + h) - x (i + 1) := by linarith
        omega
  have hneg : ∀ i, i + h ≤ n → x (0 + h) - x 0 < 0 → x (i + h) - x i < 0 := by
    intro i
    induction i with
    | zero => intro _ hh0; exact hh0
    | succ i ih =>
      intro hle hh0
      have hle' : i + h ≤ n := by omega
      have hdi := ih hle' hh0
      have hge : (h : ℤ) ≤ -(x (i + h) - x i) :=
        Int.le_of_dvd (by linarith) ((dvd_neg).2 (hdvd_d i hle'))
      rcases hjump i (by omega) with hj | hj | hj
      · linarith
      · have hnz := hne (i + 1) hle
        have : x (i + 1 + h) - x (i + 1) ≤ 0 := by linarith
        omega
      · linarith
  -- the telescoping sum over the arithmetic progression
  have hprog : ∑ t ∈ Finset.range m, (x ((t + 1) * h) - x (t * h)) = 0 := by
    rw [Finset.sum_range_sub (fun t => x (t * h)) m]
    simp only [Nat.zero_mul]
    have h_mul : m * h = n := by rw [hm, Nat.mul_comm]
    rw [h_mul, hn, h0, sub_zero]
  have hterm : ∀ t ∈ Finset.range m, (t * h) + h ≤ n := by
    intro t ht
    rw [Finset.mem_range] at ht
    have h1 : t * h + h = (t + 1) * h := by ring
    have h2 : (t + 1) * h ≤ m * h := Nat.mul_le_mul_right h (by omega)
    rw [h1, hm, Nat.mul_comm h m]
    exact h2
  have hrw : ∀ t ∈ Finset.range m,
      x ((t + 1) * h) - x (t * h) = x ((t * h) + h) - x (t * h) := by
    intro t _
    rw [show (t + 1) * h = t * h + h by ring]
  rw [Finset.sum_congr rfl hrw] at hprog
  have h0ne := hne 0 (by omega)
  rcases lt_or_gt_of_ne h0ne with hlt | hgt
  · have : ∑ t ∈ Finset.range m, (x ((t * h) + h) - x (t * h)) < 0 := by
      refine Finset.sum_neg (fun t ht => hneg (t * h) (hterm t ht) hlt) ?_
      exact ⟨0, Finset.mem_range.2 (by omega)⟩
    omega
  · have : 0 < ∑ t ∈ Finset.range m, (x ((t * h) + h) - x (t * h)) := by
      refine Finset.sum_pos (fun t ht => hpos (t * h) (hterm t ht) hgt) ?_
      exact ⟨0, Finset.mem_range.2 (by omega)⟩
    omega
