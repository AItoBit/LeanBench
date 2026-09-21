/--
If the successive gaps are all equal to one constant `d`,
then the sequence is arithmetic.
-/
lemma isArithmetic_of_constant_gap
    (s gap : ℕ → ℕ)
    (hgap :
      ∀ n : ℕ,
        s (n + 1) = s n + gap n)
    (d : ℕ)
    (hd :
      ∀ n : ℕ, gap n = d) :
    IsArithmetic s := by
  refine ⟨d, ?_⟩
  intro n
  rw [hgap n, hd n]

/--
If every gap is at most `M`, and a block of `m > 0` gaps has
the maximal possible sum `m * M`, then its first gap equals `M`.
-/
lemma first_eq_max_of_block
    (gap : ℕ → ℕ)
    (m M p : ℕ)
    (hupper :
      ∀ j : ℕ, gap j ≤ M)
    (hmpos : 0 < m)
    (hsum :
      ∑ j ∈ Finset.range m, gap (p + j) = m * M) :
    gap p = M := by

  have hle :
      gap p ≤ M :=
    hupper p

  by_contra hne

  have hlt :
      gap p < M := by
    omega

  have hzero :
      0 ∈ Finset.range m := by
    simp [hmpos]

  have hstrict :
      (∑ j ∈ Finset.range m, gap (p + j))
        <
      ∑ _j ∈ Finset.range m, M := by

    apply Finset.sum_lt_sum

    · intro j hj
      exact hupper (p + j)

    · refine ⟨0, hzero, ?_⟩
      simpa using hlt

  have hconst :
      (∑ _j ∈ Finset.range m, M) = m * M := by
    simp

  rw [hconst, hsum] at hstrict

  omega

/--
If every gap is at least `m`, and a block of `M > 0` gaps has
the minimal possible sum `M * m`, then its first gap equals `m`.
-/
lemma first_eq_min_of_block
    (gap : ℕ → ℕ)
    (m M p : ℕ)
    (hlower :
      ∀ j : ℕ, m ≤ gap j)
    (hMpos : 0 < M)
    (hsum :
      ∑ j ∈ Finset.range M, gap (p + j) = M * m) :
    gap p = m := by

  have hge :
      m ≤ gap p :=
    hlower p

  by_contra hne

  have hlt :
      m < gap p := by
    omega

  have hzero :
      0 ∈ Finset.range M := by
    simp [hMpos]

  have hstrict :
      (∑ _j ∈ Finset.range M, m)
        <
      ∑ j ∈ Finset.range M, gap (p + j) := by

    apply Finset.sum_lt_sum

    · intro j hj
      exact hlower (p + j)

    · refine ⟨0, hzero, ?_⟩
      simpa using hlt

  have hconst :
      (∑ _j ∈ Finset.range M, m) = M * m := by
    simp

  rw [hconst, hsum] at hstrict

  omega

/--
The extremal step.

At an index `imin`, a block of `m` gaps has total `m*M`.
Since every gap is at most `M`, its first gap is therefore `M`.

At an index `imax`, a block of `M` gaps has total `M*m`.
Since every gap is at least `m`, its first gap is therefore `m`.

If the gaps at all positions `s i` are equal, these two values coincide,
and hence `m = M`.
-/
lemma min_eq_max
    (s gap : ℕ → ℕ)
    (m M imin imax : ℕ)
    (hmpos : 0 < m)
    (hMpos : 0 < M)
    (hlower :
      ∀ n : ℕ, m ≤ gap n)
    (hupper :
      ∀ n : ℕ, gap n ≤ M)
    (hminBlock :
      ∑ j ∈ Finset.range m,
          gap (s imin + j) =
        m * M)
    (hmaxBlock :
      ∑ j ∈ Finset.range M,
          gap (s imax + j) =
        M * m)
    (himageConstant :
      ∀ i j : ℕ,
        gap (s i) = gap (s j)) :
    m = M := by

  have hAtMin :
      gap (s imin) = M := by
    exact
      first_eq_max_of_block
        gap m M (s imin)
        hupper hmpos hminBlock

  have hAtMax :
      gap (s imax) = m := by
    exact
      first_eq_min_of_block
        gap m M (s imax)
        hlower hMpos hmaxBlock

  calc
    m = gap (s imax) := hAtMax.symm
    _ = gap (s imin) := himageConstant imax imin
    _ = M := hAtMin

/--
If every gap is between `m` and `M`, and `m = M`,
then every gap equals `m`.
-/
lemma constant_gap_of_min_eq_max
    (gap : ℕ → ℕ)
    (m M : ℕ)
    (hlower :
      ∀ n : ℕ, m ≤ gap n)
    (hupper :
      ∀ n : ℕ, gap n ≤ M)
    (hEq : m = M) :
    ∀ n : ℕ, gap n = m := by

  intro n

  have h₁ :
      m ≤ gap n :=
    hlower n

  have h₂ :
      gap n ≤ m := by
    calc
      gap n ≤ M := hupper n
      _ = m := hEq.symm

  omega
