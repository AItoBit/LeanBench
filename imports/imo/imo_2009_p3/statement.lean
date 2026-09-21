/--
Final assembly of the extremal argument for IMO 2009 Problem 3.

The hypotheses `hminBlock`, `hmaxBlock`, and `himageConstant`
encode the consequences of the two arithmetic-progression hypotheses
used by the olympiad proof.
-/
theorem candidate
    (s gap : ℕ → ℕ)
    (m M imin imax : ℕ)
    (hgap :
      ∀ n : ℕ,
        s (n + 1) = s n + gap n)
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
    IsArithmetic s :=
