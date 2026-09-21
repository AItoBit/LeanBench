namespace IMO2005P2

open Function

/-!  A kernel-checked formalization of IMO 2005, Problem 2.

The sequence is indexed from `1`, as in the statement; index `0` is ignored.
`Int.emod (a i) n` is the remainder of `a i` modulo `n`.
-/

private lemma small_modEq_eq {N : ℕ} {x y : ℤ}
    (hxy : x ≡ y [ZMOD N]) (hsmall : |y - x| < (N : ℤ)) : x = y := by
  have hdvd : (N : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp hxy
  have hsmall' : (y - x).natAbs < N := by
    have : ((y - x).natAbs : ℤ) < (N : ℤ) := by
      simpa only [Int.natCast_natAbs] using hsmall
    exact_mod_cast this
  have hz : y - x = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hsmall')
  omega
