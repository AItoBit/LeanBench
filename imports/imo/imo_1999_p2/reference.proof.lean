by
  rw [show ∑ i, ∑ j ∈ Finset.Ioi i, x i * x j * (x i ^ 2 + x j ^ 2) = lhsSum x from rfl]
  have hsq : (∑ i, x i) ^ 2 = sumSq x + 2 * pairSum x := sq_sum_eq x
  have h4 : (∑ i, x i) ^ 4 = (sumSq x + 2 * pairSum x) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hTle : lhsSum x ≤ sumSq x * pairSum x := lhsSum_le_mul x hx
  constructor
  · intro heq
    rw [h4] at heq
    have hTPQ : lhsSum x = sumSq x * pairSum x := by
      nlinarith [sq_nonneg (sumSq x - 2 * pairSum x)]
    have hP2Q : sumSq x = 2 * pairSum x := by
      nlinarith [sq_nonneg (sumSq x - 2 * pairSum x)]
    obtain ⟨a, b, hab, hsupp⟩ := exists_pair_support hn x hx hTPQ
    refine ⟨a, b, hab, ?_, hsupp⟩
    have hs : ∑ k, x k = x a + x b := sum_of_support x hab hsupp
    have hp : sumSq x = x a ^ 2 + x b ^ 2 := sumSq_of_support x hab hsupp
    have h2P : 2 * sumSq x = (∑ i, x i) ^ 2 := by rw [hsq, hP2Q]; ring
    rw [hs, hp] at h2P
    nlinarith [sq_nonneg (x a - x b)]
  · rintro ⟨a, b, hab, hxab, hsupp⟩
    have hs : ∑ k, x k = x a + x b := sum_of_support x hab hsupp
    have hp : sumSq x = x a ^ 2 + x b ^ 2 := sumSq_of_support x hab hsupp
    have hP2Q : sumSq x = 2 * pairSum x := by
      have h := hsq
      rw [hs, hp] at h
      rw [hp]
      nlinarith [h, hxab]
    have hTPQ : lhsSum x = sumSq x * pairSum x :=
      lhsSum_eq_mul_of_support x hab hxab hsupp
    rw [h4, hTPQ, hP2Q]
    ring
