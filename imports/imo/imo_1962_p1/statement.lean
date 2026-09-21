/-- **IMO 1962 Problem 1.** The smallest natural number whose last decimal digit is `6` and
which is multiplied by `4` when that final `6` is moved to the front is `153846`. -/
theorem candidate :
    IsLeast {n : ℕ | n % 10 = 6 ∧ Nat.ofDigits 10 ((Nat.digits 10 n).tail.concat 6) = 4 * n}
    153846 :=
