/-- **IMO 1975, Problem 4.**  Let `A` be the sum of the decimal digits of `4444 ^ 4444`,
and `B` the sum of the digits of `A`.  Then the sum of the digits of `B` equals `7`. -/
theorem candidate :
    digitSum (digitSum (digitSum (4444 ^ 4444))) = 7 :=
