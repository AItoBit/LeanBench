/--
If the even case leads to a contradiction, then `n` is odd.
-/
theorem candidate
    {n : ℕ}
    (hevenImpossible :
      Even n → False) :
    Odd n :=
