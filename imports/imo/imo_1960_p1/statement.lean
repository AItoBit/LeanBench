/--
Determine all three digit numbers $N$ which are divisible by $11$ and where $N/11$ is equal to
the sum of the squares of the digits of $N$.  The answer is $\{550, 803\}$.
-/
theorem candidate :
    {n : ℕ | (Nat.digits 10 n).length = 3 ∧ 11 ∣ n ∧
      ((Nat.digits 10 n).map (· ^ 2)).sum = (n / 11 : ℕ)} = {550, 803} :=
