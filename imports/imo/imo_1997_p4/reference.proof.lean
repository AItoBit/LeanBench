by
  intro N
  refine ⟨2 ^ (N + 1), ?_, SM (2 ^ (N + 1)), silver_pow (N + 1)⟩
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
