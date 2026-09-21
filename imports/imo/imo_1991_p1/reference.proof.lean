by
  have hs : a + b + c ≠ 0 := by
    positivity

  have hid :
      ((b + c) / (a + b + c)) *
        ((c + a) / (a + b + c)) *
        ((a + b) / (a + b + c)) =
      ((a + b) * (b + c) * (c + a)) /
        (a + b + c) ^ 3 := by
    field_simp [hs] <;> ring

  rw [hid]
  exact side_length_inequality a b c ha hb hc hA hB hC
