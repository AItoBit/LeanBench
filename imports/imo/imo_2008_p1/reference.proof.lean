by
  rcases hp with ⟨t, h1, h2, hd⟩ | ⟨t, h1, h2, hd⟩ | ⟨t, h1, h2, hd⟩
  · rw [h1, h2]
    linarith [key a1 a2 b1 b2 c1 c2 R t hA hB hC hd]
  · rw [h1, h2]
    linarith [key b1 b2 c1 c2 a1 a2 R t hB hC hA hd]
  · rw [h1, h2]
    linarith [key c1 c2 a1 a2 b1 b2 R t hC hA hB hd]
