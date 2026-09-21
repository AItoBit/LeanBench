theorem candidate
    (w : Fin 100 → ℝ)
    (c : ℝ)
    (htotal :
      (∑ i : Fin 100, w i)
        ≤ (199 : ℝ) / 2)
    (hc :
      c ≤ 1 / 201)
    (hblocked :
      ∀ i : Fin 100,
        1 < w i + c) :
    False :=
