by
  constructor
  · intro c hsym hn
    exact upper c hsym hn
  · intro m hm
    by_contra hcon
    rw [not_le] at hcon
    exact ex_nomono (hm ex ex_symm (by rw [ex_card]; omega))
