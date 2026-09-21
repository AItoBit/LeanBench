namespace IMO1987P3

theorem candidate
    (S_a S_x S_ax n k : ℝ)
    (h_CS : S_ax^2 ≤ S_a * S_x)
    (h_Sx : S_x = 1)
    (h_Sa : S_a ≤ n * (k - 1)^2)
    (hn : 0 ≤ n)
    (hk : 1 ≤ k)
    (h_Sax_nonneg : 0 ≤ S_ax) :
    S_ax ≤ Real.sqrt n * (k - 1) :=
