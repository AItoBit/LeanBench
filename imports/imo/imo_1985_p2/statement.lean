theorem candidate {α : Type*}
    (n k : ℤ)
    (h_coprime : Int.gcd n k = 1)
    (c : ℤ → α)
    (h_per : ∀ i : ℤ, c (i + n) = c i)
    (h1 : ∀ i : ℤ, c i = c (-i))
    (h2 : ∀ i : ℤ, c i = c (i - k) ∨ c i = c (k - i)) :
    ∀ i j : ℤ, c i = c j :=
