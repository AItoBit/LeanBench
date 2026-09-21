theorem candidate (n : ℕ) (l : List ℕ)
    (h_last : lastElem 1 l = n)
    (h_div : DivChain n (1 :: l))
    (hn : 1 < n) :
    sumAdj (1 :: l) < n^2 :=
