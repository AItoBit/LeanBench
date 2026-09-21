by

  obtain ⟨ms, hlen, hpos, hprod⟩ :=
    imo2013_p1
      k
      n
      hk
      hn

  refine
    ⟨ms, hlen, hpos, ?_⟩

  change
    (ms.map factor).prod =
      target k n

  exact hprod
