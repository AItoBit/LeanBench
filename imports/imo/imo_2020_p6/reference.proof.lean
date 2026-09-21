by

  obtain
    ⟨C,
     hC,
     hmain⟩ :=
    combine_cases
      Wide
      Cwide
      Cstrip
      hCwide
      hCstrip
      wide_case
      strip_packing_case

  refine
    ⟨C,
     hC,
     ?_⟩

  intro n S hn hcard hsep

  exact
    hmain
      n
      S
      hn
      hcard
      hsep

/-!
============================================================
12. Unpacking HasSeparatingLine
============================================================
-/
