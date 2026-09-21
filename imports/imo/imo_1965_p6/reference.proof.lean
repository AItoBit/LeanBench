by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hS
    rcases le_or_gt (pairCount S d) (2 * S.card) with hle | hcon
    · exact hle
    · exfalso
      obtain ⟨P, hPS, hP3⟩ := exists_deg_three hcon
      obtain ⟨Q, hQS, hPQ, hQ1⟩ := geom S hS P hPS hP3
      have hcard : 1 ≤ S.card := Finset.card_pos.mpr ⟨Q, hQS⟩
      have hsub : S.erase Q ⊂ S := Finset.erase_ssubset hQS
      have hrec : pairCount (S.erase Q) d ≤ 2 * (S.erase Q).card :=
        ih _ hsub fun x hx y hy =>
          hS x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
      have hsplit := pairCount_erase S hd hQS
      rw [hQ1] at hsplit
      rw [Finset.card_erase_of_mem hQS] at hrec
      omega
