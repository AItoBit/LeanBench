by
  classical
  rw [h₀]
  let leastPrime : ℕ → ℕ := fun n =>
    if h : n.primeFactors.Nonempty then n.primeFactors.min' h else 0
  let A : Set ℕ :=
    {n | 0 < n ∧ (leastPrime n).testBit n.primeFactors.card = true}
  refine ⟨A, ?_, ?_⟩
  · intro a ha
    exact ha.1
  · intro S hS
    rcases hS with ⟨hSinf, hprime⟩
    obtain ⟨p, hpS, q, hqS, hpq, k, hk, hbit⟩ :=
      two_primes_differ_at_high_bit S hSinf hprime
    have construct (r s : ℕ) (hrS : r ∈ S) (hsS : s ∈ S)
        (hrbit : r.testBit k = true) (hsbit : s.testBit k = false) :
        ∃ m ∈ A, ∃ n ∉ A, ∃ k' ≥ 2, 0 < m ∧ 0 < n ∧
          (∃ Sₘ : Finset ℕ, ↑Sₘ ⊆ S ∧ Sₘ.card = k' ∧
            ∏ x ∈ Sₘ, x = m) ∧
          ∃ Sₙ : Finset ℕ, ↑Sₙ ⊆ S ∧ Sₙ.card = k' ∧
            ∏ x ∈ Sₙ, x = n := by
      let V : Set ℕ := S \ Set.Iic (max r s)
      have hVinf : V.Infinite :=
        infinite_sdiff_finite hSinf (Set.finite_Iic (max r s))
      obtain ⟨R, hRV, hRcard⟩ := hVinf.exists_subset_card_eq (k - 1)
      have hRS : (R : Set ℕ) ⊆ S := fun x hx => (hRV hx).1
      have hRlarge {x : ℕ} (hx : x ∈ R) : max r s < x := by
        simpa using (hRV hx).2
      have hrR : r ∉ R := by
        intro hr
        have := hRlarge hr
        omega
      have hsR : s ∉ R := by
        intro hs
        have := hRlarge hs
        omega
      let Fₘ : Finset ℕ := insert r R
      let Fₙ : Finset ℕ := insert s R
      have hFmcard : Fₘ.card = k := by
        simp [Fₘ, hrR, hRcard]
        omega
      have hFncard : Fₙ.card = k := by
        simp [Fₙ, hsR, hRcard]
        omega
      have hFmS : (Fₘ : Set ℕ) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hrS
        · exact hRS hxR
      have hFnS : (Fₙ : Set ℕ) ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxR
        · exact hsS
        · exact hRS hxR
      have hFmprime : ∀ x ∈ Fₘ, Nat.Prime x := fun x hx => hprime x (hFmS hx)
      have hFnprime : ∀ x ∈ Fₙ, Nat.Prime x := fun x hx => hprime x (hFnS hx)
      let m : ℕ := ∏ x ∈ Fₘ, x
      let n : ℕ := ∏ x ∈ Fₙ, x
      have hmpos : 0 < m := by
        dsimp [m]
        exact Finset.prod_pos fun x hx => (hFmprime x hx).pos
      have hnpos : 0 < n := by
        dsimp [n]
        exact Finset.prod_pos fun x hx => (hFnprime x hx).pos
      have hmFactors : m.primeFactors = Fₘ := by
        dsimp [m]
        exact Nat.primeFactors_prod hFmprime
      have hnFactors : n.primeFactors = Fₙ := by
        dsimp [n]
        exact Nat.primeFactors_prod hFnprime
      have hFmne : Fₘ.Nonempty := ⟨r, by simp [Fₘ]⟩
      have hFnne : Fₙ.Nonempty := ⟨s, by simp [Fₙ]⟩
      have hFmmin : Fₘ.min' hFmne = r := by
        apply le_antisymm
        · exact Finset.min'_le Fₘ r (by simp [Fₘ])
        · apply Finset.le_min' Fₘ hFmne r
          intro x hx
          rcases Finset.mem_insert.mp (by simpa [Fₘ] using hx) with rfl | hxR
          · exact le_rfl
          · exact le_trans (le_max_left r s) (le_of_lt (hRlarge hxR))
      have hFnmin : Fₙ.min' hFnne = s := by
        apply le_antisymm
        · exact Finset.min'_le Fₙ s (by simp [Fₙ])
        · apply Finset.le_min' Fₙ hFnne s
          intro x hx
          rcases Finset.mem_insert.mp (by simpa [Fₙ] using hx) with rfl | hxR
          · exact le_rfl
          · exact le_trans (le_max_right r s) (le_of_lt (hRlarge hxR))
      have hmA : m ∈ A := by
        change 0 < m ∧ (leastPrime m).testBit m.primeFactors.card = true
        refine ⟨hmpos, ?_⟩
        simp only [leastPrime, hmFactors]
        simp [hFmne, hFmmin, hFmcard, hrbit]
      have hnA : n ∉ A := by
        intro hnA'
        have hb : (leastPrime n).testBit n.primeFactors.card = true := hnA'.2
        simp only [leastPrime, hnFactors] at hb
        simp [hFnne, hFnmin, hFncard, hsbit] at hb
      refine ⟨m, hmA, n, hnA, k, hk, hmpos, hnpos, ?_, ?_⟩
      · exact ⟨Fₘ, hFmS, hFmcard, rfl⟩
      · exact ⟨Fₙ, hFnS, hFncard, rfl⟩
    cases hpbit : p.testBit k <;> cases hqbit : q.testBit k
    · exact False.elim (hbit (hpbit.trans hqbit.symm))
    · exact construct q p hqS hpS hqbit hpbit
    · exact construct p q hpS hqS hpbit hqbit
    · exact False.elim (hbit (hpbit.trans hqbit.symm))
