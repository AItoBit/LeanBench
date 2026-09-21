private lemma infinite_sdiff_finite {α : Type*} {s t : Set α}
    (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := by
  intro hst
  apply hs
  apply (hst.union ht).subset
  intro x hx
  by_cases hxt : x ∈ t
  · exact Or.inr hxt
  · exact Or.inl ⟨hx, hxt⟩

private lemma two_primes_differ_at_high_bit (S : Set ℕ) (hS : S.Infinite)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k := by
  classical
  let U : Set ℕ := S \ {2}
  have hU : U.Infinite := infinite_sdiff_finite hS (Set.finite_singleton 2)
  let U₀ : Set ℕ := {x ∈ U | x.testBit 1 = false}
  let U₁ : Set ℕ := {x ∈ U | x.testBit 1 = true}
  have hUnion : U₀ ∪ U₁ = U := by
    ext x
    change ((x ∈ U ∧ x.testBit 1 = false) ∨
      (x ∈ U ∧ x.testBit 1 = true)) ↔ x ∈ U
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      cases hbit : x.testBit 1
      · exact Or.inl ⟨hx, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩
  have hInf : U₀.Infinite ∨ U₁.Infinite := by
    rw [← Set.infinite_union, hUnion]
    exact hU
  have auxiliary (T : Set ℕ) (hT : T.Infinite) (hTU : T ⊆ U)
      (c : Bool) (hc : ∀ x ∈ T, x.testBit 1 = c) :
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
        ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k := by
    obtain ⟨p, hpT⟩ := hT.nonempty
    have hT' : (T \ {p}).Infinite :=
      infinite_sdiff_finite hT (Set.finite_singleton p)
    obtain ⟨q, hqT, hqp⟩ := hT'.nonempty
    have hpU := hTU hpT
    have hqU := hTU hqT
    have hpS : p ∈ S := hpU.1
    have hqS : q ∈ S := hqU.1
    have hp2 : p ≠ 2 := by simpa [U] using hpU.2
    have hq2 : q ≠ 2 := by simpa [U] using hqU.2
    have hpq : p ≠ q := Ne.symm (by simpa using hqp)
    refine ⟨p, hpS, q, hqS, hpq, ?_⟩
    by_cases hex : ∃ k, 2 ≤ k ∧ p.testBit k ≠ q.testBit k
    · exact hex
    exfalso
    have hbits' : ∀ k, 2 ≤ k → p.testBit k = q.testBit k := by
      intro k hk
      by_contra hne
      exact hex ⟨k, hk, hne⟩
    have hpodd : Odd p := (hprime p hpS).odd_of_ne_two hp2
    have hqodd : Odd q := (hprime q hqS).odd_of_ne_two hq2
    have hbit0 : p.testBit 0 = q.testBit 0 := by
      have hpmod : p % 2 = 1 := by
        rcases hpodd with ⟨r, hr⟩
        omega
      have hqmod : q % 2 = 1 := by
        rcases hqodd with ⟨r, hr⟩
        omega
      have hpbit : p.testBit 0 = true :=
        Nat.mod_two_eq_one_iff_testBit_zero.mp hpmod
      have hqbit : q.testBit 0 = true :=
        Nat.mod_two_eq_one_iff_testBit_zero.mp hqmod
      exact hpbit.trans hqbit.symm
    have hbit1 : p.testBit 1 = q.testBit 1 :=
      (hc p hpT).trans (hc q hqT).symm
    have : p = q := Nat.eq_of_testBit_eq fun i => by
      by_cases hi0 : i = 0
      · simpa [hi0] using hbit0
      by_cases hi1 : i = 1
      · simpa [hi1] using hbit1
      exact hbits' i (by omega)
    exact hpq this
  rcases hInf with h₀ | h₁
  · exact auxiliary U₀ h₀ (fun _ hx => hx.1) false (fun _ hx => hx.2)
  · exact auxiliary U₁ h₁ (fun _ hx => hx.1) true (fun _ hx => hx.2)
