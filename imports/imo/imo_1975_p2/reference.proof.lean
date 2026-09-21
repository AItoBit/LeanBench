by
  clear hp
  have hap : 0 < a p := hpos p
  -- Pigeonhole: infinitely many terms with index `> p` share the same residue mod `a p`.
  set f : ℕ → Fin (a p) := fun n => ⟨a (p + 1 + n) % a p, Nat.mod_lt _ hap⟩ with hf
  obtain ⟨r, hr⟩ := Finite.exists_infinite_fiber f
  have hS : (f ⁻¹' {r}).Infinite := Set.infinite_coe_iff.mp hr
  obtain ⟨n₀, hn₀⟩ := hS.nonempty
  -- `q` is the index of a fixed term in this residue class.
  set q : ℕ := p + 1 + n₀ with hq
  have hpq : p < q := by omega
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hnS, hn⟩ := hS.exists_gt (max n₀ N)
  refine ⟨p + 1 + n, ?_, by omega⟩
  have hmod : a (p + 1 + n) % a p = a q % a p := by
    have h1 : f n = r := hnS
    have h2 : f n₀ = r := hn₀
    have := h1.trans h2.symm
    simpa [hf, Fin.ext_iff, hq] using this
  have hlt : a q < a (p + 1 + n) := hmono (by omega)
  -- The difference is a positive multiple of `a p`.
  have hdvd : a p ∣ a (p + 1 + n) - a q :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  obtain ⟨x, hx⟩ := hdvd
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h, Nat.mul_zero] at hx; omega
    · exact h
  exact ⟨x, 1, q, hxpos, Nat.one_pos, hpq, by rw [Nat.mul_comm] at hx; omega⟩
