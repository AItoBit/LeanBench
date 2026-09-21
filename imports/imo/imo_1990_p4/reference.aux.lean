theorem two_mul_card_le_of_stepFree
    {m : ℕ} [NeZero m]
    (S : Finset (ZMod m))
    (hS : StepFree S) :
    2 * S.card ≤ m := by
  let f : ({x // x ∈ S} × Bool) → ZMod m :=
    fun p =>
      if p.2 then
        p.1.1 + 1
      else
        p.1.1

  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, ba⟩
    rcases b with ⟨⟨b, hb⟩, bb⟩
    cases ba <;> cases bb
    · simp [f] at hab
      subst b
      rfl
    · simp [f] at hab
      have hnot : b + 1 ∉ S := hS b hb
      have ha' : a ∈ S := ha
      rw [hab] at ha'
      exact (hnot ha').elim
    · simp [f] at hab
      have hnot : a + 1 ∉ S := hS a ha
      have hb' : b ∈ S := hb
      rw [← hab] at hb'
      exact (hnot hb').elim
    · simp [f] at hab
      subst b
      rfl

  have hcard :
      Fintype.card ({x // x ∈ S} × Bool) ≤
        Fintype.card (ZMod m) :=
    Fintype.card_le_of_injective f hf

  simpa [mul_comm] using hcard

theorem card_le_of_stepFree_oddCycle
    (q : ℕ)
    (S : Finset (ZMod (2 * q + 1)))
    (hS : StepFree S) :
    S.card ≤ q := by
  have hne : 2 * q + 1 ≠ 0 := by
    omega
  have h :=
    @two_mul_card_le_of_stepFree
      (2 * q + 1) ⟨hne⟩ S hS
  omega

@[simp]
theorem card_alternatingSet (q : ℕ) :
    (alternatingSet q).card = q := by
  simp [alternatingSet]

theorem alternatingSet_stepFree (q : ℕ) :
    StepFree (alternatingSet q) := by
  intro x hx hx1
  rw [alternatingSet] at hx hx1

  rcases Finset.mem_map.1 hx with ⟨i, _, hxi⟩
  rcases Finset.mem_map.1 hx1 with ⟨j, _, hxj⟩

  have hiq : i.1 < q := i.2
  have hjq : j.1 < q := j.2

  have h_even_j : 2 * j.1 < 2 * q + 1 := by
    omega
  have h_odd_i : 2 * i.1 + 1 < 2 * q + 1 := by
    omega

  have hxi' :
      x = ((2 * i.1 : ℕ) : ZMod (2 * q + 1)) := by
    simpa [evenEmbedding] using hxi.symm

  have hxj' :
      ((2 * j.1 : ℕ) : ZMod (2 * q + 1)) =
        x + 1 := by
    simpa [evenEmbedding] using hxj

  have hcast :
      ((2 * j.1 : ℕ) : ZMod (2 * q + 1)) =
        ((2 * i.1 + 1 : ℕ) : ZMod (2 * q + 1)) := by
    rw [hxi'] at hxj'
    simpa [Nat.cast_add] using hxj'

  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt h_even_j] at hv
  rw [ZMod.val_natCast_of_lt h_odd_i] at hv
  omega

/-- The maximum independent-set size in `C_(2q+1)` is `q`. -/
theorem oddCycle_independence_exact (q : ℕ) :
    (∀ S : Finset (ZMod (2 * q + 1)),
      StepFree S → S.card ≤ q) ∧
    (∃ S : Finset (ZMod (2 * q + 1)),
      StepFree S ∧ S.card = q) := by
  constructor
  · intro S hS
    exact card_le_of_stepFree_oddCycle q S hS
  · exact
      ⟨alternatingSet q,
        alternatingSet_stepFree q,
        card_alternatingSet q⟩

theorem oddCycle_threshold (q : ℕ) :
    ForcesPairOddCycle q (q + 1) := by
  intro S hcard hfree
  have hle := card_le_of_stepFree_oddCycle q S hfree
  omega

theorem oddCycle_threshold_is_sharp (q : ℕ) :
    ∃ S : Finset (ZMod (2 * q + 1)),
      S.card = q ∧ StepFree S := by
  exact
    ⟨alternatingSet q,
      card_alternatingSet q,
      alternatingSet_stepFree q⟩

theorem oddCycle_exact_minimum (q : ℕ) :
    IsLeast {k : ℕ | ForcesPairOddCycle q k} (q + 1) := by
  constructor
  · exact oddCycle_threshold q
  · intro k hk
    change ForcesPairOddCycle q k at hk
    obtain ⟨S, hcard, hfree⟩ :=
      oddCycle_threshold_is_sharp q
    by_contra hnot
    have hkq : k ≤ q := by
      omega
    exact hk S (by omega) hfree

theorem threeOddCycles_card_le
    (q : ℕ)
    (A B C : Finset (ZMod (2 * q + 1)))
    (h : ThreeStepFree A B C) :
    threeCard A B C ≤ 3 * q := by
  rcases h with ⟨hA, hB, hC⟩
  have hAc := card_le_of_stepFree_oddCycle q A hA
  have hBc := card_le_of_stepFree_oddCycle q B hB
  have hCc := card_le_of_stepFree_oddCycle q C hC
  unfold threeCard
  omega

theorem threeOddCycles_extremal (q : ℕ) :
    ∃ A B C : Finset (ZMod (2 * q + 1)),
      ThreeStepFree A B C ∧
      threeCard A B C = 3 * q := by
  refine
    ⟨alternatingSet q,
      alternatingSet q,
      alternatingSet q,
      ?_,
      ?_⟩
  · exact
      ⟨alternatingSet_stepFree q,
        alternatingSet_stepFree q,
        alternatingSet_stepFree q⟩
  · simp only [threeCard, card_alternatingSet]
    omega

theorem threeOddCycles_threshold (q : ℕ) :
    ForcesPairThreeCycles q (3 * q + 1) := by
  intro A B C hcard hfree
  have hle := threeOddCycles_card_le q A B C hfree
  omega

theorem threeOddCycles_threshold_is_sharp (q : ℕ) :
    ∃ A B C : Finset (ZMod (2 * q + 1)),
      threeCard A B C = 3 * q ∧
      ThreeStepFree A B C := by
  obtain ⟨A, B, C, hfree, hcard⟩ :=
    threeOddCycles_extremal q
  exact ⟨A, B, C, hcard, hfree⟩

theorem threeOddCycles_exact_minimum (q : ℕ) :
    IsLeast
      {k : ℕ | ForcesPairThreeCycles q k}
      (3 * q + 1) := by
  constructor
  · exact threeOddCycles_threshold q
  · intro k hk
    change ForcesPairThreeCycles q k at hk
    obtain ⟨A, B, C, hcard, hfree⟩ :=
      threeOddCycles_threshold_is_sharp q
    by_contra hnot
    have hkq : k ≤ 3 * q := by
      omega
    exact hk A B C (by omega) hfree

/-- The exact threshold for a single cycle of length `2n-1`. -/
theorem singleCycle_IMO_exact
    (n : ℕ)
    (hn : 1 ≤ n) :
    IsLeast
      {k : ℕ | ForcesPairOddCycle (n - 1) k}
      n := by
  have heq : n - 1 + 1 = n := by
    omega
  simpa only [heq] using oddCycle_exact_minimum (n - 1)

/-- The exact three-cycle threshold when `n = 3q+2`. -/
theorem threeCycle_IMO_exact
    (n q : ℕ)
    (hn : n = 3 * q + 2) :
    IsLeast
      {k : ℕ | ForcesPairThreeCycles q k}
      (n - 1) := by
  have heq : n - 1 = 3 * q + 1 := by
    omega
  rw [heq]
  exact threeOddCycles_exact_minimum q

theorem divisible_case_vertex_count
    {n q : ℕ}
    (hn : n = 3 * q + 2) :
    2 * n - 1 = 3 * (2 * q + 1) := by
  omega

theorem imoAnswer_divisible
    (n : ℕ)
    (h : 3 ∣ 2 * n - 1) :
    imoAnswer n = n - 1 := by
  simp [imoAnswer, h]

theorem imoAnswer_nondivisible
    (n : ℕ)
    (h : ¬ (3 ∣ 2 * n - 1)) :
    imoAnswer n = n := by
  simp [imoAnswer, h]
