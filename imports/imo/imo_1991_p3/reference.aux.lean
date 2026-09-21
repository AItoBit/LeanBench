theorem checkPairwiseCoprimeList_iff (L : List ℕ) :
    checkPairwiseCoprimeList L = true ↔ ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Nat.Coprime a b := by
  simp only [checkPairwiseCoprimeList, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro h a ha b hb hab
    rcases h a ha b hb with h' | h'
    · exact False.elim (hab h')
    · exact h'
  · intro h a ha b hb
    by_cases hab : a = b
    · exact Or.inl hab
    · exact Or.inr (h a ha b hb hab)

/-- These numerical certificates use kernel reduction natively and computably. -/
theorem blocks_pairwise (i : Fin 9) : PairwiseCoprime (blocks i) := by
  have h : PairwiseCoprime (blocks i) ↔ checkPairwiseCoprimeList (blockLists i) = true := by
    rw [checkPairwiseCoprimeList_iff]
    unfold PairwiseCoprime blocks
    simp only [List.mem_toFinset]
  rw [h]
  fin_cases i <;> decide

theorem remainder_card : remainder.card = 180 := by
  decide

private theorem card_union_family_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset ℕ) :
    (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_left ih _)

private theorem intersection_card_le_four
    (S : Finset ℕ) (hno : ¬ HasFive S) (i : Fin 9) :
    (S ∩ blocks i).card ≤ 4 := by
  by_contra h
  have hfive : 5 ≤ (S ∩ blocks i).card := by omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hfive
  apply hno
  refine ⟨T, ?_, hcard, ?_⟩
  · intro x hx
    exact (Finset.mem_inter.mp (hT hx)).1
  · intro a ha b hb hab
    exact blocks_pairwise i a
      (Finset.mem_inter.mp (hT ha)).2 b
      (Finset.mem_inter.mp (hT hb)).2 hab

/-- The upper bound for every subset with no five pairwise coprime elements. -/
theorem card_le_216_of_no_five
    (S : Finset ℕ) (hS : S ⊆ domain)
    (hno : ¬ HasFive S) :
    S.card ≤ 216 := by
  have hcover :
      S ⊆ remainder ∪
        Finset.univ.biUnion (fun i : Fin 9 => S ∩ blocks i) := by
    intro x hx
    by_cases hc : x ∈ covered
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hc
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_sdiff.mpr ⟨hS hx, hc⟩

  have hsum :
      (∑ i : Fin 9, (S ∩ blocks i).card) ≤ 36 := by
    calc
      (∑ i : Fin 9, (S ∩ blocks i).card) ≤
          ∑ _i : Fin 9, (4 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact intersection_card_le_four S hno i
      _ = 36 := by simp

  have hfamily :
      (Finset.univ.biUnion
        (fun i : Fin 9 => S ∩ blocks i)).card ≤ 36 :=
    le_trans (card_union_family_le Finset.univ
      (fun i : Fin 9 => S ∩ blocks i)) hsum

  have hcard := Finset.card_le_card hcover
  have hunion := Finset.card_union_le remainder
    (Finset.univ.biUnion (fun i : Fin 9 => S ∩ blocks i))
  rw [remainder_card] at hunion
  omega

theorem every_217_subset : ForcesFive 217 := by
  intro S hS hcard
  by_contra hno
  have h := card_le_216_of_no_five S hS hno
  omega

theorem bad_card : bad.card = 216 := by
  decide

theorem bad_subset : bad ⊆ domain := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

private theorem factor_ge_two (i : Fin 4) : 2 ≤ factor i := by
  fin_cases i <;> decide

private theorem factor_dvd (n : ℕ) (hn : n ∈ bad) :
    factor (color n) ∣ n := by
  have h : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 5 = 0 ∨ n % 7 = 0 :=
    (Finset.mem_filter.mp hn).2
  by_cases h2 : n % 2 = 0
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
    simpa [color, factor, h2]
  · by_cases h3 : n % 3 = 0
    · have : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
      simpa [color, factor, h2, h3]
    · by_cases h5 : n % 5 = 0
      · have : 5 ∣ n := Nat.dvd_of_mod_eq_zero h5
        simpa [color, factor, h2, h3, h5]
      · have h7 : n % 7 = 0 := by tauto
        have : 7 ∣ n := Nat.dvd_of_mod_eq_zero h7
        simpa [color, factor, h2, h3, h5]

/-- Pairwise coprime subsets of the extremal set have at most four elements. -/
theorem bad_pairwise_card_le_four
    (T : Finset ℕ) (hT : T ⊆ bad) (hcop : PairwiseCoprime T) :
    T.card ≤ 4 := by
  let f : {x // x ∈ T} → Fin 4 := fun x => color x.val
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have heq : color a.val = color b.val := hab
    have ha : factor (color a.val) ∣ a.val :=
      factor_dvd a.val (hT a.property)
    have hb : factor (color a.val) ∣ b.val := by
      rw [heq]
      exact factor_dvd b.val (hT b.property)
    have hg : factor (color a.val) ∣ Nat.gcd a.val b.val :=
      Nat.dvd_gcd ha hb
    have hc : Nat.gcd a.val b.val = 1 :=
      hcop a.val a.property b.val b.property hne
    rw [hc] at hg
    have hle : factor (color a.val) ≤ 1 :=
      Nat.le_of_dvd (by decide) hg
    have hge := factor_ge_two (color a.val)
    omega
  have hcard := Fintype.card_le_of_injective f hf
  simpa using hcard

theorem bad_has_no_five : ¬ HasFive bad := by
  rintro ⟨T, hT, hcard, hcop⟩
  have h := bad_pairwise_card_le_four T hT hcop
  omega
