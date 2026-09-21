namespace IMO2001P3

open Finset

/-- The conditions on the problems the girls and boys solved, represented as functions from `Fin 21`
(index in cohort) to the finset of problems they solved (numbered arbitrarily). -/
structure Condition (G B : Fin 21 → Finset ℕ) where
  /-- Every girl solved at most six problems. -/
  G_le_6 (i) : #(G i) ≤ 6
  /-- Every boy solved at most six problems. -/
  B_le_6 (j) : #(B j) ≤ 6
  /-- Every girl-boy pair solved at least one problem in common. -/
  G_inter_B (i j) : ¬Disjoint (G i) (B j)

/-- A problem is easy for a cohort (boys or girls) if at least three of its members solved it. -/
def Easy (F : Fin 21 → Finset ℕ) (p : ℕ) : Prop := 3 ≤ #{i | p ∈ F i}

variable {G B : Fin 21 → Finset ℕ}

open scoped Classical in
/-- Every contestant solved at most five problems that were not easy for the other cohort. -/
lemma card_not_easy_le_five {i : Fin 21} (hG : #(G i) ≤ 6) (hB : ∀ j, ¬Disjoint (G i) (B j)) :
    #{p ∈ G i | ¬Easy B p} ≤ 5 := by
  by_contra! h
  replace h := le_antisymm (card_filter_le ..) (hG.trans h)
  simp_rw [card_filter_eq_iff, Easy, not_le] at h
  suffices 21 ≤ 12 by norm_num at this
  calc
    _ = #{j | ¬Disjoint (G i) (B j)} := by simp [filter_true_of_mem fun j _ ↦ hB j]
    _ = #((G i).biUnion fun p ↦ {j | p ∈ B j}) := by congr 1; ext j; simp [not_disjoint_iff]
    _ ≤ ∑ p ∈ G i, #{j | p ∈ B j} := card_biUnion_le
    _ ≤ ∑ p ∈ G i, 2 := sum_le_sum fun p mp ↦ Nat.le_of_lt_succ (h p mp)
    _ ≤ _ := by rw [sum_const, smul_eq_mul]; lia

open scoped Classical in
/-- There are at most 210 girl-boy pairs who solved some problem in common that was not easy for
a fixed cohort. -/
lemma card_not_easy_le_210 (hG : ∀ i, #(G i) ≤ 6) (hB : ∀ i j, ¬Disjoint (G i) (B j)) :
    #{ij : Fin 21 × Fin 21 | ∃ p, ¬Easy B p ∧ p ∈ G ij.1 ∩ B ij.2} ≤ 210 :=
  calc
    _ = ∑ i, #{j | ∃ p, ¬Easy B p ∧ p ∈ G i ∩ B j} := by
      simp_rw [card_filter, ← univ_product_univ, sum_product]
    _ = ∑ i, #({p ∈ G i | ¬Easy B p}.biUnion fun p ↦ {j | p ∈ B j}) := by
      congr!; ext
      simp_rw [mem_biUnion, mem_inter, mem_filter]
      congr! 2; tauto
    _ ≤ ∑ i, ∑ p ∈ G i with ¬Easy B p, #{j | p ∈ B j} := sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ ∑ i, ∑ p ∈ G i with ¬Easy B p, 2 := by
      gcongr with i _ p mp
      rw [mem_filter, Easy, not_le] at mp
      exact Nat.le_of_lt_succ mp.2
    _ ≤ ∑ i : Fin 21, 5 * 2 := by
      gcongr with i
      grw [sum_const, smul_eq_mul, card_not_easy_le_five (hG _) (hB _)]
    _ = _ := by norm_num

theorem result (h : Condition G B) : ∃ p, Easy G p ∧ Easy B p := by
  obtain ⟨G_le_6, B_le_6, G_inter_B⟩ := h
  have B_inter_G : ∀ i j, ¬Disjoint (B i) (G j) := by grind
  have cB := card_not_easy_le_210 G_le_6 G_inter_B
  have cG := card_not_easy_le_210 B_le_6 B_inter_G
  rw [← card_map ⟨_, Prod.swap_injective⟩] at cG
  have key := (card_union_le _ _).trans (add_le_add cB cG) |>.trans_lt
    (show _ < #(@univ (Fin 21 × Fin 21) _) by simp)
  obtain ⟨⟨i, j⟩, -, hij⟩ := exists_mem_notMem_of_card_lt_card key
  simp_rw [mem_union, mem_map, mem_filter_univ, Function.Embedding.coeFn_mk, Prod.exists,
    Prod.swap_prod_mk, Prod.mk.injEq, existsAndEq, true_and, and_true, not_or, not_exists,
    not_and', not_not, mem_inter, and_imp] at hij
  obtain ⟨p, pG, pB⟩ := not_disjoint_iff.mp (G_inter_B i j)
  use p, hij.2 _ pB pG, hij.1 _ pG pB
