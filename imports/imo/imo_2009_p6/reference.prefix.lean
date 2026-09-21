open scoped BigOperators

open scoped Classical

set_option maxHeartbeats 1000000

/-!
# IMO 2009, Problem 6 (the grasshopper problem)

Let `a₁, a₂, …, aₙ` be distinct positive integers and let `M` be a set of `n - 1` positive
integers not containing `s = a₁ + a₂ + ⋯ + aₙ`.  A grasshopper is to jump along the real axis,
starting at the point `0` and making `n` jumps to the right with lengths `a₁, a₂, …, aₙ` in some
order.  Prove that the order can be chosen in such a way that the grasshopper never lands on any
point in `M`.

The jump lengths are modelled by a list `l : List ℕ` of distinct positive integers, and choosing
an order means choosing a permutation `l'` of `l`.  The points the grasshopper visits are the
partial sums `(l'.take k).sum` for `k ≥ 1`.
-/

namespace IMO2009P6

open List

/-- `SafeFrom M p l` says that a grasshopper standing at the point `p` and performing the jumps
of `l` in order never lands on a point of `M`; if `l` is empty this asserts that `p` itself is
not in `M`. -/
def SafeFrom (M : Finset ℕ) : ℕ → List ℕ → Prop
  | p, [] => p ∉ M
  | p, a :: t => p + a ∉ M ∧ SafeFrom M (p + a) t

@[simp] lemma safeFrom_nil (M : Finset ℕ) (p : ℕ) : SafeFrom M p [] ↔ p ∉ M := Iff.rfl

@[simp] lemma safeFrom_cons (M : Finset ℕ) (p a : ℕ) (t : List ℕ) :
    SafeFrom M p (a :: t) ↔ p + a ∉ M ∧ SafeFrom M (p + a) t := Iff.rfl

/-- If every obstacle lies strictly below the current position, the grasshopper is safe
whatever it does (all its future positions are at least the current one). -/
lemma safeFrom_of_all_lt (M : Finset ℕ) :
    ∀ (l : List ℕ) (p : ℕ), (∀ z ∈ M, z < p) → (∀ x ∈ l, 0 < x) → SafeFrom M p l := by
  intro l
  induction l with
  | nil => intro p h _; exact fun hp => absurd (h p hp) (lt_irrefl p)
  | cons b v ih =>
      intro p h hposl
      have hb : 0 < b := hposl b (List.mem_cons_self ..)
      refine ⟨fun hmem => absurd (h _ hmem) (by omega), ?_⟩
      exact ih (p + b) (fun z hz => by have := h z hz; omega)
        (fun x hx => hposl x (List.mem_cons_of_mem _ hx))

/-- Being safe for `M.erase m` is the same as being safe for `M` once we are past `m`. -/
lemma safeFrom_of_erase (M : Finset ℕ) (m : ℕ) :
    ∀ (t : List ℕ) (q : ℕ), m < q → (∀ x ∈ t, 0 < x) →
      SafeFrom (M.erase m) q t → SafeFrom M q t := by
  intro t
  induction t with
  | nil =>
      intro q hq _ h
      simp only [safeFrom_nil] at h ⊢
      intro hmem
      exact h (Finset.mem_erase.2 ⟨by omega, hmem⟩)
  | cons b v ih =>
      intro q hq hposl h
      have hb : 0 < b := hposl b (List.mem_cons_self ..)
      obtain ⟨h1, h2⟩ := h
      refine ⟨fun hmem => h1 (Finset.mem_erase.2 ⟨by omega, hmem⟩), ?_⟩
      exact ih (q + b) (by omega) (fun x hx => hposl x (List.mem_cons_of_mem _ hx)) h2

/-- Safety in terms of partial sums. -/
lemma safeFrom_take (M : Finset ℕ) :
    ∀ (l : List ℕ) (p : ℕ), SafeFrom M p l → ∀ k, 0 < k → p + (l.take k).sum ∉ M := by
  intro l
  induction l with
  | nil => intro p h k _; simpa using h
  | cons b v ih =>
      intro p h k hk
      obtain ⟨h1, h2⟩ := h
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using h1
      · have := ih (p + b) h2 j hj
        simpa [List.take_succ_cons, ← Nat.add_assoc] using this

/-- **Repair lemma.**  Suppose the grasshopper at `q` plans to jump `a` first and then the jumps
of `t` (all of which are smaller than `a`), and that this plan avoids all obstacles except
possibly the obstacle `m₁`, below which there is no obstacle above `q`.  Then the plan can be
repaired: if the plan does land on `m₁`, the jump `a` is delayed by one step. -/
lemma repair (M : Finset ℕ) (m₁ a : ℕ) :
    ∀ (t : List ℕ) (q : ℕ), (∀ x ∈ t, 0 < x ∧ x < a) →
      (∀ z ∈ M, z ≤ q ∨ m₁ ≤ z) → SafeFrom (M.erase m₁) q (a :: t) →
      q + a + t.sum ∉ M → ∃ t', t' ~ a :: t ∧ SafeFrom M q t' := by
  intro t
  induction t with
  | nil =>
      intro q _ _ _ hfinal
      exact ⟨[a], List.Perm.refl _, by simpa using hfinal, by simpa using hfinal⟩
  | cons b v ih =>
      intro q hlt hgap hsafe hfinal
      obtain ⟨h1, h3, h4⟩ := hsafe
      obtain ⟨hb0, hba⟩ : 0 < b ∧ b < a := hlt b (List.mem_cons_self ..)
      have hvpos : ∀ x ∈ v, 0 < x ∧ x < a := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
      have hvpos' : ∀ x ∈ v, 0 < x := fun x hx => (hvpos x hx).1
      rcases lt_trichotomy (q + a) m₁ with hcase | hcase | hcase
      · -- `m₁` is still ahead:  jump `b` now and keep `a` in reserve
        have hqb : q + b ∉ M := by
          intro hmem; rcases hgap _ hmem with h | h <;> omega
        have hsafe' : SafeFrom (M.erase m₁) (q + b) (a :: v) := by
          refine ⟨?_, ?_⟩
          · rw [show q + b + a = q + a + b by omega]; exact h3
          · rw [show q + b + a = q + a + b by omega]; exact h4
        have hfinal' : q + b + a + v.sum ∉ M := by
          rw [show q + b + a + v.sum = q + a + (b :: v).sum by simp; omega]; exact hfinal
        obtain ⟨t', hperm, hs⟩ := ih (q + b) hvpos
          (fun z hz => by
            rcases hgap z hz with h | h
            exacts [Or.inl (by omega), Or.inr h])
          hsafe' hfinal'
        exact ⟨b :: t', (hperm.cons b).trans (List.Perm.swap a b v), hqb, hs⟩
      · -- the plan lands on `m₁`:  swap the jumps `a` and `b`
        have hqb : q + b ∉ M := by
          intro hmem; rcases hgap _ hmem with h | h <;> omega
        have hab : q + b + a ∉ M := by
          rw [show q + b + a = q + a + b by omega]
          intro hmem; exact h3 (Finset.mem_erase.2 ⟨by omega, hmem⟩)
        refine ⟨b :: a :: v, List.Perm.swap a b v, hqb, hab, ?_⟩
        refine safeFrom_of_erase M m₁ v (q + b + a) (by omega) hvpos' ?_
        rw [show q + b + a = q + a + b by omega]; exact h4
      · -- the plan is already past `m₁`, so it is safe
        refine ⟨a :: b :: v, List.Perm.refl _, ?_, ?_⟩
        · intro hmem; exact h1 (Finset.mem_erase.2 ⟨by omega, hmem⟩)
        · exact safeFrom_of_erase M m₁ (b :: v) (q + a) hcase
            (fun x hx => by rcases List.mem_cons.1 hx with rfl | hx
                            · exact hb0
                            · exact hvpos' x hx) ⟨h3, h4⟩

/-- Every nonempty list of naturals has a greatest element. -/
lemma exists_max_mem : ∀ (l : List ℕ), l ≠ [] → ∃ a ∈ l, ∀ x ∈ l, x ≤ a := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons b v ih =>
      intro _
      rcases v with _ | ⟨c, w⟩
      · exact ⟨b, by simp, by simp⟩
      · obtain ⟨a, ha, hmax⟩ := ih (by simp)
        rcases le_total a b with h | h
        · refine ⟨b, by simp, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact le_refl _
          · exact (hmax x hx).trans h
        · refine ⟨a, List.mem_cons_of_mem _ ha, ?_⟩
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact h
          · exact hmax x hx
