open List

namespace Imo1989P6

/-! ### Pairs and partners -/

/-- `a` and `b` differ by `n`. -/
def Pair (n a b : ℕ) : Prop := a + n = b ∨ b + n = a

/-- The relation "these two values do *not* differ by `n`". -/
def NotPair (n a b : ℕ) : Prop := ¬ Pair n a b

/-- The partner of `a` inside `{0, …, 2n-1}`. -/
def ptn (n a : ℕ) : ℕ := if a < n then a + n else a - n

theorem pair_symm {n a b : ℕ} (h : Pair n a b) : Pair n b a := h.symm

theorem pair_ptn {n a : ℕ} (_hn : 0 < n) (ha : a < 2 * n) : Pair n a (ptn n a) := by
  simp only [ptn, Pair]
  split_ifs with h <;> omega

theorem ptn_lt {n a : ℕ} (_hn : 0 < n) (ha : a < 2 * n) : ptn n a < 2 * n := by
  simp only [ptn]
  split_ifs with h <;> omega

theorem ptn_ne {n a : ℕ} (hn : 0 < n) (_ha : a < 2 * n) : ptn n a ≠ a := by
  simp only [ptn]
  split_ifs with h <;> omega

/-- Inside `{0, …, 2n-1}` the partner is unique. -/
theorem eq_ptn_of_pair {n a b : ℕ} (_hn : 0 < n) (_ha : a < 2 * n) (hb : b < 2 * n)
    (h : Pair n a b) : b = ptn n a := by
  simp only [Pair] at h
  simp only [ptn]
  split_ifs with hc <;> omega

/-! ### The two surgeries -/

/-- **Forward surgery.** In a listing `a :: (pre ++ p :: post)` with no `n`-pair, moving the head
`a` to sit just in front of its partner `p` gives `pre ++ a :: p :: post`, which has no `n`-pair
before the junction and none after it. -/
theorem chain_move {n a p : ℕ} {pre post : List ℕ}
    (hchain : (a :: (pre ++ p :: post)).IsChain (NotPair n))
    (hpre : ∀ x ∈ pre, ¬ Pair n x a) :
    (pre ++ [a]).IsChain (NotPair n) ∧ (p :: post).IsChain (NotPair n) := by
  rw [isChain_cons_split] at hchain
  obtain ⟨h1, h2⟩ := hchain
  refine ⟨?_, h2⟩
  rw [← cons_append] at h1
  have h3 : (a :: pre).IsChain (NotPair n) := h1.left_of_append
  refine IsChain.append (by simpa using h3.tail) (isChain_singleton a) ?_
  intro x hx y hy
  simp only [head?_cons, Option.mem_def, Option.some.injEq] at hy
  subst hy
  exact hpre x (mem_of_mem_getLast? hx)

/-- **Uniqueness of the junction.** A listing can be cut at an `n`-pair, with no `n`-pair strictly
earlier, in at most one way. -/
theorem junction_unique {n : ℕ} {m pre₁ post₁ pre₂ post₂ : List ℕ} {a₁ p₁ a₂ p₂ : ℕ}
    (h₁ : m = pre₁ ++ a₁ :: p₁ :: post₁) (h₂ : m = pre₂ ++ a₂ :: p₂ :: post₂)
    (c₁ : (pre₁ ++ [a₁]).IsChain (NotPair n)) (c₂ : (pre₂ ++ [a₂]).IsChain (NotPair n))
    (q₁ : Pair n a₁ p₁) (q₂ : Pair n a₂ p₂) :
    pre₁ = pre₂ ∧ a₁ = a₂ ∧ p₁ = p₂ ∧ post₁ = post₂ := by
  have e₁ : m = (pre₁ ++ [a₁]) ++ (p₁ :: post₁) := by rw [h₁]; simp
  have e₂ : m = (pre₂ ++ [a₂]) ++ (p₂ :: post₂) := by rw [h₂]; simp
  have hp₁ : (pre₁ ++ [a₁]) <+: m := ⟨p₁ :: post₁, e₁.symm⟩
  have hp₂ : (pre₂ ++ [a₂]) <+: m := ⟨p₂ :: post₂, e₂.symm⟩
  -- the two cut points coincide
  have key : pre₁ ++ [a₁] = pre₂ ++ [a₂] := by
    rcases List.prefix_or_prefix_of_prefix hp₁ hp₂ with h | h
    · obtain ⟨w, hw⟩ := h
      cases w with
      | nil => simpa using hw
      | cons c w' =>
        exfalso
        have hcat : (pre₁ ++ [a₁]) ++ (p₁ :: post₁)
            = (pre₁ ++ [a₁]) ++ ((c :: w') ++ (p₂ :: post₂)) := by
          rw [← e₁, e₂, ← hw, List.append_assoc]
        have hsplit : p₁ :: post₁ = (c :: w') ++ (p₂ :: post₂) :=
          List.append_cancel_left hcat
        have hc : c = p₁ := by
          simp only [List.cons_append, List.cons.injEq] at hsplit
          exact hsplit.1.symm
        subst hc
        have hdec : pre₂ ++ [a₂] = pre₁ ++ a₁ :: c :: w' := by
          rw [← hw]; simp
        exact (isChain_iff_forall_rel_of_append_cons_cons.1 c₂ hdec) q₁
    · obtain ⟨w, hw⟩ := h
      cases w with
      | nil => simpa using hw.symm
      | cons c w' =>
        exfalso
        have hcat : (pre₂ ++ [a₂]) ++ (p₂ :: post₂)
            = (pre₂ ++ [a₂]) ++ ((c :: w') ++ (p₁ :: post₁)) := by
          rw [← e₂, e₁, ← hw, List.append_assoc]
        have hsplit : p₂ :: post₂ = (c :: w') ++ (p₁ :: post₁) :=
          List.append_cancel_left hcat
        have hc : c = p₂ := by
          simp only [List.cons_append, List.cons.injEq] at hsplit
          exact hsplit.1.symm
        subst hc
        have hdec : pre₁ ++ [a₁] = pre₂ ++ a₂ :: c :: w' := by
          rw [← hw]; simp
        exact (isChain_iff_forall_rel_of_append_cons_cons.1 c₁ hdec) q₂
  obtain ⟨hpre, hlast⟩ := List.append_inj' key (by simp)
  have ha : a₁ = a₂ := by simpa using hlast
  subst hpre
  subst ha
  rw [h₁] at h₂
  have := List.append_cancel_left h₂
  simp only [List.cons.injEq] at this
  exact ⟨rfl, rfl, this.2.1, this.2.2⟩

/-! ### The set of listings -/

/-- All listings of `{0, …, 2n-1}`. -/
def perms (n : ℕ) : Finset (List ℕ) := (List.range (2 * n)).permutations.toFinset

theorem mem_perms {n : ℕ} {l : List ℕ} : l ∈ perms n ↔ l ~ List.range (2 * n) := by
  simp [perms, List.mem_permutations]

/-- A listing without property `T` splits at the partner of its head, with a nonempty prefix, and
the moved listing has no `n`-pair before the junction. -/
theorem split_data {n : ℕ} (hn : 0 < n) {l : List ℕ} (hperm : l ~ List.range (2 * n))
    (hchain : l.IsChain (NotPair n)) :
    ∃ a pre post, l = a :: (pre ++ ptn n a :: post) ∧ pre ≠ [] ∧ a < 2 * n ∧
      (pre ++ [a]).IsChain (NotPair n) := by
  have hlen : l.length = 2 * n := by
    rw [hperm.length_eq, List.length_range]
  have hlt : ∀ x ∈ l, x < 2 * n := fun x hx => List.mem_range.1 (hperm.mem_iff.1 hx)
  have hnodup : l.Nodup := hperm.nodup_iff.2 (List.nodup_range)
  -- the head
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, l = a :: rest := by
    cases l with
    | nil => simp at hlen; omega
    | cons a rest => exact ⟨a, rest, rfl⟩
  have ha : a < 2 * n := hlt a (List.mem_cons_self ..)
  have hpltn : ptn n a < 2 * n := ptn_lt hn ha
  have hpne : ptn n a ≠ a := ptn_ne hn ha
  have hpmem : ptn n a ∈ a :: rest :=
    hperm.mem_iff.2 (List.mem_range.2 hpltn)
  have hprest : ptn n a ∈ rest := by
    rcases List.mem_cons.1 hpmem with h | h
    · exact absurd h hpne
    · exact h
  obtain ⟨pre, post, hrest⟩ := List.append_of_mem hprest
  subst hrest
  -- `pre` is nonempty
  have hprene : pre ≠ [] := by
    rintro rfl
    simp only [List.nil_append] at hchain
    exact (isChain_cons_cons.1 hchain).1 (pair_ptn hn ha)
  -- no element of `pre` is a partner of `a`
  have hnd : (pre ++ ptn n a :: post).Nodup := hnodup.of_cons
  have hnotmem : ptn n a ∉ pre := by
    intro hmem
    exact (List.nodup_append'.1 hnd).2.2 hmem (List.mem_cons_self ..)
  have hpre : ∀ x ∈ pre, ¬ Pair n x a := by
    intro x hx hpx
    have hxlt : x < 2 * n := hlt x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
    have : x = ptn n a := eq_ptn_of_pair hn ha hxlt (pair_symm hpx)
    subst this
    exact hnotmem hx
  exact ⟨a, pre, post, rfl, hprene, ha, (chain_move hchain hpre).1⟩

/-! ### The theorem -/
