namespace Imo2000P4

/-- The trick always works: the sum determines the unordered pair of boxes drawn from. -/
def Good (f : Fin 100 → Fin 3) : Prop :=
  Function.Surjective f ∧
  ∀ a b c d : Fin 100, f a ≠ f b → f c ≠ f d → (a : ℕ) + (b : ℕ) = (c : ℕ) + (d : ℕ) →
    (f a = f c ∧ f b = f d) ∨ (f a = f d ∧ f b = f c)

/-- Cards congruent mod `3` share a box. -/
def fM : Fin 100 → Fin 3 := fun i => ⟨(i : ℕ) % 3, by omega⟩

/-- The distribution `{1}`, `{2,…,99}`, `{100}`. -/
def fT : Fin 100 → Fin 3 :=
  fun i => ⟨if (i : ℕ) = 0 then 0 else if (i : ℕ) = 99 then 2 else 1, by split_ifs <;> omega⟩

/-! ### The two families work -/

theorem Good_fM : Good fM := by
  constructor
  · intro b
    fin_cases b
    · exact ⟨⟨0, by norm_num⟩, by decide⟩
    · exact ⟨⟨1, by norm_num⟩, by decide⟩
    · exact ⟨⟨2, by norm_num⟩, by decide⟩
  · intro a b c d hab hcd hsum
    simp only [fM, ne_eq, Fin.mk.injEq] at hab hcd ⊢
    omega

theorem Good_fT : Good fT := by
  constructor
  · intro b
    fin_cases b
    · exact ⟨⟨0, by norm_num⟩, by decide⟩
    · exact ⟨⟨1, by norm_num⟩, by decide⟩
    · exact ⟨⟨99, by norm_num⟩, by decide⟩
  · intro a b c d hab hcd hsum
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    have hd := d.isLt
    simp only [fT, ne_eq, Fin.mk.injEq] at hab hcd ⊢
    split_ifs at hab hcd ⊢ <;> omega

/-- Relabelling the boxes preserves the property. -/
theorem Good_comp (σ : Equiv.Perm (Fin 3)) {f : Fin 100 → Fin 3} (hf : Good f) :
    Good (fun i => σ (f i)) := by
  obtain ⟨hs, hc⟩ := hf
  constructor
  · intro b
    obtain ⟨i, hi⟩ := hs (σ.symm b)
    exact ⟨i, by simp [hi]⟩
  · intro a b c d hab hcd hsum
    have hab' : f a ≠ f b := fun h => hab (congrArg σ h)
    have hcd' : f c ≠ f d := fun h => hcd (congrArg σ h)
    rcases hc a b c d hab' hcd' hsum with ⟨u, v⟩ | ⟨u, v⟩
    · exact Or.inl ⟨congrArg σ u, congrArg σ v⟩
    · exact Or.inr ⟨congrArg σ u, congrArg σ v⟩

/-! ### Classification -/

/-- The two patterns, selected by a `Bool`. -/
def pat : Bool → (Fin 100 → Fin 3)
  | false => fM
  | true => fT

/-- The `12` distributions, indexed by a relabelling of the boxes and a choice of family. -/
def Phi (p : Equiv.Perm (Fin 3) × Bool) : {f : Fin 100 → Fin 3 // Good f} :=
  ⟨fun i => p.1 (pat p.2 i), by
    rcases p with ⟨σ, t⟩
    cases t
    · exact Good_comp σ Good_fM
    · exact Good_comp σ Good_fT⟩
