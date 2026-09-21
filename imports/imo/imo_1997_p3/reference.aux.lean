theorem f_append (p r : List ℝ) : f (p ++ r) = f p + f r + (p.length : ℝ) * r.sum := by
  induction p with
  | nil => simp [f]
  | cons a p ih =>
    simp only [List.cons_append, f, ih, List.length_cons, List.sum_append]
    push_cast
    ring

theorem f_add_reverse (l : List ℝ) : f l + f l.reverse = ((l.length : ℝ) + 1) * l.sum := by
  induction l with
  | nil => simp [f]
  | cons a t ih =>
    have h1 : f [a] = a := by simp [f]
    rw [List.reverse_cons, f_append, h1]
    simp only [f, List.length_reverse, List.length_cons, List.sum_cons, List.sum_nil,
      add_zero]
    push_cast
    linear_combination ih

theorem adjSwap_f {B : ℝ} {l l' : List ℝ} (h : AdjSwap B l l') : |f l - f l'| ≤ 2 * B := by
  obtain ⟨pre, post, a, b, ha, hb, hl, hl'⟩ := h
  have key : f l - f l' = b - a := by
    rw [hl, hl', f_append, f_append]
    simp only [f, List.sum_cons]
    ring
  rw [key, abs_le]
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

theorem adjSwap_perm {B : ℝ} {l l' : List ℝ} (h : AdjSwap B l l') : List.Perm l' l := by
  obtain ⟨pre, post, a, b, -, -, hl, hl'⟩ := h
  rw [hl, hl']
  exact List.Perm.append_left pre (List.Perm.swap a b post)

theorem adjSwap_cons {B : ℝ} {l l' : List ℝ} (a : ℝ) (h : AdjSwap B l l') :
    AdjSwap B (a :: l) (a :: l') := by
  obtain ⟨pre, post, u, v, hu, hv, hl, hl'⟩ := h
  exact ⟨a :: pre, post, u, v, hu, hv, by rw [hl]; simp, by rw [hl']; simp⟩

theorem reach_cons {B : ℝ} {l l' : List ℝ} (a : ℝ)
    (h : Relation.ReflTransGen (AdjSwap B) l l') :
    Relation.ReflTransGen (AdjSwap B) (a :: l) (a :: l') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (adjSwap_cons a hstep)

theorem reach_move {B : ℝ} (a : ℝ) (ha : |a| ≤ B) :
    ∀ r : List ℝ, (∀ z ∈ r, |z| ≤ B) →
      Relation.ReflTransGen (AdjSwap B) (a :: r) (r ++ [a]) := by
  intro r
  induction r with
  | nil =>
    intro _
    rw [List.nil_append]
  | cons b r ih =>
    intro hbd
    have hb1 : |b| ≤ B := hbd b (by simp)
    have hr : ∀ z ∈ r, |z| ≤ B := fun z hz => hbd z (by simp [hz])
    have step : AdjSwap B (a :: b :: r) (b :: a :: r) :=
      ⟨[], r, a, b, ha, hb1, by simp, by simp⟩
    refine Relation.ReflTransGen.head step ?_
    have h2 := reach_cons b (ih hr)
    simpa using h2

theorem reach_reverse {B : ℝ} : ∀ l : List ℝ, (∀ z ∈ l, |z| ≤ B) →
    Relation.ReflTransGen (AdjSwap B) l l.reverse := by
  intro l
  induction l with
  | nil =>
    intro _
    rw [List.reverse_nil]
  | cons a t ih =>
    intro hbd
    have ha : |a| ≤ B := hbd a (by simp)
    have ht : ∀ z ∈ t, |z| ≤ B := fun z hz => hbd z (by simp [hz])
    have htr : ∀ z ∈ t.reverse, |z| ≤ B := fun z hz => ht z (by simpa using hz)
    have s1 := reach_cons a (ih ht)
    have s2 := reach_move a ha t.reverse htr
    rw [List.reverse_cons]
    exact s1.trans s2

theorem reach_perm {B : ℝ} {l l' : List ℝ}
    (h : Relation.ReflTransGen (AdjSwap B) l l') : List.Perm l' l := by
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hstep ih => exact (adjSwap_perm hstep).trans ih

/-- Along a chain of swaps, a value starting above `c` and never landing in `[-c, c]` stays
above `c`. -/
theorem ivt' {B c : ℝ} (g : List ℝ → ℝ)
    (hstep : ∀ l l', AdjSwap B l l' → |g l - g l'| ≤ 2 * c)
    {a b : List ℝ} (hab : Relation.ReflTransGen (AdjSwap B) a b)
    (hno : ∀ z, Relation.ReflTransGen (AdjSwap B) a z → ¬ (|g z| ≤ c))
    (ha : c < g a) : c < g b := by
  induction hab with
  | refl => exact ha
  | tail hpath hstep' ih =>
    rename_i y z
    have hy : c < g y := ih
    have hbound := hstep y z hstep'
    have hnz := hno z (hpath.tail hstep')
    rw [abs_le] at hbound
    rw [not_le, lt_abs] at hnz
    rcases hnz with hzz | hzz
    · exact hzz
    · linarith [hbound.1, hbound.2]
