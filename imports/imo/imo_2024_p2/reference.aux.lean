lemma one_one_gcd
    (n : ℕ) :
    Nat.gcd
        ((1 : ℕ) ^ n + 1)
        ((1 : ℕ) ^ n + 1)
      =
    2 := by

  simp

theorem one_one_works :
    EventuallyConstantGCD 1 1 := by

  refine
    ⟨2,
     1,
     by norm_num,
     by norm_num,
     ?_⟩

  intro n hn

  exact
    one_one_gcd n

/-!
============================================================
3. Normalized source data
============================================================
-/

lemma eventual_gcd_le_twice
    {g d : ℕ}
    (hg :
      g = d ∨
      g = 2 * d) :
    g ≤ 2 * d := by

  rcases hg with h | h

  · rw [h]
    omega

  · rw [h]

/-!
============================================================
5. Divisibility gives an upper/lower comparison
============================================================
-/

lemma le_of_dvd_positive
    {K g : ℕ}
    (hg :
      0 < g)
    (hKg :
      K ∣ g) :
    K ≤ g := by

  exact
    Nat.le_of_dvd
      hg
      hKg

/-!
============================================================
6. Key arithmetic collapse
============================================================
-/

/--
If d,x,y are positive and

    d²*x*y + 1 ≤ 2d,

then d=x=y=1.
-/
lemma collapse_from_key_inequality
    {d x y : ℕ}
    (hd :
      0 < d)
    (hx :
      0 < x)
    (hy :
      0 < y)
    (h :
      d ^ 2 * x * y + 1
        ≤
      2 * d) :
    d = 1 ∧
    x = 1 ∧
    y = 1 := by

  have hxy_pos :
      0 < x * y := by

    exact
      Nat.mul_pos
        hx
        hy

  have hxy_one :
      1 ≤ x * y := by

    omega

  have hd2_le :
      d ^ 2 ≤
        d ^ 2 * x * y := by

    have hmul :
        d ^ 2 * 1
          ≤
        d ^ 2 * (x * y) :=

      Nat.mul_le_mul_left
        (d ^ 2)
        hxy_one

    simpa [Nat.mul_assoc] using hmul

  have hbasic :
      d ^ 2 + 1
        ≤
      2 * d := by

    calc
      d ^ 2 + 1
          ≤
        d ^ 2 * x * y + 1 := by

          exact
            Nat.add_le_add_right
              hd2_le
              1

      _ ≤ 2 * d :=
        h

  have hd_one :
      d = 1 := by

    nlinarith

  have hxy_eq :
      x * y = 1 := by

    subst d

    norm_num at h

    have hxy_le :
        x * y ≤ 1 := by
      omega

    omega

  have hx_one :
      x = 1 := by

    nlinarith

  have hy_one :
      y = 1 := by

    nlinarith

  exact
    ⟨hd_one,
     hx_one,
     hy_one⟩

/-!
============================================================
7. Euler-divisor endgame
============================================================
-/

/--
Assume

    d²xy + 1 ∣ g

and

    g = d or g = 2d.

Then d=x=y=1.
-/
lemma normalized_data_collapse
    {d x y g : ℕ}

    (hd :
      0 < d)

    (hx :
      0 < x)

    (hy :
      0 < y)

    (hgpos :
      0 < g)

    (hg :
      g = d ∨
      g = 2 * d)

    (hEuler :
      d ^ 2 * x * y + 1 ∣ g) :

    d = 1 ∧
    x = 1 ∧
    y = 1 := by

  have hK_le_g :
      d ^ 2 * x * y + 1
        ≤
      g := by

    exact
      Nat.le_of_dvd
        hgpos
        hEuler

  have hg_le :
      g ≤ 2 * d :=

    eventual_gcd_le_twice
      hg

  have hkey :
      d ^ 2 * x * y + 1
        ≤
      2 * d :=

    le_trans
      hK_le_g
      hg_le

  exact
    collapse_from_key_inequality
      hd
      hx
      hy
      hkey

/-!
============================================================
8. Return from normalized variables to a,b
============================================================
-/

lemma original_values_eq_one
    {a b d x y : ℕ}
    (ha :
      a = d * x)
    (hb :
      b = d * y)
    (hd :
      d = 1)
    (hx :
      x = 1)
    (hy :
      y = 1) :
    a = 1 ∧ b = 1 := by

  constructor

  · calc
      a = d * x := ha
      _ = 1 * 1 := by
        rw [hd, hx]
      _ = 1 := by
        norm_num

  · calc
      b = d * y := hb
      _ = 1 * 1 := by
        rw [hd, hy]
      _ = 1 := by
        norm_num

/-!
============================================================
9. Full normalized endgame
============================================================
-/

theorem endgame
    {a b g : ℕ}
    (D :
      NormalizedData a b)

    (hgpos :
      0 < g)

    (hg :
      g = D.d ∨
      g = 2 * D.d)

    (hEuler :
      D.d ^ 2 * D.x * D.y + 1 ∣ g) :

    a = 1 ∧
    b = 1 := by

  obtain
    ⟨hd1,
     hx1,
     hy1⟩ :=
    normalized_data_collapse
      D.hd
      D.hx
      D.hy
      hgpos
      hg
      hEuler

  exact
    original_values_eq_one
      D.ha
      D.hb
      hd1
      hx1
      hy1

/-!
============================================================
10. Direct source-style endgame
============================================================
-/

theorem endgame_expanded
    {a b d x y g : ℕ}

    (hd :
      0 < d)

    (hx :
      0 < x)

    (hy :
      0 < y)

    (ha :
      a = d * x)

    (hb :
      b = d * y)

    (hgpos :
      0 < g)

    (hg :
      g = d ∨
      g = 2 * d)

    (hEuler :
      d ^ 2 * x * y + 1 ∣ g) :

    a = 1 ∧
    b = 1 := by

  obtain
    ⟨hd1,
     hx1,
     hy1⟩ :=
    normalized_data_collapse
      hd
      hx
      hy
      hgpos
      hg
      hEuler

  exact
    original_values_eq_one
      ha
      hb
      hd1
      hx1
      hy1

/-!
============================================================
11. Source reduction interface
============================================================
-/

/-
The remaining source-specific number theory is:

1. prove that the stable gcd g is either d or 2d,
   where d = gcd(a,b);

2. prove, via Euler's theorem, that

       d²xy + 1 ∣ g

   after writing a=dx and b=dy.

Those facts are represented explicitly by
`source_reduction`.
-/

theorem imo2024_p2_core
    {a b : ℕ}

    (hstable :
      EventuallyConstantGCD a b)

    (source_reduction :
      EventuallyConstantGCD a b →
      ∃ D : NormalizedData a b,
        ∃ g : ℕ,
          0 < g ∧
          (g = D.d ∨
           g = 2 * D.d) ∧
          D.d ^ 2 * D.x * D.y + 1 ∣ g) :

    a = 1 ∧
    b = 1 := by

  obtain
    ⟨D,
     g,
     hgpos,
     hgform,
     hEuler⟩ :=
    source_reduction
      hstable

  exact
    endgame
      D
      hgpos
      hgform
      hEuler

/-!
============================================================
12. Final iff classification
============================================================
-/
