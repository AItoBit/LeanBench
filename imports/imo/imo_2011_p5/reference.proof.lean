by

  intro m n hmn

  /-
  If f(m)=f(n), divisibility is immediate.
  -/
  by_cases heq :
      f m = f n

  · rw [heq]

  /-
  Hence assume

      f(m) < f(n).
  -/
  · have hlt :
        f m < f n := by
      exact lt_of_le_of_ne hmn heq

    /-
    First use

        f(m-n) ∣ f(m)-f(n).

    Since the right side is negative and nonzero, write

        f(m)-f(n) = f(m-n) * q

    with q < 0.

    This implies

        f(m-n) ≤ f(n)-f(m) < f(n),

    so

        f(m-n) < f(n).
    -/
    have hmnDiv :
        f (m - n) ∣ f m - f n :=
      hdiv m n

    rcases hmnDiv with ⟨q, hq⟩

    have hqneg :
        q < 0 := by

      by_contra hnot

      have hqnonneg :
          0 ≤ q := by
        exact le_of_not_gt hnot

      have hprod :
          0 ≤ f (m - n) * q := by
        exact
          mul_nonneg
            (le_of_lt (hpos (m - n)))
            hqnonneg

      linarith

    have hminusq :
        1 ≤ -q := by
      omega

    have hmul :
        f (m - n)
          ≤
        f (m - n) * (-q) := by

      have h :=
        mul_le_mul_of_nonneg_left
          hminusq
          (le_of_lt (hpos (m - n)))

      simpa using h

    have hrewrite :
        f (m - n) * (-q)
          =
        f n - f m := by

      calc
        f (m - n) * (-q)
            =
          -(f (m - n) * q) := by
            ring

        _ =
          -(f m - f n) := by
            rw [← hq]

        _ =
          f n - f m := by
            ring

    have hcdiff :
        f (m - n)
          ≤
        f n - f m := by

      calc
        f (m - n)
            ≤
          f (m - n) * (-q) :=
            hmul

        _ =
          f n - f m :=
            hrewrite

    have hclt :
        f (m - n) < f n := by
      have hmpos :
          0 < f m :=
        hpos m

      linarith

    /-
    Now apply the original condition to

        (m, m-n).

    Since

        m - (m-n) = n,

    we obtain

        f(n) ∣ f(m) - f(m-n).
    -/
    have hsecond :=
      hdiv m (m - n)

    have hindex :
        m - (m - n) = n := by
      ring

    rw [hindex] at hsecond

    /-
    We now have

        0 < f(m) < f(n)
        0 < f(m-n) < f(n)

    and

        f(n) ∣ f(m)-f(m-n).

    The small-multiple lemma forces

        f(m) = f(m-n).
    -/
    have hsame :
        f m = f (m - n) := by

      exact
        eq_of_dvd_sub_of_lt
          (hpos m)
          (hpos n)
          (hpos (m - n))
          hlt
          hclt
          hsecond

    /-
    Return to

        f(m-n) ∣ f(m)-f(n).

    Since f(m-n)=f(m), we have

        f(m) ∣ f(m)-f(n).

    Therefore f(m) divides f(n).
    -/
    have hfinalDiv :
        f m ∣ f m - f n := by

      have htemp :
          f (m - n) ∣ f m - f n := by
        exact hdiv m n

      rw [← hsame] at htemp

      exact htemp

    rcases hfinalDiv with ⟨r, hr⟩

    refine ⟨1 - r, ?_⟩

    calc
      f n
          =
        f m - (f m - f n) := by
          ring

      _ =
        f m - f m * r := by
          rw [hr]

      _ =
        f m * (1 - r) := by
          ring
