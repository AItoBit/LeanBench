by

  intro hlast

  /-
  Turn every consecutive divisibility hypothesis into

      aᵢ ≡ aᵢ aᵢ₊₁ [ZMOD n].
  -/
  have hrel :
      ∀ i : ℕ,
        i + 1 < k →
          a i ≡ a i * a (i + 1) [ZMOD n] := by

    intro i hi

    exact
      modeq_of_chain_dvd
        (hchain i hi)

  /-
  By chaining,

      a₁ ≡ a₁ a₂ ... aₖ.
  -/
  have hfirst_full :
      a 0 ≡
        chainProd a (k - 1) [ZMOD n] := by

    apply first_modeq_chainProd n k a hrel

    omega

  /-
  We also need the product ending one position earlier:

      a₁ ≡ a₁ a₂ ... a_{k-1}.
  -/
  have hfirst_previous :
      a 0 ≡
        chainProd a (k - 2) [ZMOD n] := by

    apply first_modeq_chainProd n k a hrel

    omega

  /-
  Multiply by `aₖ`:

      a₁ aₖ ≡ a₁ a₂ ... aₖ.

  The auxiliary equality `hprod` deliberately isolates the
  `k - 1 = (k - 2) + 1` rewrite.  This avoids rewriting the
  occurrence inside `a (k - 1)`.
  -/
  have hfirst_last_to_full :
      a 0 * a (k - 1) ≡
        chainProd a (k - 1) [ZMOD n] := by

    have hm :
        a 0 * a (k - 1) ≡
          chainProd a (k - 2) * a (k - 1) [ZMOD n] :=
      hfirst_previous.mul_right (a (k - 1))

    have hk' :
        k - 1 = (k - 2) + 1 := by
      omega

    have hprod :
        chainProd a (k - 1) =
          chainProd a (k - 2) * a (k - 1) := by

      calc
        chainProd a (k - 1)
            =
          chainProd a ((k - 2) + 1) := by
            rw [hk']

        _ =
          chainProd a (k - 2) *
            a ((k - 2) + 1) := by
              rfl

        _ =
          chainProd a (k - 2) *
            a (k - 1) := by
              rw [← hk']

    rw [hprod]

    exact hm

  /-
  Assume the forbidden final divisibility

      n ∣ aₖ(a₁ - 1).

  This gives

      aₖ ≡ aₖ a₁ [ZMOD n].
  -/
  have hlast_modeq :
      a (k - 1) ≡
        a (k - 1) * a 0 [ZMOD n] := by

    exact
      modeq_of_chain_dvd hlast

  /-
  Since multiplication is commutative,

      aₖ a₁ ≡ a₁ a₂ ... aₖ,

  and therefore

      aₖ ≡ a₁ a₂ ... aₖ.
  -/
  have hlast_full :
      a (k - 1) ≡
        chainProd a (k - 1) [ZMOD n] := by

    have hcomm :
        a (k - 1) * a 0 ≡
          chainProd a (k - 1) [ZMOD n] := by

      calc
        a (k - 1) * a 0
            =
          a 0 * a (k - 1) := by
            ring

        _ ≡
          chainProd a (k - 1) [ZMOD n] :=
            hfirst_last_to_full

    exact
      hlast_modeq.trans hcomm

  /-
  Both endpoints are congruent to the same complete product.
  Hence

      a₁ ≡ aₖ [ZMOD n].
  -/
  have hends :
      a 0 ≡ a (k - 1) [ZMOD n] := by

    exact
      hfirst_full.trans
        hlast_full.symm

  /-
  Both relevant indices belong to `[0,k)`.
  -/
  have h0lt :
      0 < k := by
    omega

  have hlastlt :
      k - 1 < k := by
    omega

  /-
  Extract

      1 ≤ a₁ ≤ n
      1 ≤ aₖ ≤ n.
  -/
  have hb0 :
      1 ≤ a 0 ∧ a 0 ≤ n :=
    hbound 0 h0lt

  have hblast :
      1 ≤ a (k - 1) ∧
        a (k - 1) ≤ n :=
    hbound (k - 1) hlastlt

  /-
  Since they are congruent modulo `n` and both lie in `[1,n]`,
  they are actually equal.
  -/
  have heq :
      a 0 = a (k - 1) := by

    exact
      eq_of_modeq_of_mem_interval
        hb0.1
        hb0.2
        hblast.1
        hblast.2
        hends

  /-
  But `0 ≠ k-1` because `k ≥ 2`, and the entries are distinct.
  -/
  have hne :
      a 0 ≠ a (k - 1) := by

    apply
      hdistinct
        0
        (k - 1)

    · exact h0lt

    · exact hlastlt

    · omega

  exact hne heq
