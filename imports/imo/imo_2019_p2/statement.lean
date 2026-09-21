/--
This packages the complete logical structure of the supplied
solution.

It assumes the standard Euclidean facts that:

1. the first equal-angle relation constructs the auxiliary
   circle through `P,Q,A0,B0`;

2. the equal-angle criterion puts `P1` on that circle;

3. the analogous equal-angle criterion puts `Q1` on that circle.

Everything connecting those facts is fully checked by Lean.
-/
theorem candidate
    {P Q P1 Q1 A0 B0 : Point}
    (δ φ ψ : ℝ)

    /- Construction of the auxiliary circle. -/
    (hQPA0 :
      ang Q P A0 = δ)

    (hQB0A0 :
      ang Q B0 A0 = δ)

    (cyclic_of_equal_angle :
      ang Q P A0 =
          ang Q B0 A0 →
      ∃ ω : Circle,
        OnCircle ω P ∧
        OnCircle ω Q ∧
        OnCircle ω A0 ∧
        OnCircle ω B0)

    /- P1 angle chain. -/
    (hPA0 :
      ang P A0 B0 = φ)

    (hPP1 :
      ang P P1 B0 = φ)

    /- Q1 angle chain. -/
    (hQA0 :
      ang Q A0 B0 = ψ)

    (hQQ1 :
      ang Q Q1 B0 = ψ)

    /- Converse-inscribed-angle criterion for P1. -/
    (p1_membership :
      ∀ ω : Circle,
        OnCircle ω P →
        OnCircle ω A0 →
        OnCircle ω B0 →
        ang P A0 B0 =
            ang P P1 B0 →
        OnCircle ω P1)

    /- Converse-inscribed-angle criterion for Q1. -/
    (q1_membership :
      ∀ ω : Circle,
        OnCircle ω Q →
        OnCircle ω A0 →
        OnCircle ω B0 →
        ang Q A0 B0 =
            ang Q Q1 B0 →
        OnCircle ω Q1) :
    Concyclic
      OnCircle
      P
      Q
      P1
      Q1 :=
