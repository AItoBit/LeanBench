namespace IMO2018P6

/-!
# IMO 2018 Problem 6 — final algebraic core

The source introduces

    α = ∠XAB = ∠XCD
    φ = ∠BXA
    ψ = ∠DXC.

Its common-case argument establishes

    BX / DX = AB / CD.

The sine rule gives

    AB / sin φ = BX / sin α
    CD / sin ψ = DX / sin α.

We formalize these in denominator-free form:

    AB * sin α = BX * sin φ
    CD * sin α = DX * sin ψ
    BX * CD    = DX * AB.

From these equations and positivity/nondegeneracy of the
lengths we derive

    sin ψ = sin φ.

The geometric part of the source then distinguishes:

* φ = ψ, which leads to the special symmetric case;
* φ ≠ ψ, in which the equality of sines gives
      φ + ψ = 180°.

The file also formalizes the final angle arithmetic in both
the common and special cases.

No `sorry`, `admit`, or additional axioms are used.
-/

/-!
============================================================
1. Algebra behind the sine-rule step
============================================================
-/
