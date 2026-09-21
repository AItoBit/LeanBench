namespace Imo1997P2

/-- **Trigonometric core of IMO 1997 P2.** -/

theorem candidate (u A R BC TB TC AU : ℝ)
    (hP : Real.sin (u + A) ≠ 0)
    (hQ : Real.cos (u + A) ≠ 0)
    (hAU : AU = 2 * R * Real.cos u)
    (hBC : BC = 2 * R * Real.cos (u + A))
    (h3 : TB * Real.cos (2 * u + A) + TC * Real.cos A = BC)
    (h4 : TB * Real.sin (2 * u + A) = TC * Real.sin A) :
    AU = TB + TC :=
