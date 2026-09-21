namespace Imo1982P5

/-- **IMO 1982, Problem 5.** -/

theorem candidate (r s Mx My Nx Ny : ℝ)
    (hs : s = Real.sqrt 3) (hr0 : 0 < r) (hr1 : r < 1)
    -- `M = A + r (C - A)` with `A = (1, 0)`, `C = (-1/2, s/2)`
    (hMx : Mx = 1 + r * ((-1 / 2) - 1))
    (hMy : My = 0 + r * (s / 2 - 0))
    -- `N = C + r (E - C)` with `C = (-1/2, s/2)`, `E = (-1/2, -s/2)`
    (hNx : Nx = (-1 / 2) + r * ((-1 / 2) - (-1 / 2)))
    (hNy : Ny = s / 2 + r * ((-(s / 2)) - s / 2))
    -- `B = (1/2, s/2)` is collinear with `M` and `N`
    (hcol : (Mx - 1 / 2) * (Ny - s / 2) = (My - s / 2) * (Nx - 1 / 2)) :
    r = Real.sqrt 3 / 3 :=
