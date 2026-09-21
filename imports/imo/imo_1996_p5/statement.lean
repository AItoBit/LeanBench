namespace Imo1996P5

/-- **Metric core of IMO 1996 P5.** -/

theorem candidate (s1 s2 s3 s4 s5 s6 u v w RA RC RE : ℝ)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3)
    (hs4 : 0 ≤ s4) (hs5 : 0 ≤ s5) (hs6 : 0 ≤ s6)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hA : (s3 + s6) * w + (s1 + s4) * v ≤ 4 * RA * u)
    (hC : (s2 + s5) * v + (s3 + s6) * u ≤ 4 * RC * w)
    (hE : (s1 + s4) * u + (s2 + s5) * w ≤ 4 * RE * v) :
    (s1 + s2 + s3 + s4 + s5 + s6) / 2 ≤ RA + RC + RE :=
