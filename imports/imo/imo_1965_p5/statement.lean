/-- Every orthocenter arising from a point `M` of the side `AB` lies on the line
`a*c*x + (b² + c² - a*b)*y = a*b*c`. -/
theorem candidate (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (M : ℝ × ℝ) (hMseg : M ∈ segment ℝ ((a : ℝ), (0 : ℝ)) (b, c)) (H : ℝ × ℝ)
    (hH : IsOrthocenter 0 (footX M) (footLine (b, c) M) H) :
    a * c * H.1 + (b ^ 2 + c ^ 2 - a * b) * H.2 = a * b * c :=
