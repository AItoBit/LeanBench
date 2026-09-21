open EuclideanGeometry

namespace Imo1971P4

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- `cos (2 x) = 1 - 2 sin x ^ 2`. -/
private lemma cos_two_mul' (x : ℝ) : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  linarith [Real.sin_sq_add_cos_sq x]

/-- **Chord formula.**  In the isosceles triangle with apex `c`, equal legs `r`
and apex angle `∠ a c b`, the base has length `2 * r * sin (∠ a c b / 2)`.

This is the last step of part (b): with `c = C`, `a = A`, `b = A'` (the two
copies of `A` in the development) and `α = ∠ B A C + ∠ C A D + ∠ D A B` the
total angle at `C`, it gives the announced value `2 * AC * sin (α / 2)`. -/
theorem dist_eq_two_mul_sin_half_angle {a b c : P} {r : ℝ}
    (ha : dist a c = r) (hb : dist b c = r) :
    dist a b = 2 * r * Real.sin (∠ a c b / 2) := by
  have hr0 : 0 ≤ r := ha ▸ dist_nonneg
  have hs0 : 0 ≤ Real.sin (∠ a c b / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [angle_nonneg a c b])
      (by linarith [angle_le_pi a c b, Real.pi_pos])
  have hcos : Real.cos (∠ a c b) = 1 - 2 * Real.sin (∠ a c b / 2) ^ 2 := by
    have h := cos_two_mul' (∠ a c b / 2)
    rwa [show 2 * (∠ a c b / 2) = ∠ a c b by ring] at h
  have hlaw := EuclideanGeometry.law_cos a c b
  rw [ha, hb] at hlaw
  have hsq : dist a b ^ 2 = (2 * r * Real.sin (∠ a c b / 2)) ^ 2 := by
    rw [pow_two, pow_two, hlaw, hcos]; ring
  have hnn : 0 ≤ 2 * r * Real.sin (∠ a c b / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hr0) hs0
  calc dist a b = Real.sqrt (dist a b ^ 2) := (Real.sqrt_sq dist_nonneg).symm
    _ = Real.sqrt ((2 * r * Real.sin (∠ a c b / 2)) ^ 2) := by rw [hsq]
    _ = 2 * r * Real.sin (∠ a c b / 2) := Real.sqrt_sq hnn

/-- **Unfolding lower bound.**  In the developed plane, a four-link path
`x → y → z → t → x'` is at least as long as the segment `x x'`. -/
theorem length_ge (x y z t x' : P) :
    dist x x' ≤ dist x y + dist y z + dist z t + dist t x' := by
  have h1 := dist_triangle x y z
  have h2 := dist_triangle x z t
  have h3 := dist_triangle x t x'
  linarith
