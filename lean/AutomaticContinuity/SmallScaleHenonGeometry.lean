import AutomaticContinuity.SmallScaleHenonTrapping

/-!
# Placing the canonical Hénon fixed point at any exterior distance

The explicit positive scale `(s-r)/(4*s)` leaves the first coordinate outside
the radius-`r` ball and makes the canonical exterior fixed point have norm `s`.
This is the scalar parameter choice needed before a norm-preserving rotation.
-/

namespace AutomaticContinuity.SmallScaleHenonTrapping

open Complex

theorem euclideanPairNorm_exteriorPoint (β : ℝ) (a : ℂ) :
    euclideanPairNorm (exteriorPoint β a) = Real.sqrt (1 + β ^ 2) * ‖a‖ := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [euclideanPairNorm_sq, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + β ^ 2)]
  simp only [exteriorPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

/-- An explicit small positive coupling and a positive real first coordinate
realize every exterior Euclidean distance, however close to the boundary. -/
theorem exists_exteriorPoint_of_norm {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ∃ (β : ℝ) (a : ℂ),
      0 < β ∧ β ≤ 1 / 4 ∧ r < ‖a‖ ∧
      euclideanPairNorm (exteriorPoint β a) = s ∧ 0 < a.re ∧ a.im = 0 := by
  have hs : 0 < s := hr.trans hrs
  let β : ℝ := (s - r) / (4 * s)
  have hβ : 0 < β := div_pos (sub_pos.mpr hrs) (by positivity)
  have hβeq : β * (4 * s) = s - r := by
    dsimp [β]
    exact div_mul_cancel₀ _ (by positivity)
  have hβq : β ≤ 1 / 4 := by nlinarith
  have hbase : 0 < 1 + β ^ 2 := by positivity
  have hsqrt : 0 < Real.sqrt (1 + β ^ 2) := Real.sqrt_pos.2 hbase
  have hsqrt_le : Real.sqrt (1 + β ^ 2) ≤ 1 + β := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have hsep : r * Real.sqrt (1 + β ^ 2) < s := by
    have hbr : β * r < β * s := mul_lt_mul_of_pos_left hrs hβ
    nlinarith [mul_le_mul_of_nonneg_left hsqrt_le hr.le]
  let a : ℂ := ((s / Real.sqrt (1 + β ^ 2) : ℝ) : ℂ)
  have ha : 0 < s / Real.sqrt (1 + β ^ 2) := div_pos hs hsqrt
  have hanorm : ‖a‖ = s / Real.sqrt (1 + β ^ 2) := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  refine ⟨β, a, hβ, hβq, ?_, ?_, ?_, ?_⟩
  · rw [hanorm]
    exact (lt_div_iff₀ hsqrt).2 hsep
  · rw [euclideanPairNorm_exteriorPoint, hanorm]
    field_simp
  · exact ha
  · rfl

end AutomaticContinuity.SmallScaleHenonTrapping
