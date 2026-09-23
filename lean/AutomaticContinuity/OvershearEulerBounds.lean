import AutomaticContinuity.ParameterOvershears

set_option autoImplicit false

/-!
# Quantitative Euler remainder of an actual overshear

The norm is the actual Euclidean norm on the two fibre coordinates. The
coefficient needs no regularity for these pointwise algebraic estimates.
-/

noncomputable section

namespace AutomaticContinuity.OvershearEulerBounds

open ParameterOvershears

variable {P : Type*}

def fiberField (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) : ℂ × ℂ :=
  (0, f (z.1, z.2.1) * z.2.2)

theorem fiberField_eq_vectorField_snd [NormedAddCommGroup P] [NormedSpace ℂ P]
    (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) :
    fiberField f z = (vectorField f z).2 := rfl

def remainder (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) : ℂ × ℂ :=
  (flow f t z).2 - z.2 - t • fiberField f z

theorem norm_remainder_eq (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) :
    euclideanPairNorm (remainder f t z) =
      ‖Complex.exp (t * f (z.1, z.2.1)) - 1 - t * f (z.1, z.2.1)‖ * ‖z.2.2‖ := by
  have heq : remainder f t z =
      (0, (Complex.exp (t * f (z.1, z.2.1)) - 1 - t * f (z.1, z.2.1)) * z.2.2) := by
    ext
    · simp [remainder, flow, fiberField, smul_eq_mul]
    · simp [remainder, flow, fiberField, smul_eq_mul]
      ring
  rw [heq]
  simp only [euclideanPairNorm, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  rw [Real.sqrt_sq (norm_nonneg _), norm_mul]

/-- Constant-one quadratic remainder whenever the scalar exponent lies in
the closed unit disk. -/
theorem norm_remainder_le (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ))
    (hsmall : ‖t‖ * ‖f (z.1, z.2.1)‖ ≤ 1) :
    euclideanPairNorm (remainder f t z) ≤
      (‖t‖ * ‖f (z.1, z.2.1)‖) ^ 2 * ‖z.2.2‖ := by
  rw [norm_remainder_eq]
  have hc : ‖t * f (z.1, z.2.1)‖ ≤ 1 := by simpa only [norm_mul] using hsmall
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right
    (Complex.norm_exp_sub_one_sub_id_le hc) (norm_nonneg z.2.2)

/-- Uniform constants only require bounds on the coefficient and second
fibre coordinate, with `‖t‖ * M ≤ 1`. -/
theorem norm_remainder_le_uniform (f : P × ℂ → ℂ) (t : ℂ)
    (z : P × (ℂ × ℂ)) {M B : ℝ}
    (hf : ‖f (z.1, z.2.1)‖ ≤ M) (hy : ‖z.2.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    euclideanPairNorm (remainder f t z) ≤ ‖t‖ ^ 2 * M ^ 2 * B := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hf
  have hB : 0 ≤ B := (norm_nonneg _).trans hy
  have hc : ‖t‖ * ‖f (z.1, z.2.1)‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hf (norm_nonneg t)).trans hsmall
  calc
    euclideanPairNorm (remainder f t z) ≤
        (‖t‖ * ‖f (z.1, z.2.1)‖) ^ 2 * ‖z.2.2‖ := norm_remainder_le f t z hc
    _ ≤ (‖t‖ * M) ^ 2 * B := by gcongr
    _ = ‖t‖ ^ 2 * M ^ 2 * B := by rw [mul_pow]

/-- Negative time gives the identical uniform estimate for the actual inverse. -/
theorem norm_inverse_remainder_le_uniform (f : P × ℂ → ℂ) (t : ℂ)
    (z : P × (ℂ × ℂ)) {M B : ℝ}
    (hf : ‖f (z.1, z.2.1)‖ ≤ M) (hy : ‖z.2.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    euclideanPairNorm (remainder f (-t) z) ≤ ‖t‖ ^ 2 * M ^ 2 * B := by
  simpa only [norm_neg] using norm_remainder_le_uniform f (-t) z hf hy
    (by simpa only [norm_neg] using hsmall)

end AutomaticContinuity.OvershearEulerBounds

