import AutomaticContinuity.PolynomialCutoff
import AutomaticContinuity.EuclideanPairRotations
import AutomaticContinuity.EuclideanTrajectoryStability
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pow

set_option autoImplicit false

/-!
# Explicit localized radial fields

The cubic cutoff is applied to scalar values, so it also works for polynomials
with holomorphic parameter coefficients. Both estimates below are uniform in
the degree of the resulting polynomial. The field vanishes on the zero section;
it may also vanish elsewhere.
-/

noncomputable section

namespace AutomaticContinuity.RadialCutoffField

open PolynomialCutoff EuclideanPairRotations

def amplified (m : ℕ) (z : ℂ) : ℂ := smoothStep^[m] z

theorem norm_amplified_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 8) (m : ℕ) :
    ‖amplified m z‖ ≤ (1 / 2 : ℝ) ^ m / 8 := by
  have hh := norm_eval_iterate_le (MvPolynomial.C z : MvPolynomial Unit ℂ)
    (fun _ => 0) (by simpa using hz) m
  simpa only [eval_iterate, MvPolynomial.eval_C, amplified] using hh

theorem norm_amplified_sub_one_le {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 8) (m : ℕ) :
    ‖amplified m z - 1‖ ≤ (1 / 2 : ℝ) ^ m / 8 := by
  have hh := norm_eval_iterate_sub_one_le (MvPolynomial.C z : MvPolynomial Unit ℂ)
    (fun _ => 0) (by simpa using hz) m
  simpa only [eval_iterate, MvPolynomial.eval_C, amplified] using hh

theorem differentiable_amplified (m : ℕ) : Differentiable ℂ (amplified m) := by
  have hH : Differentiable ℂ smoothStep := by unfold smoothStep; fun_prop
  exact hH.iterate m

variable {P : Type*}

/-- The coefficient is evaluated at the given base and fibre point. -/
def field (q : P × (ℂ × ℂ) → ℂ) (m : ℕ) (rate : ℝ)
    (p : P) (w : ℂ × ℂ) : ℂ × ℂ :=
  ((rate : ℂ) * amplified m (q (p, w))) • w

@[simp] theorem field_zero (q : P × (ℂ × ℂ) → ℂ) (m : ℕ) (rate : ℝ) (p : P) :
    field q m rate p 0 = 0 := by simp [field]

theorem field_small_on_protected (q : P × (ℂ × ℂ) → ℂ) (m : ℕ)
    {rate B : ℝ} (hrate : 0 ≤ rate) (p : P) (w : ℂ × ℂ)
    (hq : ‖q (p, w)‖ ≤ 1 / 8) (hw : euclideanPairNorm w ≤ B) :
    euclideanPairNorm (field q m rate p w) ≤ rate * ((1 / 2 : ℝ) ^ m / 8) * B := by
  simp only [field, euclideanPairNorm_complex_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hrate]
  have hB : 0 ≤ B := (euclideanPairNorm_nonneg w).trans hw
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_amplified_le hq m) hrate) hw
    (euclideanPairNorm_nonneg w) (by positivity)

theorem field_close_to_radial (q : P × (ℂ × ℂ) → ℂ) (m : ℕ)
    {rate B : ℝ} (hrate : 0 ≤ rate) (p : P) (w : ℂ × ℂ)
    (hq : ‖q (p, w) - 1‖ ≤ 1 / 8) (hw : euclideanPairNorm w ≤ B) :
    euclideanPairNorm (field q m rate p w - rate • w) ≤
      rate * ((1 / 2 : ℝ) ^ m / 8) * B := by
  have heq : field q m rate p w - rate • w =
      ((rate : ℂ) * (amplified m (q (p, w)) - 1)) • w := by
    rw [mul_sub, mul_one, sub_smul]
    rfl
  rw [heq, euclideanPairNorm_complex_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hrate]
  have hB : 0 ≤ B := (euclideanPairNorm_nonneg w).trans hw
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (norm_amplified_sub_one_le hq m) hrate) hw
    (euclideanPairNorm_nonneg w) (by positivity)

/-- One cutoff degree controls both regions for any prescribed positive
field accuracy. This choice does not involve the field's Lipschitz constant. -/
theorem exists_degree {rate B ε : ℝ} (hrate : 0 ≤ rate) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ m : ℕ, rate * ((1 / 2 : ℝ) ^ m / 8) * B < ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (by positivity : 0 < 8 * ε / (rate * B + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨m, ?_⟩
  have hprod : (1 / 2 : ℝ) ^ m * (rate * B + 1) < 8 * ε :=
    (lt_div_iff₀ (by positivity : 0 < rate * B + 1)).mp hm
  have hp : 0 < (1 / 2 : ℝ) ^ m := by positivity
  nlinarith

section Regularity

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_field (q : P × (ℂ × ℂ) → ℂ) (m : ℕ) (rate : ℝ)
    {U : Set (P × (ℂ × ℂ))} (hq : DifferentiableOn ℂ q U) :
    DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) => field q m rate z.1 z.2) U := by
  unfold field
  exact ((differentiableOn_const _).mul
    ((differentiable_amplified m).comp_differentiableOn hq)).smul differentiableOn_snd

end Regularity

end AutomaticContinuity.RadialCutoffField
