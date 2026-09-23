import AutomaticContinuity.ContourExpansion
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.Ring

/-!
# Canonical one-variable Taylor coefficients and sharp Cauchy estimates

The coefficient is defined by the ordinary iterated complex derivative at zero.
For an entire scalar function it is equal to the normalized Cauchy integral on
every circle of positive radius. The same canonical coefficients give the Taylor
expansion on the whole complex plane. All analytic facts used below are existing
Mathlib theorems about actual derivatives and contour integrals.
-/

noncomputable section

namespace AutomaticContinuity.OneVariableCauchy

open Complex Metric
open scoped Real

/-- The canonical Taylor coefficient at the origin. -/
def coeff (h : ℂ → ℂ) (m : ℕ) : ℂ :=
  (m.factorial : ℂ)⁻¹ * iteratedDeriv m h 0

@[simp] theorem coeff_zero (h : ℂ → ℂ) : coeff h 0 = h 0 := by
  simp [coeff]

theorem coeff_add {h g : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hg : Differentiable ℂ g) (m : ℕ) :
    coeff (fun z => h z + g z) m = coeff h m + coeff g m := by
  unfold coeff
  rw [iteratedDeriv_fun_add hh.contDiff.contDiffAt hg.contDiff.contDiffAt, mul_add]

theorem coeff_sub {h g : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hg : Differentiable ℂ g) (m : ℕ) :
    coeff (fun z => h z - g z) m = coeff h m - coeff g m := by
  unfold coeff
  rw [iteratedDeriv_fun_sub hh.contDiff.contDiffAt hg.contDiff.contDiffAt, mul_sub]

@[simp] theorem coeff_neg (h : ℂ → ℂ) (m : ℕ) :
    coeff (fun z => -h z) m = -coeff h m := by
  simp [coeff]

theorem coeff_const_mul (c : ℂ) (h : ℂ → ℂ) (m : ℕ) :
    coeff (fun z => c * h z) m = c * coeff h m := by
  simp only [coeff, iteratedDeriv_const_mul_field]
  ring

@[simp] theorem coeff_pow (k m : ℕ) :
    coeff (fun z : ℂ => z ^ k) m = if m = k then 1 else 0 := by
  unfold coeff
  rw [iteratedDeriv_fun_pow_zero]
  by_cases hmk : m = k
  · subst k
    simp [Nat.factorial_ne_zero]
  · simp [hmk]

@[simp] theorem coeff_const (c : ℂ) (m : ℕ) :
    coeff (fun _ : ℂ => c) m = if m = 0 then c else 0 := by
  have heq : (fun _ : ℂ => c) = fun z : ℂ => c * z ^ 0 := by funext z; simp
  rw [heq, coeff_const_mul, coeff_pow]
  split_ifs <;> simp

/-- Cauchy's derivative formula identifies the canonical coefficient with the
contour integral on every positive-radius circle. -/
theorem coeff_eq_circleCoeff {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : 0 < R) (m : ℕ) :
    coeff h m = FiniteCauchy.circleCoeff R m h := by
  have hint := hh.differentiableOn.circleIntegral_one_div_sub_center_pow_smul
    (c := (0 : ℂ)) hR m
  have heq : (fun z : ℂ => h z / z ^ (m + 1)) =
      fun z : ℂ => (1 / (z - 0) ^ (m + 1)) • h z := by
    funext z
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  unfold FiniteCauchy.circleCoeff
  rw [heq, hint]
  simp only [smul_eq_mul, div_eq_mul_inv, coeff]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

/-- A single entire function has the same coefficient integral at every positive
radius; the coefficient does not depend on a later bound or evaluation point. -/
theorem circleCoeff_radius_eq {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R S : ℝ} (hR : 0 < R) (hS : 0 < S) (m : ℕ) :
    FiniteCauchy.circleCoeff R m h = FiniteCauchy.circleCoeff S m h := by
  rw [← coeff_eq_circleCoeff hh hR, ← coeff_eq_circleCoeff hh hS]

@[simp] theorem circleCoeff_const {R : ℝ} (hR : 0 < R) (c : ℂ) (m : ℕ) :
    FiniteCauchy.circleCoeff R m (fun _ => c) = if m = 0 then c else 0 := by
  rw [← coeff_eq_circleCoeff (differentiable_const c) hR]
  exact coeff_const c m

@[simp] theorem circleCoeff_pow {R : ℝ} (hR : 0 < R) (k m : ℕ) :
    FiniteCauchy.circleCoeff R m (fun z : ℂ => z ^ k) = if m = k then 1 else 0 := by
  rw [← coeff_eq_circleCoeff (show Differentiable ℂ (fun z : ℂ => z ^ k) by fun_prop) hR]
  exact coeff_pow k m

/-- The sharp constant-one Cauchy coefficient bound. -/
theorem norm_coeff_le {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R M : ℝ} (hR : 0 < R) (m : ℕ)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ ≤ M) :
    ‖coeff h m‖ ≤ M / R ^ m := by
  rw [coeff_eq_circleCoeff hh hR]
  exact FiniteCauchy.norm_circleCoeff_le hR m h hbound

/-- The canonical Taylor series of an entire function converges everywhere. -/
theorem hasSum_coeff_mul_pow {h : ℂ → ℂ} (hh : Differentiable ℂ h) (z : ℂ) :
    HasSum (fun m : ℕ => coeff h m * z ^ m) (h z) := by
  have hsum := Complex.hasSum_taylorSeries_of_entire hh 0 z
  convert! hsum using 1
  funext m
  simp only [coeff, sub_zero, smul_eq_mul]
  ring

theorem tsum_coeff_mul_pow {h : ℂ → ℂ} (hh : Differentiable ℂ h) (z : ℂ) :
    (∑' m : ℕ, coeff h m * z ^ m) = h z :=
  (hasSum_coeff_mul_pow hh z).tsum_eq

/-- Expansion using the coefficient integrals at any one fixed positive radius.
For entire functions the evaluation point may lie outside that circle. -/
theorem hasSum_circleCoeff_mul_pow {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} (hR : 0 < R) (z : ℂ) :
    HasSum (fun m : ℕ => FiniteCauchy.circleCoeff R m h * z ^ m) (h z) := by
  simpa only [← coeff_eq_circleCoeff hh hR] using hasSum_coeff_mul_pow hh z

/-- Scalar Cauchy's formula with exactly the normalization and integrand used
by the finite-dimensional integral infrastructure. -/
theorem normalized_cauchyIntegral_eq {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ ζ in C(0, R), h ζ / (ζ - z)) = h z := by
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  exact (hasSum_circleCoeff_mul_pow_integral
    (hh.continuous.continuousOn.circleIntegrable hR.le) hz).unique
      (hasSum_circleCoeff_mul_pow hh hR z)

end AutomaticContinuity.OneVariableCauchy
