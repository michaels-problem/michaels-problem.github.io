import AutomaticContinuity.FiniteCauchyRadius
import AutomaticContinuity.FiniteCauchyPrefix
import AutomaticContinuity.FiniteCauchyExpansion
import AutomaticContinuity.StageStep

set_option autoImplicit false

/-!
# Canonical finite-variable Taylor representatives in the coefficient algebra

One fixed contour defines the coefficients. Radius independence and sharp
Cauchy estimates prove all-radius absolute summability; the resulting element
of the actual coefficient algebra represents the entire function.
-/

noncomputable section

namespace AutomaticContinuity.FiniteTaylor

open CoefficientSeries FiniteCauchy

/-- Canonical finite coefficients, always chosen on the same unit torus. -/
def taylorCoeff {n : ℕ} (h : FinitePoint n → ℂ) : FiniteMultiIndex n → ℂ :=
  coefficient (fun _ => 1) h

theorem taylorCoeff_eq_coefficient {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) {R : ℝ} (hR : 0 < R) (α : FiniteMultiIndex n) :
    taylorCoeff h α = coefficient (fun _ => R) h α :=
  coefficient_eq_of_entire (fun _ => 1) (fun _ => R) (fun _ => by norm_num)
    (fun _ => hR) h hh α

theorem norm_taylorCoeff_le {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) {R M : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ polydisc n R, ‖h z‖ ≤ M) (α : FiniteMultiIndex n) :
    ‖taylorCoeff h α‖ ≤ M / R ^ finiteTotalDegree α := by
  rw [taylorCoeff_eq_coefficient h hh hR]
  exact norm_coefficient_le_common hR h hbound α

theorem summable_taylorCoeff {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) (r : ℕ) (hr : 0 < r) :
    Summable (finiteWeightedTerm (r : ℝ) (taylorCoeff h)) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨M, hM⟩ := ((isCompact_polydisc n (by positivity : 0 ≤ 2 * (r : ℝ))).image
    hh.continuous.norm).bddAbove
  apply (finiteCauchy_bound hr' (M := M) ?_).1
  intro α
  apply norm_taylorCoeff_le h hh (by positivity)
  intro z hz
  exact hM ⟨z, hz, rfl⟩

/-- The actual all-radius coefficient series representing an entire function. -/
def ofEntire {n : ℕ} (h : FinitePoint n → ℂ) (hh : Differentiable ℂ h) :
    CoefficientSeries :=
  embedFiniteCoefficients (taylorCoeff h) (summable_taylorCoeff h hh)

theorem evaluate_ofEntire {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) (w : BoundedSequence) :
    evaluate w (ofEntire h hh) = h (restrictSequence n w) := by
  rw [ofEntire, evaluate_embedFiniteCoefficients]
  obtain ⟨r, hr, hw⟩ := w.exists_integral_radius
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hz : restrictSequence n w ∈ polydisc n (2 * (r : ℝ) / 2) := by
    intro j
    change ‖w.val j.val‖ ≤ 2 * (r : ℝ) / 2
    nlinarith [hw j.val]
  have hs := hasSum_coefficient_mul_monomial h hh
    (by positivity : 0 < 2 * (r : ℝ)) (restrictSequence n w) hz
  simpa only [← taylorCoeff_eq_coefficient h hh (by positivity : 0 < 2 * (r : ℝ)),
    FiniteCauchy.monomial] using hs.tsum_eq

theorem q_ofEntire_le {n : ℕ} (h : FinitePoint n → ℂ) (hh : Differentiable ℂ h)
    (r : ℕ) (hr : 0 < r) (M : ℝ)
    (hbound : ∀ z ∈ polydisc n (2 * (r : ℝ)), ‖h z‖ ≤ M) :
    q r (ofEntire h hh) ≤ M * 2 ^ n := by
  rw [ofEntire, q_embedFiniteCoefficients]
  apply (finiteCauchy_bound (by exact_mod_cast hr) (M := M) ?_).2
  intro α
  exact norm_taylorCoeff_le h hh (by positivity) hbound α

theorem q_ofEntire_stage_le {n : ℕ} (hn : 0 < n)
    (h : FinitePoint n → ℂ) (hh : Differentiable ℂ h)
    (hbound : ∀ z ∈ polydisc n (2 * (n : ℝ)),
      ‖h z‖ ≤ ((2 : ℝ) ^ (3 * n))⁻¹) :
    q n (ofEntire h hh) ≤ (1 / 4 : ℝ) ^ n := by
  rw [ofEntire, q_embedFiniteCoefficients]
  have hc (α : FiniteMultiIndex n) :
      ‖taylorCoeff h α‖ ≤ ((2 : ℝ) ^ (3 * n))⁻¹ /
        (2 * (n : ℝ)) ^ finiteTotalDegree α :=
    norm_taylorCoeff_le h hh (by positivity) hbound α
  simpa only [stageCoefficientError_eq_quarter_pow] using
    (finiteStageCauchy_bound hn hc).2

theorem ofEntire_sub {n : ℕ} (h k : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) (hk : Differentiable ℂ k) :
    ofEntire (fun z => h z - k z) (hh.sub hk) = ofEntire h hh - ofEntire k hk := by
  have hc : taylorCoeff (fun z => h z - k z) =
      fun α => taylorCoeff h α - taylorCoeff k α := by
    funext α
    exact coefficient_sub (fun _ => 1) (fun _ => by norm_num)
      hh.continuous hk.continuous α
  apply Subtype.ext
  change extendFiniteCoefficients (taylorCoeff (fun z => h z - k z)) =
    extendFiniteCoefficients (taylorCoeff h) - extendFiniteCoefficients (taylorCoeff k)
  rw [hc]
  exact congrArg Subtype.val (embedFiniteCoefficients_sub _ _
    (summable_taylorCoeff h hh) (summable_taylorCoeff k hk)
    (hc ▸ summable_taylorCoeff (fun z => h z - k z) (hh.sub hk)))

theorem ofEntire_prefixProjection {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) :
    ofEntire (fun z => h (prefixProjection n z))
      (hh.comp (differentiable_prefixProjection n)) = ofEntire h hh := by
  apply Subtype.ext
  change extendFiniteCoefficients (taylorCoeff (fun z => h (prefixProjection n z))) =
    extendFiniteCoefficients (taylorCoeff h)
  have hc : taylorCoeff (fun z => h (prefixProjection n z)) =
      liftFiniteCoefficients (taylorCoeff h) := by
    funext α
    exact coefficient_prefixProjection (by norm_num : (0 : ℝ) < 1) h α
  rw [hc, extendFiniteCoefficients_lift]

/-- The bound is on the actual difference of two representatives, after the
older function is regarded as independent of the newly added variable. -/
theorem q_sub_ofEntire_le {n : ℕ}
    (h : FinitePoint (n + 1) → ℂ) (k : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) (hk : Differentiable ℂ k)
    (hbound : ∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
      ‖h z - k (prefixProjection n z)‖ ≤ ((2 : ℝ) ^ (3 * (n + 1)))⁻¹) :
    q (n + 1) (ofEntire h hh - ofEntire k hk) ≤ (1 / 4 : ℝ) ^ (n + 1) := by
  rw [← ofEntire_prefixProjection k hk, ← ofEntire_sub]
  exact q_ofEntire_stage_le (Nat.succ_pos n) _ _ hbound

end AutomaticContinuity.FiniteTaylor
