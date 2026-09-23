import AutomaticContinuity.FiniteCauchySeries
import AutomaticContinuity.OneVariableCauchy
import AutomaticContinuity.FiniteCauchySummation

/-!
# Expansion of an entire finite-dimensional function

The proof inducts on the number of variables. At each step a uniformly
summable geometric majorant justifies integrating the series in the remaining
variables; the one-variable Cauchy expansion supplies the initial coordinate.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set
open scoped BigOperators Real

private theorem circleCoeff_mul_const (R : ℝ) (m : ℕ) (c : ℂ) (h : ℂ → ℂ) :
    circleCoeff R m (fun z => h z * c) = circleCoeff R m h * c := by
  simpa only [mul_comm] using circleCoeff_const_mul R m c h

/-- The half-polydisc expansion with an explicit uniform bound, which is also
the majorant used in the inductive summation argument. -/
theorem hasSum_coefficient_mul_monomial_of_bound {n : ℕ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h)
    (hbound : ∀ w ∈ polydisc n (2 * r), ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) :
    HasSum (fun α => coefficient (fun _ => 2 * r) h α * monomial z α) (h z) := by
  induction n with
  | zero =>
      have heq : h Fin.elim0 = h z := congrArg h (Subsingleton.elim _ _)
      simp [coefficient, monomial, heq]
  | succ n ih =>
      have hr2 : 0 < 2 * r := by positivity
      have hz0 : ‖z 0‖ < 2 * r := (hz 0).trans_lt (by linarith)
      have hzTail : Fin.tail z ∈ polydisc n r := fun j => hz j.succ
      let b : FiniteMultiIndex n → ℂ → ℂ := fun β ζ =>
        coefficient (fun _ => 2 * r) (fun w => h (Fin.cons ζ w)) β *
          monomial (Fin.tail z) β
      let g : ℂ → ℂ := fun ζ => h (Fin.cons ζ (Fin.tail z))
      have hbcont (β : FiniteMultiIndex n) : Continuous (b β) :=
        (continuous_coefficient (fun _ => 2 * r) (fun _ => hr2)
          (fun ζ w => h (Fin.cons ζ w))
          (hh.continuous.comp
            (continuous_fst.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_snd)) β).mul_const _
      have hsliceBound (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) (2 * r)) :
          ∀ w ∈ polydisc n (2 * r), ‖h (Fin.cons ζ w)‖ ≤ M := by
        intro w hw
        apply hbound (Fin.cons ζ w)
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · have heq : ‖ζ‖ = 2 * r := by simpa only [mem_sphere, dist_zero_right] using hζ
          exact heq.le
        · exact hw j
      have hbBound (β : FiniteMultiIndex n) (ζ : ℂ)
          (hζ : ζ ∈ sphere (0 : ℂ) (2 * r)) :
          ‖b β ζ‖ ≤ M * (1 / 2 : ℝ) ^ finiteTotalDegree β :=
        norm_coefficient_mul_monomial_le hr _ (hsliceBound ζ hζ) _ hzTail β
      have hbSum (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) (2 * r)) :
          HasSum (fun β => b β ζ) (g ζ) := by
        apply ih (fun w => h (Fin.cons ζ w))
          (hh.comp ((differentiable_const ζ).finCons differentiable_id))
          (hsliceBound ζ hζ) (Fin.tail z) hzTail
      have hsumIntegral := hasSum_cauchyIntegral_of_summable_bound hr2 hz0 b g hbcont
        (fun β => M * (1 / 2 : ℝ) ^ finiteTotalDegree β)
        ((summable_half_pow_finiteTotalDegree n).mul_left M)
        (fun β => mul_nonneg hM (pow_nonneg (by norm_num) _)) hbBound hbSum
      have hg : Differentiable ℂ g := by
        apply hh.comp
        apply differentiable_pi.mpr
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · change Differentiable ℂ (fun ζ : ℂ => ζ)
          exact differentiable_id
        · simpa only [Fin.cons_succ] using
            (differentiable_const (Fin.tail z j) :
              Differentiable ℂ (fun _ : ℂ => Fin.tail z j))
      have hintegral :
          ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, 2 * r), g ζ / (ζ - z 0)) = h z := by
        have hgeneric := OneVariableCauchy.hasSum_circleCoeff_mul_pow_integral_of_continuousOn
          hg.continuous.continuousOn hz0
        have hentire := OneVariableCauchy.hasSum_circleCoeff_mul_pow hg hr2 (z 0)
        convert hgeneric.unique hentire using 1
        simp [g]
      rw [hintegral] at hsumIntegral
      let e : (FiniteMultiIndex n × ℕ) ≃ FiniteMultiIndex (n + 1) :=
        (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))
      let t : FiniteMultiIndex (n + 1) → ℂ :=
        fun α => coefficient (fun _ => 2 * r) h α * monomial z α
      have hs : Summable (fun p : FiniteMultiIndex n × ℕ => t (e p)) :=
        (e.summable_iff (f := t)).mpr (summable_coefficient_mul_monomial hr h hbound z hz)
      have hrow (β : FiniteMultiIndex n) :
          HasSum (fun m => t (e (β, m)))
            ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, 2 * r), b β ζ / (ζ - z 0)) := by
        have hgeneric := OneVariableCauchy.hasSum_circleCoeff_mul_pow_integral_of_continuousOn
          (hbcont β).continuousOn hz0
        convert hgeneric using 1
        funext m
        change coefficient (fun _ => 2 * r) h (Fin.cons m β) *
          monomial z (Fin.cons m β) = circleCoeff (2 * r) m (b β) * z 0 ^ m
        rw [monomial_cons]
        change (circleCoeff (2 * r) m (fun ζ =>
          coefficient (fun _ => 2 * r) (fun w => h (Fin.cons ζ w)) β)) *
            (z 0 ^ m * monomial (Fin.tail z) β) =
          circleCoeff (2 * r) m (fun ζ =>
            coefficient (fun _ => 2 * r) (fun w => h (Fin.cons ζ w)) β *
              monomial (Fin.tail z) β) * z 0 ^ m
        rw [circleCoeff_mul_const]
        ring
      have heq := (hs.hasSum.prod_fiberwise hrow).unique hsumIntegral
      apply (e.hasSum_iff (f := t)).mp
      exact heq ▸ hs.hasSum

/-- Every entire scalar function equals its finite contour coefficient series
on the half-polydisc. The coefficients are actual iterated contour integrals. -/
theorem hasSum_coefficient_mul_monomial {n : ℕ} (h : FinitePoint n → ℂ)
    (hh : Differentiable ℂ h) {R : ℝ} (hR : 0 < R)
    (z : FinitePoint n) (hz : z ∈ polydisc n (R / 2)) :
    HasSum (fun α => coefficient (fun _ => R) h α * monomial z α) (h z) := by
  obtain ⟨M, hM⟩ := ((isCompact_polydisc n hR.le).image hh.continuous.norm).bddAbove
  have htwo : 2 * (R / 2) = R := by ring
  have hbound : ∀ w ∈ polydisc n (2 * (R / 2)), ‖h w‖ ≤ max M 0 := by
    intro w hw
    have hw' : w ∈ polydisc n R := by simpa only [htwo] using hw
    exact (hM ⟨w, hw', rfl⟩).trans (le_max_left _ _)
  simpa only [htwo] using
    hasSum_coefficient_mul_monomial_of_bound (div_pos hR (by norm_num))
      (le_max_right M 0) h hh hbound z hz

end AutomaticContinuity.FiniteCauchy
