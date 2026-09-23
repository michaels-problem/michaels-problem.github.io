import AutomaticContinuity.LocalFlagInterpolation
import AutomaticContinuity.LocalPointInterpolation

/-!
# The one-dimensional flag approximation theorem

In dimension one the sole positive flag is the point with coordinate `4`.
Polynomial approximation with exact interpolation at that point suffices. When
the point lies inside the approximation disc we use its constant projection;
when it lies outside, a polynomial peak corrects the value with arbitrarily
small error on the disc. This proves precisely the dimension-one specialization
of `FiniteFlagApproximationStatement`, for every nonnegative radius, without
asserting any higher-dimensional flag-avoidance approximation theorem.
-/

noncomputable section

namespace AutomaticContinuity

open Set

/-- Entire approximation on a one-dimensional polydisc while preserving the
value at the prescribed point exactly, whether that point is inside or outside. -/
theorem exists_entire_pair_approx_matching_prescribedPoint_one {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (h : FinitePoint 1 → ℂ × ℂ)
    {U : Set (FinitePoint 1)} (hU : IsOpen U) (hKU : polydisc 1 R ⊆ U)
    (hh : DifferentiableOn ℂ h U) :
    ∃ H : FinitePoint 1 → ℂ × ℂ,
      Differentiable ℂ H ∧ H (prescribedPoint 1) = h (prescribedPoint 1) ∧
        ∀ z ∈ polydisc 1 R, euclideanPairNorm (H z - h z) < ε := by
  by_cases hp : prescribedPoint 1 ∈ polydisc 1 R
  · have hfour : 4 * (1 : ℝ) ≤ R := by
      have hp0 := hp (0 : Fin 1)
      simpa [prescribedPoint, norm_prescribedCoordinate] using hp0
    have hagree : EqOn h (fun _ => h (prescribedPoint 1)) (finiteFlag 1 1) := by
      intro z hz
      rw [finiteFlag_self] at hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      rfl
    obtain ⟨H, hH, hHflag, hHapprox⟩ := exists_entire_pair_approx_interpolating_flag
      hR hε (flagProjection_maps_polydisc_of_four_mul_le (by simpa using hfour))
      h (fun _ => h (prescribedPoint 1)) hU hKU hh
      (differentiable_const _) hagree
    exact ⟨H, hH, hHflag (prescribedPoint_mem_finiteFlag 1 1), hHapprox⟩
  · have hhalf : 0 < ε / 2 := by positivity
    obtain ⟨p, hpvalue, hpapprox⟩ :=
      FiniteCauchy.exists_polynomial_approx_interpolate_exterior
        hR (fun z => (h z).1) hU hKU hh.fst hhalf hp (h (prescribedPoint 1)).1
    obtain ⟨q, hqvalue, hqapprox⟩ :=
      FiniteCauchy.exists_polynomial_approx_interpolate_exterior
        hR (fun z => (h z).2) hU hKU hh.snd hhalf hp (h (prescribedPoint 1)).2
    refine ⟨fun z => (MvPolynomial.eval z p, MvPolynomial.eval z q),
      (differentiable_polynomial_eval p).prodMk (differentiable_polynomial_eval q),
      Prod.ext hpvalue hqvalue, ?_⟩
    intro z hz
    refine (euclideanPairNorm_le_sum _).trans_lt ?_
    change ‖MvPolynomial.eval z p - (h z).1‖ + ‖MvPolynomial.eval z q - (h z).2‖ < ε
    linarith [hpapprox z hz, hqapprox z hz]

/-- The exact dimension-one case of the remaining flag approximation input.
The global continuity assumption is retained to match that statement, although
local holomorphicity and the prescribed point value already suffice here. -/
theorem finiteFlagApproximation_one (R : ℝ) (hR : 0 ≤ R)
    (h : FinitePoint 1 → ℂ × ℂ) (_hh : Continuous h)
    (hlocal : ∃ U : Set (FinitePoint 1), IsOpen U ∧ polydisc 1 R ⊆ U ∧
      DifferentiableOn ℂ h U)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ 1 →
      ∀ z ∈ finiteFlag 1 k, (k : ℝ) < euclideanPairNorm (h z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : FinitePoint 1 → ℂ × ℂ,
      Differentiable ℂ H ∧
      (∀ z ∈ polydisc 1 R, euclideanPairNorm (H z - h z) < ε) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 1 →
        ∀ z ∈ finiteFlag 1 k, (k : ℝ) < euclideanPairNorm (H z)) := by
  obtain ⟨U, hU, hKU, hhU⟩ := hlocal
  obtain ⟨H, hH, hHvalue, hHapprox⟩ :=
    exists_entire_pair_approx_matching_prescribedPoint_one hR hε h hU hKU hhU
  refine ⟨H, hH, hHapprox, ?_⟩
  intro k hk hkn z hz
  have hk1 : k = 1 := by omega
  subst k
  rw [finiteFlag_self] at hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  rw [hHvalue]
  exact hb 1 le_rfl le_rfl (prescribedPoint 1) (prescribedPoint_mem_finiteFlag 1 1)

end AutomaticContinuity
