import AutomaticContinuity.FlagObstaclePush

set_option autoImplicit false

/-!
# One fixed protected tube for all target radii and errors

The separator and the protected radius are chosen before the target radius
or approximation error. This order of quantifiers retains the uniform
geometric input needed by subsequent iterative constructions.
-/

noncomputable section

namespace AutomaticContinuity.FlagObstaclePush

open Set FlagPolynomialSeparation FlagTotalSpace FlagCenteredSeparator
open CenteredPolynomialFamily FlagPolynomialPush

/-- The protected tube depends only on the initial admissible section and
compact forbidden graph. Target radius and error are arbitrary afterwards. -/
theorem exists_fixed_tube_forbidden_graph_push {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ totalSet n) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ε : ℝ, 0 < ε →
      ∃ Ψ : FinitePoint n → Pair ≃ₜ Pair,
        (∀ p, Ψ p (h p) = h p) ∧
        DifferentiableOn ℂ (fun z : Point n => Ψ z.1 z.2) (U ×ˢ univ) ∧
        DifferentiableOn ℂ (fun z : Point n => (Ψ z.1).symm z.2) (U ×ˢ univ) ∧
        (∀ p ∈ polydisc n R, ∀ w : Pair, euclideanPairNorm (w - h p) ≤ a →
          euclideanPairNorm (Ψ p w - w) < ε ∧ euclideanPairNorm ((Ψ p).symm w - w) < ε) ∧
        (∀ z ∈ compactForbiddenGraph n R, r < euclideanPairNorm (Ψ z.1 z.2)) := by
  obtain ⟨q, hqgraph, hqobstacle⟩ := FlagGraphCutoff.exists_forbidden_graph_separator
    hR h hU hKU hh hadm (by norm_num : (0 : ℝ) < 1 / 32)
  have hL := isCompact_polydisc n hR
  have hK := isCompact_compactForbiddenGraph n hR
  have hbase : compactForbiddenGraph n R ⊆ polydisc n R ×ˢ univ :=
    fun z hz => ⟨(mem_compactForbiddenGraph_iff.mp hz).1, mem_univ _⟩
  obtain ⟨a, ha, hKc, hKbase, hzero, hone, _⟩ := exists_separator_data q h hL hK hU hKU hbase
    hh.continuousOn (fun p hp => (hqgraph p hp).le) (fun z hz => (hqobstacle z hz).le)
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hh.continuousOn.mono hKU)
  let B : ℝ := 2 * max M 0
  have hb : ∀ p ∈ polydisc n R, euclideanPairNorm (h p) ≤ B := by
    intro p hp
    exact (euclideanPairNorm_le_two_mul_norm _).trans
      (mul_le_mul_of_nonneg_left ((hM p hp).trans (le_max_left _ _)) (by norm_num))
  refine ⟨a, ha, ?_⟩
  intro r ε hε
  obtain ⟨Φ, hfix, hhol, hholi, hprotected, hpush⟩ :=
    RadialPolynomialPush.exists_expelling_push (polynomial q h) q.totalDegree (r + B)
      hL hKc hU hKU hKbase ha hε (holomorphicCoefficientsOn_polynomial q h hh)
      (fun p _ => totalDegree_polynomial_le q h p) hzero
      (fun z hz => (hone z hz).trans (by norm_num))
  refine ⟨uncenter h Φ, uncenter_fixes_section h Φ hfix,
    differentiableOn_uncenter h Φ hh hhol, differentiableOn_uncenter_symm h Φ hh hholi,
    ?_, ?_⟩
  · intro p hp w hw
    simpa only [uncenter_error, uncenter_inverse_error] using
      hprotected (p, w - h p) ⟨hp, hw⟩
  · intro z hz
    have hr := hpush (centerMap h z) ⟨z, hz, rfl⟩
    have hhbound := hb z.1 (hbase hz).1
    have htriangle := euclideanPairNorm_add_le (uncenter h Φ z.1 z.2) (-h z.1)
    have heq : uncenter h Φ z.1 z.2 + -h z.1 = Φ z.1 (z.2 - h z.1) := by simp
    have hneg : euclideanPairNorm (-h z.1) = euclideanPairNorm (h z.1) := by
      simp [euclideanPairNorm]
    rw [heq, hneg] at htriangle
    change r + B < euclideanPairNorm (Φ z.1 (z.2 - h z.1)) at hr
    linarith

end AutomaticContinuity.FlagObstaclePush
