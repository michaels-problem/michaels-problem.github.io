import AutomaticContinuity.FlagPolynomialPush
import AutomaticContinuity.RadialPolynomialExpulsion

set_option autoImplicit false

/-!
# Expelling the original compact obstacle beyond an arbitrary radius

The map fixes the actual section and controls its actual inverse near that
section. A compact bound on the section converts centered radial expulsion
to expulsion in the original target coordinates.
-/

noncomputable section

namespace AutomaticContinuity.FlagPolynomialPush

open Set FlagPolynomialSeparation FlagCenteredSeparator CenteredPolynomialFamily
open FlagTotalSpace

theorem exists_centered_expelling_push {n : ℕ} (q : Polynomial n) (h : FinitePoint n → Pair)
    {L U : Set (FinitePoint n)} {K : Set (Point n)} {ε : ℝ} (r : ℝ)
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ) (hh : DifferentiableOn ℂ h U)
    (hgraph : ∀ p ∈ L, ‖evaluate (p, h p) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖evaluate z q - 1‖ ≤ 1 / 32) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : FinitePoint n → Pair ≃ₜ Pair,
      (∀ p, Φ p 0 = 0) ∧
      DifferentiableOn ℂ (fun z : Point n => Φ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : Point n => (Φ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ z ∈ L ×ˢ closedEuclideanBall a,
        euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
        euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
      (∀ z ∈ centeredObstacle h K, r < euclideanPairNorm (Φ z.1 z.2)) := by
  obtain ⟨a, ha, hKc, hKbase, hzero, hone, _⟩ :=
    exists_separator_data q h hL hK hU hLU hKL hh.continuousOn hgraph hobstacle
  obtain ⟨Φ, hΦ⟩ := RadialPolynomialPush.exists_expelling_push (polynomial q h) q.totalDegree r
    hL hKc hU hLU hKbase ha hε (holomorphicCoefficientsOn_polynomial q h hh)
    (fun p _ => totalDegree_polynomial_le q h p) hzero
    (fun z hz => (hone z hz).trans (by norm_num))
  exact ⟨a, ha, Φ, hΦ⟩

/-- An actual section-fixing fibre automorphism expels the original compact
obstacle beyond any prescribed Euclidean target radius, while both directions
remain uniformly close to the identity on a positive tube around the section. -/
theorem exists_section_expelling_push {n : ℕ} (q : Polynomial n) (h : FinitePoint n → Pair)
    {L U : Set (FinitePoint n)} {K : Set (Point n)} {ε : ℝ} (r : ℝ)
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ) (hh : DifferentiableOn ℂ h U)
    (hgraph : ∀ p ∈ L, ‖evaluate (p, h p) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖evaluate z q - 1‖ ≤ 1 / 32) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ Ψ : FinitePoint n → Pair ≃ₜ Pair,
      (∀ p, Ψ p (h p) = h p) ∧
      DifferentiableOn ℂ (fun z : Point n => Ψ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : Point n => (Ψ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ p ∈ L, ∀ w : Pair, euclideanPairNorm (w - h p) ≤ a →
        euclideanPairNorm (Ψ p w - w) < ε ∧ euclideanPairNorm ((Ψ p).symm w - w) < ε) ∧
      (∀ z ∈ K, r < euclideanPairNorm (Ψ z.1 z.2)) := by
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn (hh.continuousOn.mono hLU)
  let B : ℝ := 2 * max M 0
  have hb : ∀ p ∈ L, euclideanPairNorm (h p) ≤ B := by
    intro p hp
    exact (euclideanPairNorm_le_two_mul_norm _).trans
      (mul_le_mul_of_nonneg_left ((hM p hp).trans (le_max_left _ _)) (by norm_num))
  obtain ⟨a, ha, Φ, hfix, hhol, hholi, hprotected, hpush⟩ :=
    exists_centered_expelling_push q h (r + B) hL hK hU hLU hKL hh hgraph hobstacle hε
  refine ⟨a, ha, uncenter h Φ, uncenter_fixes_section h Φ hfix,
    differentiableOn_uncenter h Φ hh hhol, differentiableOn_uncenter_symm h Φ hh hholi,
    ?_, ?_⟩
  · intro p hp w hw
    simpa only [uncenter_error, uncenter_inverse_error] using
      hprotected (p, w - h p) ⟨hp, hw⟩
  · intro z hz
    have hr := hpush (centerMap h z) ⟨z, hz, rfl⟩
    have hhbound := hb z.1 (hKL hz).1
    have htriangle := euclideanPairNorm_add_le (uncenter h Φ z.1 z.2) (-h z.1)
    have heq : uncenter h Φ z.1 z.2 + -h z.1 = Φ z.1 (z.2 - h z.1) := by simp
    have hneg : euclideanPairNorm (-h z.1) = euclideanPairNorm (h z.1) := by
      simp [euclideanPairNorm]
    rw [heq, hneg] at htriangle
    change r + B < euclideanPairNorm (Φ z.1 (z.2 - h z.1)) at hr
    linarith

end AutomaticContinuity.FlagPolynomialPush
