import AutomaticContinuity.RadialPolynomialRealization
import AutomaticContinuity.PolynomialFamilyEvaluation
import AutomaticContinuity.FiberAutomorphismFamily

set_option autoImplicit false

/-!
# Compact radial push by actual polynomially generated automorphisms

The cutoff is a genuine polynomial in the two fibre variables with holomorphic
base coefficients and a common finite degree bound. Complete shear and
overshear flows discharge the realization premise. There is no assumed
automorphism approximation theorem in this endpoint.
-/

noncomputable section

namespace AutomaticContinuity.RadialPolynomialPush

open Set RadialPolynomialField RadialPolynomialFamily
open PolynomialFamilyRegularity (HolomorphicCoefficientsOn)

abbrev Pair := ℂ × ℂ

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

/-- A true finite composition of complete fibre flows performs the prescribed
compact radial push, with the actual inverse controlled on the same protected
cylinder and joint holomorphy only on the given open base domain. -/
theorem exists_compact_push (q : P → Poly) (D : ℕ)
    {L U : Set P} {K : Set (P × Pair)} {a c ε : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U) (hLU : L ⊆ U)
    (hKL : K ⊆ L ×ˢ univ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hq : HolomorphicCoefficientsOn q U)
    (hdegree : ∀ p ∈ U, (q p).totalDegree ≤ D)
    (hzero : ∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a, ‖value q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖value q z - 1‖ ≤ 1 / 16) :
    ∃ Φ : P → Pair ≃ₜ Pair,
      (∀ p, Φ p 0 = 0) ∧
      DifferentiableOn ℂ (fun z : P × Pair => Φ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : P × Pair => (Φ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a,
        euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
        euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
      (∀ z ∈ K, euclideanPairNorm (Φ z.1 z.2 - (1 + c) • z.2) < ε) := by
  have hcont : ContinuousOn (value q) (U ×ˢ univ) := by
    exact (PolynomialFamilyEvaluation.continuousOn_joint_eval D hdegree
      (fun α => (hq α).continuousOn)).mono (fun z hz => hz.1)
  exact RadialCompactPush.exists_compact_push (value q) hL hK hU hLU hKL hc hε
    hcont hzero hone (fun m => ⟨RadialPolynomialRealization.realization q D hc hq hdegree m⟩)

end AutomaticContinuity.RadialPolynomialPush
