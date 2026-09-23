import AutomaticContinuity.RectangleAdditiveSplitting
import AutomaticContinuity.EuclideanBallGeometry

set_option autoImplicit false

/-! # Rectangular additive splitting with the specified Euclidean pair norm

The factor two is the explicit conversion from the default product norm used
by the Banach-valued contour integral to `euclideanPairNorm`.
-/

namespace AutomaticContinuity.RectangleCauchy

open Set

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

theorem exists_euclidean_bounded_additive_split
    {a b c d s t l r v w δ M : ℝ}
    (hbc : b ≤ c) (hst : s ≤ t) (hδ : 0 < δ)
    (hl : l + δ ≤ b) (hr : c + δ ≤ r)
    (hv : v + δ ≤ s) (hw : t + δ ≤ w) (hM : 0 ≤ M)
    {f : P × ℂ → ℂ × ℂ} {V : Set (P × ℂ)} {O K : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r v w ⊆ V)
    (hbound : ∀ p ∈ K, ∀ z ∈ closedRectangle l r v w,
      euclideanPairNorm (f (p,z)) ≤ M) :
    ∃ alpha beta : P × ℂ → ℂ × ℂ,
      DifferentiableOn ℂ alpha (O ×ˢ rightDomain r v w) ∧
      DifferentiableOn ℂ beta (O ×ˢ leftDomain l) ∧
      (∀ p ∈ O, ∀ z ∈ closedRectangle b c s t, beta (p,z) - alpha (p,z) = f (p,z)) ∧
      (∀ p ∈ K, ∀ z ∈ closedRectangle a c s t,
        euclideanPairNorm (alpha (p,z)) ≤ 2*((2*|r-l|+|w-v|)/(2*Real.pi*δ))*M) ∧
      (∀ p ∈ K, ∀ z ∈ closedRectangle b d s t,
        euclideanPairNorm (beta (p,z)) ≤ 2*((2*|r-l|+|w-v|)/(2*Real.pi*δ))*M) := by
  obtain ⟨alpha,beta,hα,hβ,hs,ha,hb⟩ := exists_bounded_additive_split
    (a := a) (d := d) hbc hst hδ hl hr hv hw hM hV hf hO hrect
    (fun p hp z hz ↦ (norm_le_euclideanPairNorm _).trans (hbound p hp z hz))
  refine ⟨alpha,beta,hα,hβ,hs,?_,?_⟩
  · intro p hp z hz
    exact (euclideanPairNorm_le_two_mul_norm _).trans (by nlinarith [ha p hp z hz])
  · intro p hp z hz
    exact (euclideanPairNorm_le_two_mul_norm _).trans (by nlinarith [hb p hp z hz])

end AutomaticContinuity.RectangleCauchy
