import AutomaticContinuity.BallComplementEmbeddings
import AutomaticContinuity.OneChartApproximation

/-!
# A proved local target domain with global ball-avoiding approximation

For every exterior point the explicit Hénon construction supplies one open
target neighborhood. Every map whose compact polydisc image lies in this same
neighborhood admits entire approximation avoiding the ball everywhere.

The compact image condition is essential here. No gluing between different
target neighborhoods, and no full convex approximation property, is asserted.
-/

namespace AutomaticContinuity.BallComplementOneChartApproximation

open Set

theorem exists_neighborhood_with_entire_approximation {r : ℝ} (hr : 0 < r)
    (p : ℂ × ℂ) (hp : r < euclideanPairNorm p) :
    ∃ Ω : Set (ℂ × ℂ), IsOpen Ω ∧ p ∈ Ω ∧
      (∀ v ∈ Ω, r < euclideanPairNorm v) ∧
      ∀ (n : ℕ) (R ε : ℝ), 0 ≤ R → 0 < ε →
        ∀ (f : FinitePoint n → ℂ × ℂ) (U : Set (FinitePoint n)),
          IsOpen U → polydisc n R ⊆ U → DifferentiableOn ℂ f U →
            MapsTo f (polydisc n R) Ω →
            ∃ g : FinitePoint n → ℂ × ℂ, Differentiable ℂ g ∧
              (∀ z, r < euclideanPairNorm (g z)) ∧
              ∀ z ∈ polydisc n R, euclideanPairNorm (g z - f z) < ε := by
  obtain ⟨Ω, hΩ, hpΩ, hout, H, h, hh, hHeq, hInv⟩ :=
    BallComplementEmbeddings.exists_biholomorphic_domain hr p hp
  refine ⟨Ω, hΩ, hpΩ, hout, ?_⟩
  intro n R ε hR hε f U hU hKU hf hfΩ
  obtain ⟨g, hg, hgΩ, hgapprox⟩ := OneChartApproximation.exists_entire_approx_in_one_chart
    hR hε hΩ H h hh hHeq hInv f hU hKU hf hfΩ
  exact ⟨g, hg, fun z => hout (g z) (hgΩ z), hgapprox⟩

end AutomaticContinuity.BallComplementOneChartApproximation
