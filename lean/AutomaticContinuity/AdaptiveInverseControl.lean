import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# Adaptive uniform control of cumulative inverse increments

A previously chosen continuous inverse has one positive tolerance on each
compact target set. Making the next actual inverse factor that close to
identity controls the increment of the actual cumulative inverse. No uniform
modulus over all previous stages, or already constructed infinite sequence,
is assumed.
-/

noncomputable section

namespace AutomaticContinuity.AdaptiveInverseControl

open Set Metric

theorem exists_control_on_compact {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (G : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hG : ContinuousOn G U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y, dist y x ≤ δ →
      y ∈ U ∧ dist (G y) (G x) < ε := by
  have hu := hK.uniformContinuousAt_of_continuousAt G
    (fun x hx => hG.continuousAt (hU.mem_nhds (hKU hx))) (dist_mem_uniformity hε)
  obtain ⟨r, hr, hcontrol⟩ := mem_uniformity_dist.mp hu
  obtain ⟨s, hs, hbuffer⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨min s (r / 2), lt_min hs (half_pos hr), ?_⟩
  intro x hx y hy
  constructor
  · exact hbuffer (mem_cthickening_of_dist_le y x s K hx (hy.trans (min_le_left _ _)))
  · have hxy : dist x y < r := by
      rw [dist_comm]
      exact (hy.trans (min_le_right _ _)).trans_lt (half_lt_self hr)
    have hh : dist (G x) (G y) < ε := hcontrol hxy hx
    simpa only [dist_comm] using hh

/-- One tolerance works for all fibre perturbations on the compact family.
Both the input displacement and output error are genuinely Euclidean. -/
theorem exists_euclidean_fiber_control {P : Type*} [PseudoMetricSpace P]
    (G : P × (ℂ × ℂ) → ℂ × ℂ) {K : Set (P × (ℂ × ℂ))} {U : Set P}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U ×ˢ univ)
    (hG : ContinuousOn G (U ×ˢ univ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ w : ℂ × ℂ,
      euclideanPairNorm (w - z.2) ≤ δ →
      euclideanPairNorm (G (z.1, w) - G z) < ε := by
  obtain ⟨δ, hδ, hb⟩ := exists_control_on_compact G hK (hU.prod isOpen_univ)
    hKU hG (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro z hz w hw
  have hd : dist (z.1, w) z ≤ δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, max_eq_right (dist_nonneg)]
    rw [dist_eq_norm]
    exact (norm_le_euclideanPairNorm (w - z.2)).trans hw
  have hh := (hb z hz (z.1, w) hd).2
  rw [dist_eq_norm] at hh
  exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)

/-- For any next actual fibre homeomorphism sufficiently close to identity
in its inverse, the actual inverse of the composed map changes uniformly
by less than the prescribed error. The tolerance is chosen before that map. -/
theorem exists_composed_inverse_increment {P : Type*} [PseudoMetricSpace P]
    (F : P → (ℂ × ℂ) ≃ₜ (ℂ × ℂ))
    {K : Set (P × (ℂ × ℂ))} {U : Set P}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U ×ˢ univ)
    (hF : ContinuousOn (fun z : P × (ℂ × ℂ) => (F z.1).symm z.2) (U ×ˢ univ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : P → (ℂ × ℂ) ≃ₜ (ℂ × ℂ),
      (∀ z ∈ K, euclideanPairNorm ((ψ z.1).symm z.2 - z.2) ≤ δ) →
      ∀ z ∈ K,
        euclideanPairNorm (((F z.1).trans (ψ z.1)).symm z.2 - (F z.1).symm z.2) < ε := by
  obtain ⟨δ, hδ, hb⟩ := exists_euclidean_fiber_control
    (fun z : P × (ℂ × ℂ) => (F z.1).symm z.2) hK hU hKU hF hε
  exact ⟨δ, hδ, fun ψ hψ z hz => hb z hz ((ψ z.1).symm z.2) (hψ z hz)⟩

end AutomaticContinuity.AdaptiveInverseControl
