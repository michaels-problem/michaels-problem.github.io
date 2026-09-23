import AutomaticContinuity.FlagApproximationPath
import AutomaticContinuity.CompactFamilyInverseCoordinates

set_option autoImplicit false

/-!
# The actual inverse-family argument for openness of approximability

The sole analytic transfer premise says that every holomorphic parameter map
composed with the supplied family is approximable on the old compact. The
separate transfer assembly produces precisely this conclusion from scalar
two-piece approximation, bounded additive splitting, and buffered geometry.
The present file constructs inverse coordinates and proves local stability;
it does not assert that the transfer premise holds without those inputs.
-/

noncomputable section

namespace AutomaticContinuity.FlagSectionApproximation

open Set

def HolomorphicNear {n : ℕ} (K : Set (FinitePoint n)) (h : FinitePoint n → Pair) : Prop :=
  ∃ U : Set (FinitePoint n), IsOpen U ∧ K ⊆ U ∧ DifferentiableOn ℂ h U

/-- The concrete transfer property used in the inverse-family openness
argument. This is a named premise, not an asserted approximation theorem. -/
def ApproximableCompositions {n : ℕ} (K L : Set (FinitePoint n))
    (G : FinitePoint n × Pair → Pair) : Prop :=
  ∀ φ : FinitePoint n → Pair, HolomorphicNear K φ →
    Approximable K L (fun z => G (z, φ z))

/-- A genuine holomorphic inverse on an open graph neighbourhood gives
uniform stability of approximability from the explicit composition input. -/
theorem exists_approximation_tolerance_of_open_image {n : ℕ}
    {K L : Set (FinitePoint n)} (hK : IsCompact K)
    (h : FinitePoint n → Pair) (hh : ContinuousOn h K)
    {Ω : Set (FinitePoint n × Pair)} (hΩ : IsOpen Ω)
    (hgraph : ∀ z ∈ K, (z, h z) ∈ Ω)
    (F G : FinitePoint n × Pair → Pair)
    (hF : DifferentiableOn ℂ F Ω) (hFzero : ∀ z ∈ K, F (z, h z) = 0)
    (hGF : ∀ z ∈ Ω, G (z.1, F z) = z.2)
    (hcompose : ApproximableCompositions K L G) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : FinitePoint n → Pair,
      HolomorphicNear K u →
      (∀ z ∈ K, euclideanPairNorm (u z - h z) ≤ δ) → Approximable K L u := by
  obtain ⟨δ, hδ, hcontrol⟩ := CompactFamilyInverseCoordinates.exists_uniform_inverse_tolerance
    hK h hh hΩ hgraph F hF.continuousOn hFzero (by norm_num : (0 : ℝ) < 1)
  refine ⟨δ, hδ, ?_⟩
  intro u hu hclose
  obtain ⟨U, hU, hKU, hu⟩ := hu
  have hugraph : ∀ z ∈ K, (z, u z) ∈ Ω := fun z hz => (hcontrol z hz (u z) (hclose z hz)).1
  obtain ⟨V, hV, hKV, _hVU, _hVgraph, hcoords⟩ :=
    CompactFamilyInverseCoordinates.exists_coordinate_neighbourhood hU hKU hΩ F u hF hu hugraph
  have happ := hcompose (CompactFamilyInverseCoordinates.coordinates F u) ⟨V, hV, hKV, hcoords⟩
  apply happ.congr
  intro z hz
  exact hGF (z, u z) (hugraph z hz)

/-- Openness along a compact continuous path follows from the displayed local
stability assertion at each already approximable time. The latter is the
conclusion of the inverse-family theorem above, after analytic transfer. -/
theorem openAlongPath_of_local_stability {n : ℕ} {K L : Set (FinitePoint n)}
    (hK : IsCompact K) (H : ℝ × FinitePoint n → Pair)
    (hH : ContinuousOn H (Icc 0 1 ×ˢ K))
    (hhol : ∀ t : Time, HolomorphicNear K (fun z => H (t.val, z)))
    (hstable : ∀ t : Time, Approximable K L (fun z => H (t.val, z)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ u : FinitePoint n → Pair,
        HolomorphicNear K u →
        (∀ z ∈ K, euclideanPairNorm (u z - H (t.val, z)) ≤ δ) → Approximable K L u) :
    OpenAlongPath K L H := by
  have hfamily := uniformFamily_of_continuous_path hK H hH
  apply Metric.isOpen_iff.mpr
  intro t ht
  obtain ⟨δ, hδ, htransfer⟩ := hstable t ht
  obtain ⟨r, hr, hcontrol⟩ := hfamily t δ hδ
  refine ⟨r, hr, ?_⟩
  intro s hs
  exact htransfer (fun z => H (s.val, z)) (hhol s) (fun z hz => (hcontrol s hs z hz).le)

end AutomaticContinuity.FlagSectionApproximation
