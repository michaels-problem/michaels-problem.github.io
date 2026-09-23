import AutomaticContinuity.CompactBaseFlagMargin
import AutomaticContinuity.AdaptiveInverseControl

set_option autoImplicit false

/-!
# Uniform inverse coordinates for sections near a compact graph

The open image and inverse are actual outputs of the compact-base family.
Compactness chooses one neighbourhood tolerance before any new section is
supplied. A holomorphic new section then has inverse coordinates holomorphic
on an explicit open neighbourhood of the compact set.
-/

noncomputable section

namespace AutomaticContinuity.CompactFamilyInverseCoordinates

open Set

abbrev Pair := ℂ × ℂ

theorem exists_uniform_inverse_tolerance {P : Type*} [PseudoMetricSpace P]
    {K : Set P} (hK : IsCompact K) (h : P → Pair) (hh : ContinuousOn h K)
    {Ω : Set (P × Pair)} (hΩ : IsOpen Ω)
    (hgraph : ∀ p ∈ K, (p, h p) ∈ Ω) (F : P × Pair → Pair)
    (hF : ContinuousOn F Ω) (hFzero : ∀ p ∈ K, F (p, h p) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K, ∀ v : Pair,
      euclideanPairNorm (v - h p) ≤ δ →
      (p, v) ∈ Ω ∧ euclideanPairNorm (F (p, v)) < ε := by
  have hc : IsCompact ((fun p => (p, h p)) '' K) :=
    hK.image_of_continuousOn (continuousOn_id.prodMk hh)
  have hcΩ : (fun p => (p, h p)) '' K ⊆ Ω := by
    rintro _ ⟨p, hp, rfl⟩
    exact hgraph p hp
  obtain ⟨δ, hδ, hcontrol⟩ := AdaptiveInverseControl.exists_control_on_compact
    F hc hΩ hcΩ hF (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro p hp v hv
  have hd : dist (p, v) (p, h p) ≤ δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact (norm_le_euclideanPairNorm _).trans hv
  obtain ⟨hmem, herr⟩ := hcontrol (p, h p) ⟨p, hp, rfl⟩ (p, v) hd
  rw [hFzero p hp, dist_zero_right] at herr
  exact ⟨hmem, (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

def coordinates (F : P × Pair → Pair) (f : P → Pair) (p : P) : Pair := F (p, f p)

theorem differentiableOn_coordinates {V : Set P} {Ω : Set (P × Pair)}
    (F : P × Pair → Pair) (f : P → Pair) (hF : DifferentiableOn ℂ F Ω)
    (hf : DifferentiableOn ℂ f V) (hgraph : ∀ p ∈ V, (p, f p) ∈ Ω) :
    DifferentiableOn ℂ (coordinates F f) V :=
  hF.comp (differentiableOn_id.prodMk hf) hgraph

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
theorem reconstructed {V : Set P} {Ω : Set (P × Pair)}
    (F G : P × Pair → Pair) (f : P → Pair)
    (hGF : ∀ z ∈ Ω, G (z.1, F z) = z.2)
    (hgraph : ∀ p ∈ V, (p, f p) ∈ Ω) :
    ∀ p ∈ V, G (p, coordinates F f p) = f p :=
  fun p hp => hGF (p, f p) (hgraph p hp)

/-- Holomorphic inverse coordinates live on a genuine open neighbourhood,
obtained by the graph preimage of the family's actual open image. -/
theorem exists_coordinate_neighbourhood {K U : Set P} {Ω : Set (P × Pair)}
    (hU : IsOpen U) (hKU : K ⊆ U) (hΩ : IsOpen Ω)
    (F : P × Pair → Pair) (f : P → Pair)
    (hF : DifferentiableOn ℂ F Ω) (hf : DifferentiableOn ℂ f U)
    (hgraph : ∀ p ∈ K, (p, f p) ∈ Ω) :
    ∃ V : Set P, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, (p, f p) ∈ Ω) ∧ DifferentiableOn ℂ (coordinates F f) V := by
  let V : Set P := U ∩ (fun p => (p, f p)) ⁻¹' Ω
  have hV : IsOpen V :=
    (continuousOn_id.prodMk hf.continuousOn).isOpen_inter_preimage hU hΩ
  have hVU : V ⊆ U := inter_subset_left
  have hvgraph : ∀ p ∈ V, (p, f p) ∈ Ω := fun _ hp => hp.2
  exact ⟨V, hV, fun p hp => ⟨hKU hp, hgraph p hp⟩, hVU, hvgraph,
    differentiableOn_coordinates F f hF (hf.mono hVU) hvgraph⟩

end AutomaticContinuity.CompactFamilyInverseCoordinates
