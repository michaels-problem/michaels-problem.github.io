import AutomaticContinuity.CoordinateCutChart

set_option autoImplicit false

/-!
# Actual contour splitting in source coordinates

The right cap carries the old extending section and the left cap carries the
entire-fibre family. The norm constant is the proved contour bound, including
the conversion to the Euclidean pair norm. The transverse output window must
lie in the transverse set on which the input is uniformly bounded.
-/

noncomputable section

namespace AutomaticContinuity.FlagApproximationTransfer

open Set RectangleCauchy

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

theorem boundedSplitting_of_rectangle {n : ℕ}
    (e : FinitePoint n ≃ₜ P × ℂ)
    (he : Differentiable ℂ e) (hei : Differentiable ℂ e.symm)
    {O D : Set P} (hO : IsOpen O) (hOD : O ⊆ D)
    {left right : Set ℂ} {l r b t δ : ℝ}
    (hlr : l ≤ r) (hbt : b ≤ t) (hδ : 0 < δ)
    (hoverlap : left ∩ right ⊆ openRectangle l r b t)
    (hgapL : ∀ z ∈ left, ∀ ζ ∈ rightContour l r b t, δ ≤ ‖ζ-z‖)
    (hgapR : ∀ z ∈ right, ∀ ζ ∈ leftContour l b t, δ ≤ ‖ζ-z‖)
    {W : Set (FinitePoint n)} (hW : IsOpen W)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ e.symm ⁻¹' W) :
    BoundedSplitting (e ⁻¹' (O ×ˢ right)) (e ⁻¹' (O ×ˢ left)) W
      (e ⁻¹' (D ×ˢ closedRectangle l r b t))
      (2 * ((2*|r-l|+|t-b|)/(2*Real.pi*δ))) := by
  intro c hc η hη hbound
  have hc' : DifferentiableOn ℂ (fun q : P × ℂ => c (e.symm q)) (e.symm ⁻¹' W) :=
    hc.comp hei.differentiableOn (fun _ h => h)
  obtain ⟨alpha, beta, hleft, hright, hα, hβ, hsplit, hbα, hbβ⟩ :=
    exists_bounded_additive_split_of_contour_separation hlr hbt hδ hη.le
      hoverlap hgapL hgapR (hW.preimage e.symm.continuous) hc' hO hrect
      (K := D) (fun p hp z hz => (norm_le_euclideanPairNorm _).trans
        (hbound (e.symm (p,z)) (by simpa using And.intro hp hz)).le)
  refine ⟨(fun z => beta (e z)), (fun z => alpha (e z)), ?_, ?_, ?_, ?_, ?_⟩
  · exact hβ.comp he.differentiableOn (fun z hz => ⟨hz.1, hright hz.2⟩)
  · exact hα.comp he.differentiableOn (fun z hz => ⟨hz.1, hleft hz.2⟩)
  · intro z hz
    have hs := hsplit (e z).1 hz.1.1 (e z).2 ⟨hz.2.2, hz.1.2⟩
    simpa using hs.symm
  · intro z hz
    have h := hbβ (e z).1 (hOD hz.1) (e z).2 hz.2
    exact (euclideanPairNorm_le_two_mul_norm _).trans (by nlinarith)
  · intro z hz
    have h := hbα (e z).1 (hOD hz.1) (e z).2 hz.2
    exact (euclideanPairNorm_le_two_mul_norm _).trans (by nlinarith)

end AutomaticContinuity.FlagApproximationTransfer
