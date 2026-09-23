import AutomaticContinuity.CoordinateCutConvexity
import AutomaticContinuity.FlagRectangleSplitting
import AutomaticContinuity.FlagApproximationComposition
import AutomaticContinuity.SeparatedConvexParameterApproximation

set_option autoImplicit false

/-!
# Approximation transfer with both analytic inputs discharged

Only concrete buffered source geometry and actual holomorphic section/family
data remain in the hypotheses. Polynomial approximation on the two separated
convex sets and bounded contour splitting are proved dependencies.
-/

noncomputable section

namespace AutomaticContinuity.FlagApproximationTransfer

open Set FlagTotalSpace FlagSectionApproximation RectangleCauchy

variable {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b₀ : ℝ)

local notation "e" => CoordinateCutChart.homeomorph j a ha b₀

theorem approximableCompositions_of_coordinate_rectangle
    {K L U V W : Set (FinitePoint n)}
    (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKcut : ∀ z ∈ K, (a * z j).re ≤ b₀)
    {O D : Set (CoordinateCutChart.Remaining j)}
    (hO : IsOpen O) (hOD : O ⊆ D) (hD : IsCompact D) (hDconv : Convex ℝ D)
    {left right : Set ℂ} (hleft : IsOpen left) (hright : IsOpen right)
    {l r b t δ : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hbt : b < t) (hδ : 0 < δ)
    (hoverlap : left ∩ right ⊆ openRectangle l r b t)
    (hgapL : ∀ z ∈ left, ∀ ζ ∈ rightContour l r b t, δ ≤ ‖ζ-z‖)
    (hgapR : ∀ z ∈ right, ∀ ζ ∈ leftContour l b t, δ ≤ ‖ζ-z‖)
    (hLAB : L ⊆ e ⁻¹' (O ×ˢ right) ∪ e ⁻¹' (O ×ˢ left))
    (hKB : K ⊆ e ⁻¹' (O ×ˢ left))
    (hAU : e ⁻¹' (O ×ˢ right) ⊆ U) (hBV : e ⁻¹' (O ×ˢ left) ⊆ V)
    (hCV : e ⁻¹' (D ×ˢ closedRectangle l r b t) ⊆ V)
    (hV : IsOpen V) (hW : IsOpen W) (hWU : W ⊆ U) (hWV : W ⊆ V)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ (e).symm ⁻¹' W)
    (g θ : FinitePoint n → Pair) (G : FinitePoint n × Pair → Pair)
    (hg : DifferentiableOn ℂ g U) (hG : DifferentiableOn ℂ G (V ×ˢ univ))
    (hθ : DifferentiableOn ℂ θ V) (hθeq : ∀ z ∈ V, G (z, θ z) = g z)
    {δA δB : ℝ} (hδA : 0 < δA) (hδB : 0 < δB)
    (hmarginA : ∀ z ∈ U, ∀ u : Pair, euclideanPairNorm u ≤ δA →
      (z, g z + u) ∈ totalSet n)
    (hmarginB : ∀ z ∈ V, ∀ s u : Pair, euclideanPairNorm u ≤ δB →
      (z, G (z, s) + u) ∈ totalSet n) : ApproximableCompositions K L G := by
  let C := e ⁻¹' (D ×ˢ closedRectangle l r b t)
  have hC : IsCompact C := (e).isCompact_preimage.mpr
    (hD.prod (isCompact_Icc.reProdIm isCompact_Icc))
  have hCconv : Convex ℝ C := CoordinateCutChart.convex_preimage j a ha b₀
    (hDconv.prod (CoordinateCutChart.convex_closedRectangle l r b t))
  have hM : 0 < 2 * ((2*|r-l|+|t-b|)/(2*Real.pi*δ)) := by
    have hpos : 0 < |t-b| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hbt))
    positivity
  apply approximableCompositions_of_transfer_data hK hC
    ((hO.prod hright).preimage (e).continuous) ((hO.prod hleft).preimage (e).continuous)
    hV hLAB hKB hAU hBV hCV hWU hWV g θ G hg hG
    (hθ.continuousOn.mono hCV) (fun z hz => hθeq z (hCV hz)) hδA hδB hM
    (fun z hz => hmarginA z (hAU hz)) (fun z hz => hmarginB z (hBV hz))
  · intro φ hφ
    obtain ⟨Z, hZ, hKZ, hφZ⟩ := hφ
    apply SeparatedCapPolynomialGluing.parameterApproximation_of_separated_convex
      hK hC hKconv hCconv hZ hV hKZ hCV j a (show b₀ < b₀+l by linarith)
      hKcut _ φ θ hφZ hθ
    intro z hz
    have hzre : l ≤ (e z).2.re := hz.2.1.1
    change l ≤ ((CoordinateCutChart.chart j a ha b₀ z).2).re at hzre
    rw [CoordinateCutChart.second_re] at hzre
    linarith
  · exact boundedSplitting_of_rectangle e
      (CoordinateCutChart.differentiable_chart j a ha b₀)
      (CoordinateCutChart.differentiable_chart_symm j a ha b₀)
      hO hOD hlr hbt.le hδ hoverlap hgapL hgapR hW hrect

end AutomaticContinuity.FlagApproximationTransfer
