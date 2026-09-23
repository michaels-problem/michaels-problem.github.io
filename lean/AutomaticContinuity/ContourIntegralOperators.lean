import AutomaticContinuity.FiniteHolomorphicRegularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

/-!
# Fixed-contour operators

The integration interval is fixed independently of the complex parameters.
Bounds are taken on the contour, and a positive distance from that contour is
an explicit hypothesis. These are the analytic ingredients for buffered
rectangle splitting; no approximation or splitting theorem is assumed.
-/

noncomputable section

namespace AutomaticContinuity.ContourIntegralOperators

open Set Filter MeasureTheory Metric
open scoped Topology Interval

universe u v
variable {X : Type u} {E : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The unnormalised Cauchy transform along a parametrised fixed contour.
The tangent factor can be included in `h`; for horizontal edges it is one. -/
def cauchyIntegral (a b : ℝ) (γ : ℝ → ℂ) (h : ℝ → E) (z : ℂ) : E :=
  ∫ t in a..b, (γ t - z)⁻¹ • h t

theorem norm_cauchyIntegral_le {a b M δ : ℝ} {γ : ℝ → ℂ}
    {h : ℝ → E} {z : ℂ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hh : ∀ t ∈ Ι a b, ‖h t‖ ≤ M)
    (hgap : ∀ t ∈ Ι a b, δ ≤ ‖γ t - z‖) :
    ‖cauchyIntegral a b γ h z‖ ≤ (M / δ) * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [norm_smul, norm_inv, inv_mul_eq_div]
  exact div_le_div₀ hM (hh t ht) hδ (hgap t ht)

section Differentiation

variable [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A complex version of differentiation under an interval integral. The
uniform derivative bound is needed only in a neighbourhood of the point. -/
theorem hasFDerivAt_intervalIntegral {a b : ℝ} (hab : a ≤ b)
    {F : X → ℝ → E} {F' : X → ℝ → X →L[ℂ] E} {x : X}
    {s : Set X} (hs : s ∈ 𝓝 x) {B : ℝ}
    (hF : ∀ y ∈ s, ContinuousOn (F y) (Icc a b))
    (hF' : ContinuousOn (F' x) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ∀ y ∈ s, ‖F' y t‖ ≤ B)
    (hdiff : ∀ t ∈ Icc a b, ∀ y ∈ s, HasFDerivAt (F · t) (F' y t) y) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, F y t) (∫ t in a..b, F' x t) x := by
  have hmeasure : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Icc a b :=
    ae_restrict_mem measurableSet_Icc
  have hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (Icc a b)) := by
    filter_upwards [hs] with y hy
    exact (hF y hy).aestronglyMeasurable measurableSet_Icc
  have hint : Integrable (F x) (volume.restrict (Icc a b)) :=
    (hF x (mem_of_mem_nhds hs)).integrableOn_Icc
  have hder := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume.restrict (Icc a b)) (bound := fun _ ↦ B)
    hs hmeas hint (hF'.aestronglyMeasurable measurableSet_Icc)
    (hmeasure.mono fun t ht ↦ hbound t ht) (integrable_const B)
    (hmeasure.mono fun t ht ↦ hdiff t ht)
  simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using hder

variable [ProperSpace X]

/-- Continuous parameter derivatives on a product with a compact interval
provide the uniform bound required for differentiating under the integral. -/
theorem differentiableOn_intervalIntegral {a b : ℝ} (hab : a ≤ b)
    {F : X → ℝ → E} {F' : X → ℝ → X →L[ℂ] E}
    {U : Set X} (hU : IsOpen U)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Icc a b))
    (hF' : ContinuousOn (Function.uncurry F') (U ×ˢ Icc a b))
    (hdiff : ∀ t ∈ Icc a b, ∀ x ∈ U, HasFDerivAt (F · t) (F' x t) x) :
    DifferentiableOn ℂ (fun x ↦ ∫ t in a..b, F x t) U := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K : Set X := closedBall x (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := by
    apply Set.Subset.trans _ hrU
    exact closedBall_subset_ball (by linarith)
  have hKn : K ∈ 𝓝 x := closedBall_mem_nhds _ (by positivity)
  have hprod : K ×ˢ Icc a b ⊆ U ×ˢ Icc a b := prod_mono hKU Subset.rfl
  obtain ⟨B, hB⟩ := ((hK.prod isCompact_Icc).image_of_continuousOn
    (hF'.mono hprod)).isBounded.exists_norm_le
  have hFc (y : X) (hy : y ∈ K) : ContinuousOn (F y) (Icc a b) := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hKU hy, ht⟩)
  have hDc : ContinuousOn (F' x) (Icc a b) := by
    exact hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hx, ht⟩)
  exact (hasFDerivAt_intervalIntegral hab hKn hFc hDc
    (fun t ht y hy ↦ hB _ ⟨(y,t), ⟨hy, ht⟩, rfl⟩)
    (fun t ht y hy ↦ hdiff t ht y (hKU hy))).differentiableAt.differentiableWithinAt

/-- Integrating a jointly holomorphic function on any fixed continuous
contour preserves holomorphy in all the remaining complex parameters. -/
theorem differentiableOn_contourIntegral {a b : ℝ} (hab : a ≤ b)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {H : X × ℂ → E}
    {W : Set (X × ℂ)} (hW : IsOpen W) (hH : DifferentiableOn ℂ H W)
    {U : Set X} (hU : IsOpen U)
    (htrace : ∀ x ∈ U, ∀ t ∈ Icc a b, (x, γ t) ∈ W) :
    DifferentiableOn ℂ (fun x ↦ ∫ t in a..b, H (x, γ t)) U := by
  let F : X → ℝ → E := fun x t ↦ H (x, γ t)
  let F' : X → ℝ → X →L[ℂ] E := fun x t ↦
    (fderiv ℂ H (x, γ t)).comp (ContinuousLinearMap.inl ℂ X ℂ)
  have hmap : Continuous (fun q : X × ℝ ↦ (q.1, γ q.2)) :=
    continuous_fst.prodMk (hγ.comp continuous_snd)
  have hmaps : MapsTo (fun q : X × ℝ ↦ (q.1, γ q.2))
      (U ×ˢ Icc a b) W := fun q hq ↦ htrace q.1 hq.1 q.2 hq.2
  have hFc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc a b) :=
    hH.continuousOn.comp hmap.continuousOn hmaps
  have hDc : ContinuousOn (Function.uncurry F') (U ×ˢ Icc a b) :=
    ((FiniteHolomorphicRegularity.continuousOn_fderiv hW hH).comp
      hmap.continuousOn hmaps).clm_comp continuousOn_const
  apply differentiableOn_intervalIntegral hab hU hFc hDc
  intro t ht x hx
  have hpair : HasFDerivAt (fun y : X ↦ (y, γ t))
      (ContinuousLinearMap.inl ℂ X ℂ) x := by
    have heq : ContinuousLinearMap.inl ℂ X ℂ =
        (ContinuousLinearMap.id ℂ X).prod 0 := by ext y <;> simp
    rw [heq]
    exact (hasFDerivAt_id x).prodMk (hasFDerivAt_const (γ t) x)
  exact (hH.differentiableAt (hW.mem_nhds (htrace x hx t ht))).hasFDerivAt.comp x hpair

/-- Joint holomorphy of the parameter-dependent Cauchy transform on any open
set whose evaluation points avoid the fixed contour. -/
theorem differentiableOn_cauchyIntegral {a b : ℝ} (hab : a ≤ b)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {f : X × ℂ → E}
    {V : Set (X × ℂ)} (hV : IsOpen V) (hf : DifferentiableOn ℂ f V)
    {U : Set (X × ℂ)} (hU : IsOpen U)
    (htrace : ∀ q ∈ U, ∀ t ∈ Icc a b, (q.1, γ t) ∈ V)
    (havoid : ∀ q ∈ U, ∀ t ∈ Icc a b, γ t ≠ q.2) :
    DifferentiableOn ℂ
      (fun q ↦ cauchyIntegral a b γ (fun t ↦ f (q.1, γ t)) q.2) U := by
  let W : Set ((X × ℂ) × ℂ) :=
    {q | (q.1.1, q.2) ∈ V ∧ q.2 - q.1.2 ≠ 0}
  have hW : IsOpen W :=
    (hV.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
      (isOpen_ne.preimage (continuous_snd.sub continuous_fst.snd))
  let H : (X × ℂ) × ℂ → E := fun q ↦ (q.2 - q.1.2)⁻¹ • f (q.1.1, q.2)
  have hH : DifferentiableOn ℂ H W := by
    intro q hq
    have hd : DifferentiableAt ℂ (fun q : (X × ℂ) × ℂ ↦ q.2 - q.1.2) q :=
      differentiableAt_snd.sub differentiableAt_fst.snd
    have hg : DifferentiableAt ℂ (fun q : (X × ℂ) × ℂ ↦ (q.1.1, q.2)) q :=
      differentiableAt_fst.fst.prodMk differentiableAt_snd
    exact ((hd.inv hq.2).smul
      ((hf.differentiableAt (hV.mem_nhds hq.1)).comp q hg)).differentiableWithinAt
  exact differentiableOn_contourIntegral hab hγ hW hH hU
    (fun q hq t ht ↦ ⟨htrace q hq t ht, sub_ne_zero.mpr (havoid q hq t ht)⟩)

end Differentiation

end AutomaticContinuity.ContourIntegralOperators
