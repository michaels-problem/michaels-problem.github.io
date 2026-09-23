import AutomaticContinuity.RectangleCauchyDomains
import AutomaticContinuity.RectangleCauchyReproduction

set_option autoImplicit false

/-! # Bounded additive splitting over overlapping product rectangles

All additional complex variables are retained as the parameter `P`. A single
fixed rectangle in the holomorphic overlap buffer supplies both operators.
The norm is controlled on that buffered rectangle, not merely on the smaller
overlap. The output domains and the operator constant are independent of the
input function. The convention is `f = beta - alpha`.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Set Complex
open scoped Interval

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem leftPart_add_rightPart_eq {l r b t : ℝ}
    (f : ℂ → E) {z : ℂ} (hz : z ∈ openRectangle l r b t)
    (hc : ContinuousOn f (closedRectangle l r b t))
    (hd : DifferentiableOn ℂ f (openRectangle l r b t)) :
    leftPart l b t f z + rightPart l r b t f z = f z := by
  rw [leftPart_add_rightPart]
  exact normalized_rectangleIntegral_inv_smul f hz hc hd

/-- The actual fixed Cauchy operators solve the additive splitting problem
on two overlapping rectangles, holomorphically in every complex parameter.
The input bound on `K × Q` yields both output bounds with the same explicit
constant; `K` can be any chosen set of parameter values. -/
theorem exists_bounded_additive_split
    {a b c d s t l r v w δ M : ℝ}
    (hbc : b ≤ c) (hst : s ≤ t) (hδ : 0 < δ)
    (hl : l + δ ≤ b) (hr : c + δ ≤ r)
    (hv : v + δ ≤ s) (hw : t + δ ≤ w) (hM : 0 ≤ M)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O K : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r v w ⊆ V)
    (hbound : ∀ p ∈ K, ∀ z ∈ closedRectangle l r v w, ‖f (p,z)‖ ≤ M) :
    ∃ alpha beta : P × ℂ → E,
      DifferentiableOn ℂ alpha (O ×ˢ rightDomain r v w) ∧
      DifferentiableOn ℂ beta (O ×ˢ leftDomain l) ∧
      (∀ p ∈ O, ∀ z ∈ closedRectangle b c s t, beta (p,z) - alpha (p,z) = f (p,z)) ∧
      (∀ p ∈ K, ∀ z ∈ closedRectangle a c s t,
        ‖alpha (p,z)‖ ≤ ((2*|r-l|+|w-v|)/(2*Real.pi*δ))*M) ∧
      (∀ p ∈ K, ∀ z ∈ closedRectangle b d s t,
        ‖beta (p,z)‖ ≤ ((2*|r-l|+|w-v|)/(2*Real.pi*δ))*M) := by
  have hlr : l ≤ r := by linarith
  have hvw : v ≤ w := by linarith
  let alpha : P × ℂ → E := fun q ↦ -rightPart l r v w (fun ζ ↦ f (q.1,ζ)) q.2
  let beta : P × ℂ → E := fun q ↦ leftPart l v w (fun ζ ↦ f (q.1,ζ)) q.2
  refine ⟨alpha, beta,
    (differentiableOn_rightPart_domain hlr hvw hV hf hO hrect).neg,
    differentiableOn_leftPart_domain hlr hvw hV hf hO hrect, ?_, ?_, ?_⟩
  · intro p hp z hz
    have hz' : z ∈ openRectangle l r v w := by
      change (l < z.re ∧ z.re < r) ∧ (v < z.im ∧ z.im < w)
      rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
      exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩
    have hc : ContinuousOn (fun ζ ↦ f (p,ζ)) (closedRectangle l r v w) :=
      hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun ζ hζ ↦ hrect ⟨hp,hζ⟩)
    have hd : DifferentiableOn ℂ (fun ζ ↦ f (p,ζ)) (openRectangle l r v w) :=
      hf.comp ((differentiable_const p).prodMk differentiable_id).differentiableOn
        (fun ζ hζ ↦ hrect ⟨hp,openRectangle_subset_closedRectangle l r v w hζ⟩)
    simpa only [alpha, beta, sub_neg_eq_add] using leftPart_add_rightPart_eq _ hz' hc hd
  · intro p hp z hz
    have hbnd (y : ℝ) (hy : y ∈ Icc v w) (x : ℝ) (hx : x ∈ Ι l r) :
        ‖f (p,(x:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (horizontal_mem_closedRectangle hy _)
      simpa only [uIcc_of_le hlr] using uIoc_subset_uIcc hx
    have hrbnd (y : ℝ) (hy : y ∈ Ι v w) : ‖f (p,(r:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (vertical_mem_closedRectangle ⟨hlr,le_rfl⟩ _)
      simpa only [uIcc_of_le hvw] using uIoc_subset_uIcc hy
    have hzr : z.re + δ ≤ r := by have := hz.1.2; linarith
    have hzv : v + δ ≤ z.im := by have := hz.2.1; linarith
    have hzw : z.im + δ ≤ w := by have := hz.2.2; linarith
    simpa only [alpha, norm_neg] using norm_rightPart_le_of_buffers hM hδ hzr hzv hzw
      (hbnd v ⟨le_rfl,hvw⟩) (hbnd w ⟨hvw,le_rfl⟩) hrbnd
  · intro p hp z hz
    have hbnd (y : ℝ) (hy : y ∈ Ι v w) : ‖f (p,(l:ℂ)+(y:ℂ)*I)‖ ≤ M := by
      apply hbound p hp _ (vertical_mem_closedRectangle ⟨le_rfl,hlr⟩ _)
      simpa only [uIcc_of_le hvw] using uIoc_subset_uIcc hy
    have hzl : l + δ ≤ z.re := by have := hz.1.1; linarith
    have hleft := norm_leftPart_le_of_re_buffer (b := v) (t := w)
      (f := fun ζ ↦ f (p,ζ)) hM hδ hzl hbnd
    exact hleft.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by have := abs_nonneg (r-l); linarith) (by positivity)) hM)

end AutomaticContinuity.RectangleCauchy
