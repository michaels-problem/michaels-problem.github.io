import AutomaticContinuity.RectangleCauchyOperators

set_option autoImplicit false

/-! # Buffered domains for rectangular splitting

The left contour is holomorphic to its right. The other three contours are
holomorphic on the open strip lying below the top, above the bottom, and to
the left of the right side. Positive coordinate buffers give the uniform
operator bounds on closed output sets.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Set Complex
open scoped Interval

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

def leftDomain (l : ℝ) : Set ℂ := {z | l < z.re}
def rightDomain (r b t : ℝ) : Set ℂ := {z | z.re < r ∧ b < z.im ∧ z.im < t}

theorem isOpen_leftDomain (l : ℝ) : IsOpen (leftDomain l) :=
  isOpen_lt continuous_const continuous_re

theorem isOpen_rightDomain (r b t : ℝ) : IsOpen (rightDomain r b t) :=
  (isOpen_lt continuous_re continuous_const).inter
    ((isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const))

theorem horizontal_mem_closedRectangle {l r b t y x : ℝ}
    (hy : y ∈ Icc b t) (hx : x ∈ Icc l r) :
    (x:ℂ)+(y:ℂ)*I ∈ closedRectangle l r b t := by
  simpa [closedRectangle, mem_reProdIm] using And.intro hx hy

theorem vertical_mem_closedRectangle {l r b t y x : ℝ}
    (hx : x ∈ Icc l r) (hy : y ∈ Icc b t) :
    (x:ℂ)+(y:ℂ)*I ∈ closedRectangle l r b t :=
  horizontal_mem_closedRectangle hy hx

theorem norm_leftPart_le_of_re_buffer {l b t M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ) (hz : l + δ ≤ z.re)
    (hf : ∀ y ∈ Ι b t, ‖f ((l:ℂ)+(y:ℂ)*I)‖ ≤ M) :
    ‖leftPart l b t f z‖ ≤ (|t-b| / (2*Real.pi*δ))*M := by
  apply norm_leftPart_le hM hδ hf
  intro y _
  calc
    δ ≤ -(((l:ℂ)+(y:ℂ)*I-z).re) := by simp; linarith
    _ ≤ |((l:ℂ)+(y:ℂ)*I-z).re| := neg_le_abs _
    _ ≤ ‖(l:ℂ)+(y:ℂ)*I-z‖ := Complex.abs_re_le_norm _

theorem norm_rightPart_le_of_buffers {l r b t M δ : ℝ} {f : ℂ → E} {z : ℂ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hzr : z.re + δ ≤ r) (hzb : b + δ ≤ z.im) (hzt : z.im + δ ≤ t)
    (hbottom : ∀ x ∈ Ι l r, ‖f ((x:ℂ)+(b:ℂ)*I)‖ ≤ M)
    (htop : ∀ x ∈ Ι l r, ‖f ((x:ℂ)+(t:ℂ)*I)‖ ≤ M)
    (hright : ∀ y ∈ Ι b t, ‖f ((r:ℂ)+(y:ℂ)*I)‖ ≤ M) :
    ‖rightPart l r b t f z‖ ≤ ((2*|r-l|+|t-b|)/(2*Real.pi*δ))*M := by
  apply norm_rightPart_le hM hδ hbottom htop hright
  · intro x _
    calc
      δ ≤ -(((x:ℂ)+(b:ℂ)*I-z).im) := by simp; linarith
      _ ≤ |((x:ℂ)+(b:ℂ)*I-z).im| := neg_le_abs _
      _ ≤ ‖(x:ℂ)+(b:ℂ)*I-z‖ := Complex.abs_im_le_norm _
  · intro x _
    calc
      δ ≤ ((x:ℂ)+(t:ℂ)*I-z).im := by simp; linarith
      _ ≤ |((x:ℂ)+(t:ℂ)*I-z).im| := le_abs_self _
      _ ≤ ‖(x:ℂ)+(t:ℂ)*I-z‖ := Complex.abs_im_le_norm _
  · intro y _
    calc
      δ ≤ ((r:ℂ)+(y:ℂ)*I-z).re := by simp; linarith
      _ ≤ |((r:ℂ)+(y:ℂ)*I-z).re| := le_abs_self _
      _ ≤ ‖(r:ℂ)+(y:ℂ)*I-z‖ := Complex.abs_re_le_norm _

section Holomorphy

variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

theorem differentiableOn_leftPart_domain {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ V) :
    DifferentiableOn ℂ (fun q ↦ leftPart l b t (fun ζ ↦ f (q.1,ζ)) q.2)
      (O ×ˢ leftDomain l) := by
  apply differentiableOn_leftPart hbt hV hf (hO.prod (isOpen_leftDomain l))
  · intro q hq y hy
    exact hrect ⟨hq.1, vertical_mem_closedRectangle ⟨le_rfl, hlr⟩ hy⟩
  · intro q hq y _ heq
    have hre := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero, zero_mul,
      sub_self, add_zero] at hre
    exact (ne_of_lt hq.2) hre

theorem differentiableOn_rightPart_domain {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    {f : P × ℂ → E} {V : Set (P × ℂ)} {O : Set P}
    (hV : IsOpen V) (hf : DifferentiableOn ℂ f V) (hO : IsOpen O)
    (hrect : O ×ˢ closedRectangle l r b t ⊆ V) :
    DifferentiableOn ℂ (fun q ↦ rightPart l r b t (fun ζ ↦ f (q.1,ζ)) q.2)
      (O ×ˢ rightDomain r b t) := by
  apply differentiableOn_rightPart hlr hbt hV hf (hO.prod (isOpen_rightDomain r b t))
  · intro q hq x hx
    exact hrect ⟨hq.1, horizontal_mem_closedRectangle ⟨le_rfl, hbt⟩ hx⟩
  · intro q hq x hx
    exact hrect ⟨hq.1, horizontal_mem_closedRectangle ⟨hbt, le_rfl⟩ hx⟩
  · intro q hq y hy
    exact hrect ⟨hq.1, vertical_mem_closedRectangle ⟨hlr, le_rfl⟩ hy⟩
  · intro q hq x _ heq
    have him := congrArg Complex.im heq
    simp at him
    exact (ne_of_lt hq.2.2.1) him
  · intro q hq x _ heq
    have him := congrArg Complex.im heq
    simp at him
    exact (ne_of_gt hq.2.2.2) him
  · intro q hq y _ heq
    have hre := congrArg Complex.re heq
    simp at hre
    exact (ne_of_gt hq.2.1) hre

end Holomorphy

end AutomaticContinuity.RectangleCauchy
