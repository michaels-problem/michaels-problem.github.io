import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

/-! # Positively oriented rectangular contour integrals

The horizontal sides use increasing real coordinates, and the vertical sides
use increasing imaginary coordinates with the complex tangent factor `I`.
The full boundary is bottom minus top plus right minus left, so the left edge
is oriented downwards. This convention matches Mathlib's rectangular Goursat
formula exactly.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Complex Set MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def horizontalIntegral (l r y : ℝ) (f : ℂ → E) : E :=
  ∫ x : ℝ in l..r, f ((x : ℂ) + (y : ℂ) * I)

def verticalIntegral (b t x : ℝ) (f : ℂ → E) : E :=
  I • ∫ y : ℝ in b..t, f ((x : ℂ) + (y : ℂ) * I)

def rectangleIntegral (l r b t : ℝ) (f : ℂ → E) : E :=
  horizontalIntegral l r b f - horizontalIntegral l r t f +
    verticalIntegral b t r f - verticalIntegral b t l f

def closedRectangle (l r b t : ℝ) : Set ℂ := Icc l r ×ℂ Icc b t

def openRectangle (l r b t : ℝ) : Set ℂ := Ioo l r ×ℂ Ioo b t

theorem isOpen_openRectangle (l r b t : ℝ) : IsOpen (openRectangle l r b t) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem openRectangle_subset_closedRectangle (l r b t : ℝ) :
    openRectangle l r b t ⊆ closedRectangle l r b t :=
  inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

theorem rectangleIntegral_eq_zero_off_countable [CompleteSpace E]
    (f : ℂ → E) {l r b t : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    (s : Set ℂ) (hs : s.Countable)
    (hc : ContinuousOn f (closedRectangle l r b t))
    (hd : ∀ z ∈ openRectangle l r b t \ s, DifferentiableAt ℂ f z) :
    rectangleIntegral l r b t f = 0 := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f ⟨l, b⟩ ⟨r, t⟩ s hs
  simp only [Set.uIcc_of_le hlr, Set.uIcc_of_le hbt, min_eq_left hlr, max_eq_right hlr,
    min_eq_left hbt, max_eq_right hbt] at hh
  exact hh hc hd

end AutomaticContinuity.RectangleCauchy
