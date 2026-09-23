import AutomaticContinuity.RectangleCauchyOperators
import AutomaticContinuity.RectangleCauchyAlgebra

set_option autoImplicit false

/-! # Linearity of the fixed rectangular splitting operators

The additivity hypotheses involve only the relevant contour pieces. Scalar
linearity and zero preservation hold without extra integrability hypotheses.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Set Complex MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

@[simp] theorem horizontalCauchy_zero (l r y : ℝ) (z : ℂ) :
    horizontalCauchy l r y (fun _ ↦ (0:E)) z = 0 := by
  simp [horizontalCauchy, horizontalIntegral]

@[simp] theorem verticalCauchy_zero (b t x : ℝ) (z : ℂ) :
    verticalCauchy b t x (fun _ ↦ (0:E)) z = 0 := by
  simp [verticalCauchy, verticalIntegral]

@[simp] theorem leftPart_zero (l b t : ℝ) (z : ℂ) :
    leftPart l b t (fun _ ↦ (0:E)) z = 0 := by simp [leftPart]

@[simp] theorem rightPart_zero (l r b t : ℝ) (z : ℂ) :
    rightPart l r b t (fun _ ↦ (0:E)) z = 0 := by simp [rightPart]

theorem horizontalCauchy_add {l r y : ℝ} {z : ℂ} {f g : ℂ → E}
    (hf : IntervalIntegrable (fun x : ℝ ↦ ((x:ℂ)+(y:ℂ)*I-z)⁻¹ • f ((x:ℂ)+(y:ℂ)*I)) volume l r)
    (hg : IntervalIntegrable (fun x : ℝ ↦ ((x:ℂ)+(y:ℂ)*I-z)⁻¹ • g ((x:ℂ)+(y:ℂ)*I)) volume l r) :
    horizontalCauchy l r y (fun ζ ↦ f ζ + g ζ) z =
      horizontalCauchy l r y f z + horizontalCauchy l r y g z := by
  simp only [horizontalCauchy, horizontalIntegral, smul_add]
  exact intervalIntegral.integral_add hf hg

theorem verticalCauchy_add {b t x : ℝ} {z : ℂ} {f g : ℂ → E}
    (hf : IntervalIntegrable (fun y : ℝ ↦ ((x:ℂ)+(y:ℂ)*I-z)⁻¹ • f ((x:ℂ)+(y:ℂ)*I)) volume b t)
    (hg : IntervalIntegrable (fun y : ℝ ↦ ((x:ℂ)+(y:ℂ)*I-z)⁻¹ • g ((x:ℂ)+(y:ℂ)*I)) volume b t) :
    verticalCauchy b t x (fun ζ ↦ f ζ + g ζ) z =
      verticalCauchy b t x f z + verticalCauchy b t x g z := by
  simp only [verticalCauchy, verticalIntegral, smul_add, intervalIntegral.integral_add hf hg]

theorem leftPart_add {l b t : ℝ} {z : ℂ} {f g : ℂ → E}
    (hf : IntervalIntegrable (fun y : ℝ ↦ ((l:ℂ)+(y:ℂ)*I-z)⁻¹ • f ((l:ℂ)+(y:ℂ)*I)) volume b t)
    (hg : IntervalIntegrable (fun y : ℝ ↦ ((l:ℂ)+(y:ℂ)*I-z)⁻¹ • g ((l:ℂ)+(y:ℂ)*I)) volume b t) :
    leftPart l b t (fun ζ ↦ f ζ + g ζ) z = leftPart l b t f z + leftPart l b t g z := by
  simp only [leftPart, verticalCauchy_add hf hg, smul_add, neg_add]

theorem rightPart_add {l r b t : ℝ} {z : ℂ} {f g : ℂ → E}
    (hf : BoundaryIntegrable l r b t (fun ζ ↦ (ζ-z)⁻¹ • f ζ))
    (hg : BoundaryIntegrable l r b t (fun ζ ↦ (ζ-z)⁻¹ • g ζ)) :
    rightPart l r b t (fun ζ ↦ f ζ + g ζ) z =
      rightPart l r b t f z + rightPart l r b t g z := by
  simp only [rightPart, horizontalCauchy_add hf.bottom hg.bottom,
    horizontalCauchy_add hf.top hg.top, verticalCauchy_add hf.right hg.right, smul_add, smul_sub]
  abel

theorem horizontalCauchy_smul (l r y : ℝ) (f : ℂ → E) (z c : ℂ) :
    horizontalCauchy l r y (fun ζ ↦ c • f ζ) z = c • horizontalCauchy l r y f z := by
  simp only [horizontalCauchy, horizontalIntegral, smul_comm _ c, intervalIntegral.integral_smul]

theorem verticalCauchy_smul (b t x : ℝ) (f : ℂ → E) (z c : ℂ) :
    verticalCauchy b t x (fun ζ ↦ c • f ζ) z = c • verticalCauchy b t x f z := by
  simp only [verticalCauchy, verticalIntegral, smul_comm _ c, intervalIntegral.integral_smul]

theorem leftPart_smul (l b t : ℝ) (f : ℂ → E) (z c : ℂ) :
    leftPart l b t (fun ζ ↦ c • f ζ) z = c • leftPart l b t f z := by
  simp only [leftPart, verticalCauchy_smul, smul_comm _ c, smul_neg]

theorem rightPart_smul (l r b t : ℝ) (f : ℂ → E) (z c : ℂ) :
    rightPart l r b t (fun ζ ↦ c • f ζ) z = c • rightPart l r b t f z := by
  simp only [rightPart, horizontalCauchy_smul, verticalCauchy_smul,
    ← smul_sub, ← smul_add, smul_comm _ c]

theorem horizontalCauchy_eq_zero_of_eq_zero {l r y : ℝ} {f : ℂ → E} (z : ℂ)
    (hf : ∀ x ∈ uIcc l r, f ((x:ℂ)+(y:ℂ)*I) = 0) :
    horizontalCauchy l r y f z = 0 := by
  unfold horizontalCauchy horizontalIntegral
  calc
    _ = ∫ x in l..r, (0:E) := intervalIntegral.integral_congr (fun x hx ↦ by simp [hf x hx])
    _ = 0 := by simp

theorem verticalCauchy_eq_zero_of_eq_zero {b t x : ℝ} {f : ℂ → E} (z : ℂ)
    (hf : ∀ y ∈ uIcc b t, f ((x:ℂ)+(y:ℂ)*I) = 0) :
    verticalCauchy b t x f z = 0 := by
  unfold verticalCauchy verticalIntegral
  have hi : (∫ y in b..t, ((x:ℂ)+(y:ℂ)*I-z)⁻¹ • f ((x:ℂ)+(y:ℂ)*I)) = 0 := by
    calc
      _ = ∫ y in b..t, (0:E) := intervalIntegral.integral_congr (fun y hy ↦ by rw [hf y hy, smul_zero])
      _ = 0 := by simp
  rw [hi, smul_zero]

end AutomaticContinuity.RectangleCauchy
