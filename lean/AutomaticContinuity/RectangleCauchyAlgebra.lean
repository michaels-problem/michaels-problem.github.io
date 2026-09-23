import AutomaticContinuity.RectangleCauchyIntegral

set_option autoImplicit false

/-! # Boundary algebra for rectangular contour integrals

Continuity is required only on the four edges.  This allows Cauchy kernels
with an interior singularity while keeping all integral linearity hypotheses
explicit.
-/

noncomputable section
namespace AutomaticContinuity.RectangleCauchy
open Complex Set MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rectangleBoundary (l r b t : ℝ) : Set ℂ :=
  {w | w ∈ closedRectangle l r b t ∧
    (w.re = l ∨ w.re = r ∨ w.im = b ∨ w.im = t)}

theorem rectangleBoundary_subset_closedRectangle (l r b t : ℝ) :
    rectangleBoundary l r b t ⊆ closedRectangle l r b t := fun _ h => h.1

theorem horizontal_mem_boundary {l r b t y : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    (hy : y = b ∨ y = t) {x : ℝ} (hx : x ∈ uIcc l r) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary l r b t := by
  rw [uIcc_of_le hlr] at hx
  rcases hy with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, mem_reProdIm]

theorem vertical_mem_boundary {l r b t x : ℝ} (hlr : l ≤ r) (hbt : b ≤ t)
    (hx : x = l ∨ x = r) {y : ℝ} (hy : y ∈ uIcc b t) :
    (x : ℂ) + (y : ℂ) * I ∈ rectangleBoundary l r b t := by
  rw [uIcc_of_le hbt] at hy
  rcases hx with rfl | rfl <;>
    simp_all [rectangleBoundary, closedRectangle, mem_reProdIm]

theorem boundary_ne_interior {l r b t : ℝ} {w z : ℂ}
    (hw : w ∈ rectangleBoundary l r b t) (hz : z ∈ openRectangle l r b t) :
    w ≠ z := by
  intro heq
  subst w
  rcases hw.2 with h | h | h | h
  · exact (ne_of_gt hz.1.1) h
  · exact (ne_of_lt hz.1.2) h
  · exact (ne_of_gt hz.2.1) h
  · exact (ne_of_lt hz.2.2) h

structure BoundaryIntegrable (l r b t : ℝ) (f : ℂ → E) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (b : ℂ) * I)) volume l r
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (t : ℂ) * I)) volume l r
  right : IntervalIntegrable (fun y : ℝ => f ((r : ℂ) + (y : ℂ) * I)) volume b t
  left : IntervalIntegrable (fun y : ℝ => f ((l : ℂ) + (y : ℂ) * I)) volume b t

omit [NormedSpace ℂ E] in
theorem boundaryIntegrable_of_continuousOn {l r b t : ℝ} {f : ℂ → E}
    (hlr : l ≤ r) (hbt : b ≤ t) (hf : ContinuousOn f (rectangleBoundary l r b t)) :
    BoundaryIntegrable l r b t f := by
  have hh (y : ℝ) (hy : y = b ∨ y = t) :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (uIcc l r) :=
    hf.comp (by fun_prop) (fun _ hx => horizontal_mem_boundary hlr hbt hy hx)
  have hv (x : ℝ) (hx : x = l ∨ x = r) :
      ContinuousOn (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) (uIcc b t) :=
    hf.comp (by fun_prop) (fun _ hy => vertical_mem_boundary hlr hbt hx hy)
  exact ⟨(hh b (Or.inl rfl)).intervalIntegrable,
    (hh t (Or.inr rfl)).intervalIntegrable,
    (hv r (Or.inr rfl)).intervalIntegrable,
    (hv l (Or.inl rfl)).intervalIntegrable⟩

theorem rectangleIntegral_congr {l r b t : ℝ} {f g : ℂ → E}
    (hlr : l ≤ r) (hbt : b ≤ t) (hfg : EqOn f g (rectangleBoundary l r b t)) :
    rectangleIntegral l r b t f = rectangleIntegral l r b t g := by
  have hh (y : ℝ) (hy : y = b ∨ y = t) :
      horizontalIntegral l r y f = horizontalIntegral l r y g :=
    intervalIntegral.integral_congr
      (fun _ hx => hfg (horizontal_mem_boundary hlr hbt hy hx))
  have hv (x : ℝ) (hx : x = l ∨ x = r) :
      verticalIntegral b t x f = verticalIntegral b t x g := by
    unfold verticalIntegral
    congr 1
    exact intervalIntegral.integral_congr
      (fun _ hy => hfg (vertical_mem_boundary hlr hbt hx hy))
  rw [rectangleIntegral, rectangleIntegral, hh b (Or.inl rfl), hh t (Or.inr rfl),
    hv r (Or.inr rfl), hv l (Or.inl rfl)]

theorem rectangleIntegral_sub {l r b t : ℝ} {f g : ℂ → E}
    (hf : BoundaryIntegrable l r b t f) (hg : BoundaryIntegrable l r b t g) :
    rectangleIntegral l r b t (fun w => f w - g w) =
      rectangleIntegral l r b t f - rectangleIntegral l r b t g := by
  simp only [rectangleIntegral, horizontalIntegral, verticalIntegral,
    intervalIntegral.integral_sub hf.bottom hg.bottom,
    intervalIntegral.integral_sub hf.top hg.top,
    intervalIntegral.integral_sub hf.right hg.right,
    intervalIntegral.integral_sub hf.left hg.left, smul_sub]
  abel

theorem rectangleIntegral_smul_const [CompleteSpace E] (l r b t : ℝ)
    (f : ℂ → ℂ) (v : E) :
    rectangleIntegral l r b t (fun w => f w • v) =
      rectangleIntegral l r b t f • v := by
  simp only [rectangleIntegral, horizontalIntegral, verticalIntegral,
    intervalIntegral.integral_smul_const, sub_smul, add_smul, smul_smul,
    smul_eq_mul]

end AutomaticContinuity.RectangleCauchy
