import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false

/-!
# Uniform derivative estimates on smaller complex balls

These are direct consequences of the Schwarz estimate for complex normed
spaces. They require no completeness or finite-dimensionality assumptions.
-/

namespace AutomaticContinuity.SchwarzDerivativeBounds

open Metric Set

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {f g : E → F} {c x : E} {r R B : ℝ}

/-- A uniform value bound controls the derivative on every smaller closed ball. -/
theorem norm_fderiv_le_closedBall
    (hd : DifferentiableOn ℂ f (ball c R))
    (hbound : ∀ y ∈ ball c R, ‖f y‖ ≤ B)
    (hrR : r < R) (hx : x ∈ closedBall c r) :
    ‖fderiv ℂ f x‖ ≤ 2 * B / (R - r) := by
  have hsmall : ball x (R - r) ⊆ ball c R := by
    apply ball_subset_ball'
    have hx' : dist x c ≤ r := hx
    linarith
  have hxR : x ∈ ball c R := (closedBall_subset_ball hrR) hx
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hd.mono hsmall) _ (sub_pos.mpr hrR)
  intro y hy
  change dist (f y) (f x) ≤ 2 * B
  rw [dist_eq_norm]
  exact (norm_sub_le (f y) (f x)).trans (by linarith [hbound y (hsmall hy), hbound x hxR])

/-- Open-ball version of the uniform derivative bound. -/
theorem norm_fderiv_le
    (hd : DifferentiableOn ℂ f (ball c R))
    (hbound : ∀ y ∈ ball c R, ‖f y‖ ≤ B)
    (hrR : r < R) (hx : x ∈ ball c r) :
    ‖fderiv ℂ f x‖ ≤ 2 * B / (R - r) :=
  norm_fderiv_le_closedBall hd hbound hrR (ball_subset_closedBall hx)

/-- A uniform bound on a difference controls the difference of the actual
Fréchet derivatives, uniformly on every smaller closed ball. -/
theorem norm_fderiv_sub_le_closedBall
    (hf : DifferentiableOn ℂ f (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hbound : ∀ y ∈ ball c R, ‖f y - g y‖ ≤ B)
    (hrR : r < R) (hx : x ∈ closedBall c r) :
    ‖fderiv ℂ f x - fderiv ℂ g x‖ ≤ 2 * B / (R - r) := by
  have hxR : x ∈ ball c R := (closedBall_subset_ball hrR) hx
  have hfx : DifferentiableAt ℂ f x := hf.differentiableAt (isOpen_ball.mem_nhds hxR)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (isOpen_ball.mem_nhds hxR)
  have h := norm_fderiv_le_closedBall (hf.sub hg) hbound hrR hx
  simpa only [fderiv_sub hfx hgx] using h

/-- Open-ball version used for locally uniform Cauchy estimates on derivatives. -/
theorem norm_fderiv_sub_le
    (hf : DifferentiableOn ℂ f (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hbound : ∀ y ∈ ball c R, ‖f y - g y‖ ≤ B)
    (hrR : r < R) (hx : x ∈ ball c r) :
    ‖fderiv ℂ f x - fderiv ℂ g x‖ ≤ 2 * B / (R - r) :=
  norm_fderiv_sub_le_closedBall hf hg hbound hrR (ball_subset_closedBall hx)

end AutomaticContinuity.SchwarzDerivativeBounds
