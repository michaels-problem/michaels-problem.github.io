import AutomaticContinuity.SchwarzDerivativeBounds
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

set_option autoImplicit false

/-!
# Joint holomorphicity of locally uniform limits in several variables

Schwarz's derivative estimate turns uniform convergence on a ball into uniform
convergence of Fréchet derivatives on smaller balls. The general theorem about
limits of derivatives then proves joint complex differentiability. No Hartogs
theorem or separate-holomorphicity assumption is used.

The ball statements allow general complex normed domains. The locally uniform
statement assumes a proper domain space so that closed balls are compact; this
includes every finite-dimensional complex normed space.
-/

noncomputable section

namespace AutomaticContinuity.SeveralVariableUniformLimit

open Filter Metric Set
open scoped Topology Uniformity

universe u v w

variable {E : Type u} {F : Type v} {ι : Type w}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {l : Filter ι} {f : ι → E → F} {g : E → F} {c : E} {r R : ℝ}

/-- Uniformly Cauchy holomorphic functions have uniformly Cauchy Fréchet
derivatives on every smaller concentric ball. -/
theorem uniformCauchy_fderiv_ball
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hC : UniformCauchySeqOn f l (ball c R)) (hrR : r < R) :
    UniformCauchySeqOn (fun i => fderiv ℂ (f i)) l (ball c r) := by
  intro u hu
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  let δ : ℝ := ε * (R - r) / 4
  have hδ : 0 < δ := div_pos (mul_pos hε (sub_pos.mpr hrR)) (by norm_num)
  filter_upwards [hC _ (Metric.dist_mem_uniformity hδ)] with ij hij x hx
  apply hεu
  rw [dist_eq_norm]
  have hb : ∀ y ∈ ball c R, ‖f ij.1 y - f ij.2 y‖ ≤ δ := by
    intro y hy
    exact (show ‖f ij.1 y - f ij.2 y‖ < δ by
      simpa only [dist_eq_norm] using hij y hy).le
  apply (SchwarzDerivativeBounds.norm_fderiv_sub_le (hf ij.1) (hf ij.2) hb hrR hx).trans_lt
  rw [div_lt_iff₀ (sub_pos.mpr hrR)]
  dsimp [δ]
  nlinarith

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- Completeness turns a uniform Cauchy family on a set into a uniform limit.
Only the values on that set matter; the chosen extension is zero outside it. -/
theorem exists_uniform_limit [CompleteSpace F] [l.NeBot] {s : Set E}
    (hC : UniformCauchySeqOn f l s) :
    ∃ g : E → F, TendstoUniformlyOn f g l s := by
  classical
  have hpoint : ∀ x : s, ∃ y : F, Tendsto (fun i => f i x.val) l (𝓝 y) :=
    fun x => cauchy_map_iff_exists_tendsto.mp (hC.cauchy_map x.property)
  choose g hg using hpoint
  let G : E → F := fun x => if hx : x ∈ s then g ⟨x, hx⟩ else 0
  refine ⟨G, hC.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [G, dite_eq_left hx] using hg ⟨x, hx⟩

variable [CompleteSpace F] [l.NeBot]

/-- Uniform convergence on one ball implies uniform convergence of the actual
Fréchet derivatives on each smaller ball. -/
theorem tendstoUniformlyOn_fderiv_ball
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hlim : TendstoUniformlyOn f g l (ball c R)) (hrR : r < R) :
    TendstoUniformlyOn (fun i => fderiv ℂ (f i)) (fderiv ℂ g) l (ball c r) := by
  obtain ⟨G, hG⟩ := exists_uniform_limit
    (uniformCauchy_fderiv_ball hf hlim.uniformCauchySeqOn hrR)
  have hGderiv : ∀ x ∈ ball c r, HasFDerivAt g (G x) x := by
    intro x hx
    apply hasFDerivAt_of_tendstoUniformlyOn (f := f) isOpen_ball hG ?_ ?_ hx
    · intro i y hy
      exact ((hf i y (ball_subset_ball hrR.le hy)).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hy))).hasFDerivAt
    · intro y hy
      exact hlim.tendsto_at (ball_subset_ball hrR.le hy)
  exact hG.congr_right (fun x hx => (hGderiv x hx).fderiv.symm)

/-- The uniform limit on a ball is jointly complex differentiable there. -/
theorem differentiableOn_of_tendstoUniformlyOn_ball
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hlim : TendstoUniformlyOn f g l (ball c R)) :
    DifferentiableOn ℂ g (ball c R) := by
  intro x hx
  obtain ⟨r, hxr, hrR⟩ := exists_between (show dist x c < R from hx)
  have hderiv := tendstoUniformlyOn_fderiv_ball hf hlim hrR
  have hg : HasFDerivAt g (fderiv ℂ g x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn (f := f) isOpen_ball hderiv ?_ ?_ hxr
    · intro i y hy
      exact ((hf i y (ball_subset_ball hrR.le hy)).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball hrR.le hy))).hasFDerivAt
    · intro y hy
      exact hlim.tendsto_at (ball_subset_ball hrR.le hy)
  exact hg.differentiableAt.differentiableWithinAt

/-- Several-variable Weierstrass theorem on an open set. Properness is used
only to turn locally uniform convergence into uniform convergence on a compact
closed subball, and holds for all finite-dimensional complex source spaces. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn [ProperSpace E]
    {U : Set E} (hU : IsOpen U) (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hlim : TendstoLocallyUniformlyOn f g l U) : DifferentiableOn ℂ g U := by
  intro x hx
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hR2 : 0 < R / 2 := half_pos hR
  have hclosed : closedBall x (R / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith : R / 2 < R)).trans hRU
  have hcompact := isCompact_closedBall x (R / 2)
  have huniform :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hclosed hcompact
  have hball : ball x (R / 2) ⊆ U := ball_subset_closedBall.trans hclosed
  have hd := differentiableOn_of_tendstoUniformlyOn_ball
    (fun i => (hf i).mono hball) (huniform.mono ball_subset_closedBall)
  exact (hd.differentiableAt (ball_mem_nhds x hR2)).differentiableWithinAt

end AutomaticContinuity.SeveralVariableUniformLimit
