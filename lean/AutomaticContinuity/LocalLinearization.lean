import AutomaticContinuity.KoenigsEstimates
import AutomaticContinuity.NormalizedHolomorphicLimit

set_option autoImplicit false

/-!
# An actual normalized holomorphic conjugacy from quadratic estimates

The map is constructed as the uniform limit of rescaled iterates. Both its
identity derivative at zero and its conjugacy equation are proved from that
sequence. The explicit small quadratic remainder is still a hypothesis here.
-/

noncomputable section

namespace AutomaticContinuity.LocalLinearization

open Filter Metric KoenigsEstimates
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A quadratic perturbation of a quarter-scale linear equivalence has a
normalized holomorphic solution of the linearization equation near zero. -/
theorem exists_normalized_conjugacy (A : E ≃L[ℂ] E) (T : E → E)
    (hA : ∀ x, ‖A x‖ = (1 / 4 : ℝ) * ‖x‖)
    (hT : Differentiable ℂ T) (hT0 : T 0 = 0)
    (hTd : HasFDerivAt T (A : E →L[ℂ] E) 0)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hsmall : C * r ≤ 1 / 12)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2) :
    ∃ g : E → E,
      TendstoUniformlyOn (rescaledIterate A T) g atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
      HasFDerivAt g (ContinuousLinearMap.id ℂ E) 0 ∧
      ∀ x ∈ closedBall (0 : E) r, g (T x) = A (g x) := by
  have hcontract := contraction_of_quadratic_remainder hA hC hsmall hrem
  obtain ⟨g, hg, hgd, hg0, hgd0⟩ :=
    NormalizedHolomorphicLimit.exists_normalized_limit (rescaledIterate A T) hr
      (fun n => (differentiable_rescaledIterate A hT n).differentiableOn)
      (norm_rescaledIterate_sub_le hA hr.le hC hcontract hrem)
      (rescaledIterate_zero A hT0) (hasFDerivAt_rescaledIterate_zero A hT0 hTd)
  refine ⟨g, hg, hgd, hg0, hgd0, ?_⟩
  intro x hx
  have hTx : T x ∈ closedBall (0 : E) r := by
    simpa only [Function.iterate_one] using (norm_iterate_le hr.le hcontract hx 1).2
  have hleft := hg.tendsto_at hTx
  have hshift : Tendsto (fun n => rescaledIterate A T (n + 1) x) atTop (𝓝 (g x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hg.tendsto_at hx)
  have hright : Tendsto (fun n => A (rescaledIterate A T (n + 1) x)) atTop (𝓝 (A (g x))) :=
    A.continuous.continuousAt.tendsto.comp hshift
  have heq : (fun n => rescaledIterate A T n (T x)) =
      (fun n => A (rescaledIterate A T (n + 1) x)) :=
    funext fun n => rescaledIterate_comp A T n x
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end AutomaticContinuity.LocalLinearization
