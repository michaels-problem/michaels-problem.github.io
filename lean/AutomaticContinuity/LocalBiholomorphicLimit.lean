import AutomaticContinuity.NormalizedHolomorphicLimit
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Biholomorphic neighborhoods for normalized limits

Restrict the inverse-function-theorem chart to a neighborhood where the complex
Fréchet derivative is invertible. The inverse is then holomorphic on its actual
open target, not merely differentiable at the origin.
-/

noncomputable section

namespace AutomaticContinuity.NormalizedHolomorphicLimit

open Filter Metric Set
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A chart whose derivative is the identity at the origin and continuous there
has a restriction with holomorphic inverse on the whole restricted target. -/
theorem exists_biholomorphic_restriction (e : OpenPartialHomeomorph E E)
    {r : ℝ} (hr : 0 < r) (he0 : e 0 = 0) (hsource : (0 : E) ∈ e.source)
    (hd : DifferentiableOn ℂ e (ball 0 r))
    (hd0 : HasFDerivAt e (ContinuousLinearMap.id ℂ E) 0)
    (hcont : ContinuousAt (fderiv ℂ e) 0) :
    ∃ e' : OpenPartialHomeomorph E E,
      (e' : E → E) = e ∧ e' 0 = 0 ∧ (0 : E) ∈ e'.source ∧
      (0 : E) ∈ e'.target ∧ e'.source ⊆ ball 0 r ∧
      DifferentiableOn ℂ e'.symm e'.target := by
  have hunit0 : IsUnit (fderiv ℂ e 0) := by
    rw [hd0.fderiv]
    exact isUnit_one
  have hunit : {x : E | IsUnit (fderiv ℂ e x)} ∈ 𝓝 (0 : E) :=
    hcont (Units.isOpen.mem_nhds hunit0)
  obtain ⟨δ, hδ, hδunit⟩ := Metric.mem_nhds_iff.mp hunit
  let e' := e.restrOpen (ball 0 r ∩ ball 0 δ) (isOpen_ball.inter isOpen_ball)
  have heq : (e' : E → E) = e := rfl
  have hs0 : (0 : E) ∈ e'.source :=
    ⟨hsource, mem_ball_self hr, mem_ball_self hδ⟩
  have ht0 : (0 : E) ∈ e'.target := by
    simpa only [heq, he0] using e'.map_source hs0
  refine ⟨e', heq, he0, hs0, ht0, fun x hx => hx.2.1, ?_⟩
  intro y hy
  have hs := e'.map_target hy
  have hu := hδunit hs.2.2
  obtain ⟨u, hu⟩ := hu
  have hueq : ((ContinuousLinearEquiv.ofUnit u) : E →L[ℂ] E) =
      fderiv ℂ e (e'.symm y) := by
    ext v
    change (u : E →L[ℂ] E) v = (fderiv ℂ e (e'.symm y)) v
    rw [hu]
  have hde := (hd.differentiableAt (isOpen_ball.mem_nhds hs.2.1)).hasFDerivAt
  rw [← hueq] at hde
  exact (e'.hasFDerivAt_symm hy hde).differentiableAt.differentiableWithinAt

/-- The normalized geometric limit admits an actual local biholomorphism whose
source lies in the original holomorphic ball. The forward map still represents
the uniform limit on the full closed ball. -/
theorem exists_normalized_localBiholomorph (f : ℕ → E → E) {r C : ℝ} (hr : 0 < r)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 r))
    (hstep : ∀ n, ∀ x ∈ closedBall 0 r,
      ‖f (n + 1) x - f n x‖ ≤ C * (4 / 9 : ℝ) ^ n)
    (hf0 : ∀ n, f n 0 = 0)
    (hdf0 : ∀ n, HasFDerivAt (f n) (ContinuousLinearMap.id ℂ E) 0)
    (hcont : ∀ n, ContinuousOn (fderiv ℂ (f n)) (ball 0 r)) :
    ∃ e : OpenPartialHomeomorph E E,
      TendstoUniformlyOn f e atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ e (ball 0 r) ∧ e 0 = 0 ∧
      (0 : E) ∈ e.source ∧ (0 : E) ∈ e.target ∧
      e.source ⊆ ball 0 r ∧ DifferentiableOn ℂ e.symm e.target := by
  obtain ⟨e, he, hd, he0, hs, _ht, hd0, _hdi0⟩ :=
    exists_normalized_localHomeomorph f hr hf hstep hf0 hdf0 hcont
  have hderiv := SeveralVariableUniformLimit.tendstoUniformlyOn_fderiv_ball
    hf (he.mono ball_subset_closedBall) (by linarith : r / 2 < r)
  have hce : ContinuousOn (fderiv ℂ e) (ball 0 (r / 2)) := by
    apply hderiv.continuousOn
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      (hcont n).mono (ball_subset_ball (by linarith : r / 2 ≤ r)))
  obtain ⟨e', heq, he'0, hs', ht', hsub, hdi⟩ := exists_biholomorphic_restriction
    e hr he0 hs hd hd0.hasFDerivAt (hce.continuousAt (ball_mem_nhds 0 (half_pos hr)))
  refine ⟨e', ?_, ?_, he'0, hs', ht', hsub, hdi⟩
  · simpa only [heq] using he
  · simpa only [heq] using hd

end AutomaticContinuity.NormalizedHolomorphicLimit
