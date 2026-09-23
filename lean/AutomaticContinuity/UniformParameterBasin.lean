import AutomaticContinuity.ParameterKoenigsBasin
import AutomaticContinuity.LinearParameterAttraction

set_option autoImplicit false

/-!
# Uniform Koenigs bounds give a holomorphic family of actual basins

All automorphism-family and uniform analytic hypotheses are explicit. The
joint conjugacy, invariant source cylinder, and global product trivialization
are conclusions. This does not construct automorphism families with any
additional compact approximation or interpolation property.
-/

noncomputable section

namespace AutomaticContinuity.ParameterBasin

open Set Filter Metric BasinGlobalization
open scoped Topology

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace P] [ProperSpace E]

/-- A genuine jointly biholomorphic automorphism family, uniformly close to
its contracting fibrewise linearization, has an actual holomorphically
trivial family of entry basins near each base point. -/
theorem exists_of_uniform_koenigs
    (T A : (P × E) ≃ₜ (P × E)) (L : P → E ≃L[ℂ] E)
    {U : Set P} (hU : IsOpen U) {p : P} (hp : p ∈ U)
    {M q r C : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) (hq1 : q < 1)
    (hr : 0 < r) (hC : 0 ≤ C) (hrate : M * q ^ 2 < 1)
    (hTf : ∀ z, (T z).1 = z.1)
    (hAlift : ∀ a x, A (a, x) = (a, L a x))
    (hT : Differentiable ℂ (T : P × E → P × E))
    (hTinv : Differentiable ℂ (T.symm : P × E → P × E))
    (hA : Differentiable ℂ (A : P × E → P × E))
    (hAinv : Differentiable ℂ (A.symm : P × E → P × E))
    (hLinv : ∀ a ∈ U, ∀ x, ‖(L a).symm x‖ ≤ M * ‖x‖)
    (hL : ∀ a ∈ U, ∀ x, ‖L a x‖ ≤ q * ‖x‖)
    (hbound : ∀ a ∈ U, ∀ x ∈ closedBall (0 : E) r,
      ‖(T (a, x)).2‖ ≤ q * ‖x‖)
    (hrem : ∀ a ∈ U, ∀ x ∈ closedBall (0 : E) r,
      ‖(T (a, x)).2 - L a x‖ ≤ C * ‖x‖ ^ 2)
    (hzero : ∀ a ∈ U, (T (a, 0)).2 = 0)
    (hder : ∀ a ∈ U,
      HasFDerivAt (fun x => (T (a, x)).2) ((L a) : E →L[ℂ] E) 0) :
    ∃ δ > 0, ball p δ ⊆ U ∧
      IsOpen (basin T (ball p δ ×ˢ ball (0 : E) δ)) ∧
      basin T (ball p δ ×ˢ ball (0 : E) δ) ⊆ ball p δ ×ˢ univ ∧
      HasHolomorphicProductTrivialization
        (basin T (ball p δ ×ˢ ball (0 : E) δ)) (ball p δ) := by
  have hAf : ∀ z, (A z).1 = z.1 := by
    rintro ⟨a, x⟩
    simp only [hAlift]
  have hAinvformula (z : P × E) :
      A.symm z = (z.1, (L z.1).symm z.2) := by
    apply A.injective
    rw [A.apply_symm_apply, hAlift]
    simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta]
  have hAi : DifferentiableOn ℂ (fun z : P × E => (L z.1).symm z.2) (U ×ˢ univ) := by
    have heq : (fun z : P × E => (L z.1).symm z.2) = fun z => (A.symm z).2 := by
      funext z
      rw [hAinvformula]
    rw [heq]
    exact (differentiable_snd.comp hAinv).differentiableOn
  have hTi : DifferentiableOn ℂ (fun z : P × E => (T (z.1, z.2)).2)
      (U ×ˢ ball 0 r) := (differentiable_snd.comp hT).differentiableOn
  obtain ⟨H, _, hdH, _, hnorm, hconj⟩ :=
    UniformParameterKoenigs.exists_normalized_joint_limit L (fun a x => (T (a, x)).2)
      hU hM hq hq1.le hr hC hrate hAi hTi hLinv hbound hrem hzero hder
  apply exists_of_normalized_conjugacy T A hU hp hr hq1.le hTf hAf
    hT hTinv hA hAinv (fun z hz => hbound z.1 hz.1 z.2 hz.2)
    (fun a ha y => LinearParameterAttraction.tendsto_linear_fiber_pow A L hAlift
      hq hq1 hL ha y) hdH (fun a ha => (hnorm a ha).1) (fun a ha => (hnorm a ha).2)
  intro z hz
  have heT : T z = (z.1, (T z).2) := Prod.ext (hTf z) rfl
  change ((T z).1, H (T z)) = A (z.1, H z)
  rw [hTf, hAlift]
  apply Prod.ext
  · rfl
  · change H (T z) = L z.1 (H z)
    rw [heT]
    exact hconj z.1 hz.1 z.2 (ball_subset_closedBall hz.2)

end AutomaticContinuity.ParameterBasin
