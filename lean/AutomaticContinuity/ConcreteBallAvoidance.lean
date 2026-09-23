import AutomaticContinuity.SmallScaleBasin
import AutomaticContinuity.SmallScaleHenonTrapping
import AutomaticContinuity.BasinAvoidance

set_option autoImplicit false

/-! # Concrete biholomorphic domains avoiding a closed Euclidean ball -/

noncomputable section

namespace AutomaticContinuity.ConcreteBallAvoidance

open Set Metric SmallScaleHenonTrapping
open scoped Topology

/-- The actual invertible derivative of the Hénon map. -/
def henonDerivativeEquiv {β : ℝ} (hβ : β ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) where
  toFun := henonDerivative β
  invFun v := ((β : ℂ)⁻¹ * v.2, -(β : ℂ)⁻¹ * v.1)
  left_inv v := by
    have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
    ext <;> simp [henonDerivative_apply, hb]
  right_inv v := by
    have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
    ext <;> simp [henonDerivative_apply, hb]
  map_add' := (henonDerivative β).map_add
  map_smul' := (henonDerivative β).map_smul
  continuous_toFun := (henonDerivative β).continuous
  continuous_invFun := by fun_prop

@[simp] theorem henonDerivativeEquiv_toContinuousLinearMap {β : ℝ} (hβ : β ≠ 0) :
    (henonDerivativeEquiv hβ : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = henonDerivative β := rfl

/-- An actual biholomorphic domain through the canonical exterior fixed point
and disjoint from the prescribed closed Euclidean ball. -/
theorem exists_biholomorphic_domain {β r : ℝ} {a : ℂ}
    (hβ : 0 < β) (hβq : β ≤ 1 / 4) (hr : 0 < r) (hra : r < ‖a‖) :
    ∃ Ω : Set (ℂ × ℂ), IsOpen Ω ∧ exteriorPoint β a ∈ Ω ∧
      (∀ v ∈ Ω, r < euclideanPairNorm v) ∧
      ∃ H : Ω ≃ₜ (ℂ × ℂ), ∃ h : (ℂ × ℂ) → ℂ × ℂ,
        DifferentiableOn ℂ h Ω ∧ (∀ x : Ω, H x = h x) ∧
        Differentiable ℂ (fun y : ℂ × ℂ => (H.symm y : ℂ × ℂ)) := by
  obtain ⟨m, htrap, hfix, hpout, hderiv⟩ := exists_henon_trapping hβ hβq hr hra
  let T := henonHomeomorph hβ.ne' a m
  let p := exteriorPoint β a
  let A := henonDerivativeEquiv hβ.ne'
  obtain ⟨δ, hδ, hδout⟩ := Metric.mem_nhds_iff.mp
    ((FlagTotalSpace.isOpen_exteriorEuclideanBall r).mem_nhds hpout)
  have hT : Differentiable ℂ (T : (ℂ × ℂ) → ℂ × ℂ) := differentiable_henonMap β a m
  have hTinv : Differentiable ℂ (T.symm : (ℂ × ℂ) → ℂ × ℂ) :=
    differentiable_henonInverse β a m
  have hc0 : BasinAvoidance.centered T p 0 = 0 := BasinAvoidance.centered_zero T hfix
  have hcd : HasFDerivAt (BasinAvoidance.centered T p : (ℂ × ℂ) → ℂ × ℂ)
      (A : (ℂ × ℂ) →L[ℂ] ℂ × ℂ) 0 :=
    BasinAvoidance.hasFDerivAt_centered_zero T p _ hderiv
  obtain ⟨ρ, hρ, hρδ, _hρinv, H, h, hh, hH, hInv, _h0⟩ :=
    SmallScaleBasin.exists_biholomorphic_basin (BasinAvoidance.centered T p) A
      (BasinAvoidance.differentiable_centered T p hT)
      (BasinAvoidance.differentiable_centered_symm T p hTinv) hc0 hcd hβ hβq hδ
      (norm_henonDerivative hβ.le)
  obtain ⟨G, g, hg, hG, hGinv⟩ :=
    BasinAvoidance.transfer_biholomorphic_basin T p ρ H h hh hH hInv
  let Ω := BasinGlobalization.basin T (ball p ρ)
  have hK : MapsTo T (FlagTotalSpace.closedEuclideanBall r)
      (FlagTotalSpace.closedEuclideanBall r) := by
    intro v hv
    exact (htrap v hv).le
  have hdis : Disjoint (ball p ρ) (FlagTotalSpace.closedEuclideanBall r) := by
    apply Set.disjoint_left.mpr
    intro v hv hKv
    have hvout : r < euclideanPairNorm v := hδout ((ball_subset_ball hρδ.le) hv)
    have hvle : euclideanPairNorm v ≤ r := hKv
    exact (not_le_of_gt hvout) hvle
  have hout := BasinAvoidance.basin_subset_compl T hK hdis
  refine ⟨Ω, BasinGlobalization.isOpen_basin T isOpen_ball,
    BasinGlobalization.subset_basin T _ (mem_ball_self hρ), ?_, G, g, hg, hG, hGinv⟩
  intro v hv
  exact lt_of_not_ge (hout hv)

/-- In particular, an injective entire map into the ball complement passes
through the chosen exterior point at the origin. -/
theorem exists_entire_injection {β r : ℝ} {a : ℂ}
    (hβ : 0 < β) (hβq : β ≤ 1 / 4) (hr : 0 < r) (hra : r < ‖a‖) :
    ∃ f : (ℂ × ℂ) → ℂ × ℂ, Differentiable ℂ f ∧ Function.Injective f ∧
      f 0 = exteriorPoint β a ∧ ∀ z, r < euclideanPairNorm (f z) := by
  obtain ⟨Ω, _hΩ, hp, hout, H, _h, _hh, _hH, hInv⟩ :=
    exists_biholomorphic_domain hβ hβq hr hra
  let q := H ⟨exteriorPoint β a, hp⟩
  let f : (ℂ × ℂ) → ℂ × ℂ := fun z => (H.symm (z + q) : ℂ × ℂ)
  refine ⟨f, hInv.comp (differentiable_id.add_const q), ?_, ?_, ?_⟩
  · intro x y hxy
    have heq : H.symm (x + q) = H.symm (y + q) := Subtype.ext hxy
    exact add_right_cancel (H.symm.injective heq)
  · change (H.symm (0 + H ⟨exteriorPoint β a, hp⟩) : ℂ × ℂ) = _
    simp
  · intro z
    exact hout _ (H.symm (z + q)).property

end AutomaticContinuity.ConcreteBallAvoidance
