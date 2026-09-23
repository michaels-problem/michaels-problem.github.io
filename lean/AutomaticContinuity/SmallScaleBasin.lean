import AutomaticContinuity.BasinGlobalization
import AutomaticContinuity.LocalBiholomorphicLimit
import AutomaticContinuity.FiniteHolomorphicRegularity
import AutomaticContinuity.SmallQuadraticRemainder
import AutomaticContinuity.SmallScaleKoenigsEstimates

set_option autoImplicit false

/-!
# Biholomorphic basins with arbitrary small similarity factor and local radius

An actual globally biholomorphic map fixing zero with derivative a linear
equivalence that shrinks every norm by a factor `0 < β ≤ 1/4` has an arbitrarily
small invariant ball whose
entry basin is biholomorphic to the full complex vector space. The local
conjugacy, inverse chart, invariant ball, and target exhaustion are constructed
from checked analytic estimates, not assumed.
-/

noncomputable section

namespace AutomaticContinuity.SmallScaleBasin

open Filter Metric Set BasinGlobalization KoenigsEstimates
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem tendsto_linear_pow_zero (A : E ≃L[ℂ] E)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (x : E) :
    Tendsto (fun n : ℕ => (A.toHomeomorph ^ n) x) atTop (𝓝 0) := by
  have hn : ∀ n : ℕ, ‖(A.toHomeomorph ^ n) x‖ = β ^ n * ‖x‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Homeomorph.mul_apply]
      change ‖A ((A.toHomeomorph ^ n) x)‖ = _
      rw [hA, ih, pow_succ]
      ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [hn]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const ‖x‖

/-- A genuine local conjugacy chart and a local contraction provide an
invariant ball and a biholomorphism of its entire entry basin. -/
theorem globalize_conjugating_chart (T : E ≃ₜ E) (A : E ≃L[ℂ] E)
    (hT : Differentiable ℂ (T : E → E))
    (hTinv : Differentiable ℂ (T.symm : E → E))
    {β δ : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hδ : 0 < δ)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖)
    (e : OpenPartialHomeomorph E E) {R : ℝ} (hR : 0 < R)
    (he0 : e 0 = 0) (hs0 : (0 : E) ∈ e.source)
    (hed : DifferentiableOn ℂ e (ball 0 R))
    (heid : DifferentiableOn ℂ e.symm e.target)
    (hcontract : ∀ x ∈ ball (0 : E) R, ‖T x‖ ≤ (1 / 3 : ℝ) * ‖x‖)
    (hconj : ∀ x ∈ ball (0 : E) R, e (T x) = A (e x)) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ MapsTo T (ball (0 : E) r) (ball 0 r) ∧
      ∃ H : basin T (ball (0 : E) r) ≃ₜ E, ∃ h : E → E,
        DifferentiableOn ℂ h (basin T (ball (0 : E) r)) ∧
        (∀ x : basin T (ball (0 : E) r), H x = h x) ∧
        Differentiable ℂ (fun y : E => (H.symm y : E)) ∧ h 0 = 0 := by
  obtain ⟨s, hs, hsub'⟩ := Metric.mem_nhds_iff.mp
    ((e.open_source.inter isOpen_ball).mem_nhds ⟨hs0, mem_ball_self hR⟩)
  let r := min s (δ / 2)
  have hr : 0 < r := lt_min hs (half_pos hδ)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hsub : ball (0 : E) r ⊆ e.source ∩ ball 0 R :=
    (ball_subset_ball (min_le_left _ _)).trans hsub'
  have hTU : MapsTo T (ball (0 : E) r) (ball 0 r) := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx ⊢
    have hbound := hcontract x (hsub (by simpa only [mem_ball, dist_zero_right] using hx)).2
    exact hbound.trans_lt ((by nlinarith [norm_nonneg x] :
      (1 / 3 : ℝ) * ‖x‖ ≤ ‖x‖).trans_lt hx)
  let D : LocalConjugacy T A.toHomeomorph (ball (0 : E) r) (e '' ball 0 r) :=
    LocalConjugacy.ofOpenPartialHomeomorph e isOpen_ball (fun _ hx => (hsub hx).1)
      hTU (fun x hx => hconj x (hsub hx).2)
  have h0 : (0 : E) ∈ e '' ball (0 : E) r := ⟨0, mem_ball_self hr, he0⟩
  have hex := D.target_exhaustion_of_tendsto_zero h0 (tendsto_linear_pow_zero A hβ hβ1 hA)
  have hh : DifferentiableOn ℂ D.toFun (ball (0 : E) r) :=
    hed.mono (fun _ hx => (hsub hx).2)
  have hk : DifferentiableOn ℂ D.invFun (e '' ball (0 : E) r) :=
    heid.mono (by rintro _ ⟨x, hx, rfl⟩; exact e.mapsTo (hsub hx).1)
  obtain ⟨H, h, hhd, hHeq, hHid, hlocal⟩ := D.exists_biholomorphic_globalization hex
    hT hTinv A.differentiable A.symm.differentiable hh hk
  exact ⟨r, hr, hrδ, hTU, H, h, hhd, hHeq, hHid,
    (hlocal 0 (mem_ball_self hr)).trans he0⟩

variable [ProperSpace E]

/-- The complete small-scale basin theorem, with prescribed upper bound on
the local radius. All local quadratic bounds and
local inverse/conjugacy data are constructed from complex differentiability
and the stated derivative at zero. -/
theorem exists_biholomorphic_basin (T : E ≃ₜ E) (A : E ≃L[ℂ] E)
    (hT : Differentiable ℂ (T : E → E))
    (hTinv : Differentiable ℂ (T.symm : E → E)) (hT0 : T 0 = 0)
    (hTd : HasFDerivAt (T : E → E) (A : E →L[ℂ] E) 0)
    {β δ : ℝ} (hβ : 0 < β) (hβquarter : β ≤ 1 / 4) (hδ : 0 < δ)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) :
    ∃ r : ℝ, 0 < r ∧ r < δ ∧ MapsTo T (ball (0 : E) r) (ball 0 r) ∧
      ∃ H : basin T (ball (0 : E) r) ≃ₜ E, ∃ h : E → E,
        DifferentiableOn ℂ h (basin T (ball (0 : E) r)) ∧
        (∀ x : basin T (ball (0 : E) r), H x = h x) ∧
        Differentiable ℂ (fun y : E => (H.symm y : E)) ∧ h 0 = 0 := by
  obtain ⟨r, C, hr, hC, hsmall, hrem⟩ :=
    HolomorphicQuadraticRemainder.exists_quadratic_remainder_le T A hT hT0 hTd
      (by positivity : 0 < β / 3)
  have hcontract := SmallScaleKoenigsEstimates.contraction_of_quadratic_remainder
    hA hC hsmall hrem
  have hcontract' : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ (1 / 3 : ℝ) * ‖x‖ := by
    intro x hx
    exact (hcontract x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith : (4 / 3 : ℝ) * β ≤ 1 / 3) (norm_nonneg x))
  obtain ⟨e, he, hed, he0, hs0, _ht0, _hsource, heid⟩ :=
    NormalizedHolomorphicLimit.exists_normalized_localBiholomorph (rescaledIterate A T) hr
      (fun n => (differentiable_rescaledIterate A hT n).differentiableOn)
      (SmallScaleKoenigsEstimates.norm_rescaledIterate_sub_le hβ hβquarter hA
        hr.le hC hcontract hrem)
      (rescaledIterate_zero A hT0) (hasFDerivAt_rescaledIterate_zero A hT0 hTd)
      (fun n => FiniteHolomorphicRegularity.continuousOn_fderiv isOpen_ball
        (differentiable_rescaledIterate A hT n).differentiableOn)
  apply globalize_conjugating_chart T A hT hTinv hβ.le (by linarith : β < 1) hδ hA
    e hr he0 hs0 hed heid (fun x hx => hcontract' x (ball_subset_closedBall hx))
  intro x hx
  have hx' := ball_subset_closedBall hx
  have hTx : T x ∈ closedBall (0 : E) r := by
    simpa only [Function.iterate_one] using (norm_iterate_le hr.le hcontract' hx' 1).2
  have hleft := he.tendsto_at hTx
  have hshift : Tendsto (fun n => rescaledIterate A T (n + 1) x) atTop (𝓝 (e x)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (he.tendsto_at hx')
  have hright : Tendsto (fun n => A (rescaledIterate A T (n + 1) x)) atTop (𝓝 (A (e x))) :=
    A.continuous.continuousAt.tendsto.comp hshift
  have heq : (fun n => rescaledIterate A T n (T x)) =
      (fun n => A (rescaledIterate A T (n + 1) x)) :=
    funext fun n => rescaledIterate_comp A T n x
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end AutomaticContinuity.SmallScaleBasin
