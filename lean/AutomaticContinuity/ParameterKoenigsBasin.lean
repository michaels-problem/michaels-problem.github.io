import AutomaticContinuity.ParameterBasin

set_option autoImplicit false

/-!
# A normalized joint conjugacy produces an actual family of basins

The local inverse function theorem supplies a source cylinder. Uniform fibre
contraction makes that actual cylinder invariant. Its entry basin is then
biholomorphic, over the parameter base, to the full product with the fibre.
-/

noncomputable section

namespace AutomaticContinuity.ParameterBasin

open Set Filter Metric BasinGlobalization
open scoped Topology

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace P] [ProperSpace E]

/-- An actual biholomorphic trivialization over a base, with holomorphic
ambient representatives in both directions. -/
def HasHolomorphicProductTrivialization (Ω : Set (P × E)) (B : Set P) : Prop :=
  ∃ F : Ω ≃ₜ (B ×ˢ (univ : Set E)), ∃ h k : P × E → P × E,
    DifferentiableOn ℂ h Ω ∧ DifferentiableOn ℂ k (B ×ˢ univ) ∧
    (∀ z : Ω, (F z : P × E) = h z) ∧
    (∀ z : B ×ˢ (univ : Set E), (F.symm z : P × E) = k z) ∧
    (∀ z : Ω, (F z : P × E).1 = (z : P × E).1) ∧
    (∀ z : B ×ˢ (univ : Set E), (F.symm z : P × E).1 = (z : P × E).1)

/-- This constructs the invariant source cylinder from a normalized jointly
holomorphic conjugacy, rather than assuming an already global basin chart. -/
theorem exists_of_normalized_conjugacy
    (T A : (P × E) ≃ₜ (P × E)) {U : Set P} (hU : IsOpen U)
    {p : P} (hp : p ∈ U) {r q : ℝ} (hr : 0 < r) (hq : q ≤ 1)
    (hTf : ∀ z, (T z).1 = z.1) (hAf : ∀ z, (A z).1 = z.1)
    (hT : Differentiable ℂ (T : P × E → P × E))
    (hTinv : Differentiable ℂ (T.symm : P × E → P × E))
    (hA : Differentiable ℂ (A : P × E → P × E))
    (hAinv : Differentiable ℂ (A.symm : P × E → P × E))
    (hbound : ∀ z ∈ U ×ˢ closedBall (0 : E) r, ‖(T z).2‖ ≤ q * ‖z.2‖)
    (hattract : ∀ a ∈ U, ∀ y : E,
      Tendsto (fun n : ℕ => (A ^ n) (a, y)) atTop (𝓝 (a, 0)))
    {H : P × E → E} (hH : DifferentiableOn ℂ H (U ×ˢ ball 0 r))
    (hzero : ∀ a ∈ U, H (a, 0) = 0)
    (hder : ∀ a ∈ U, HasFDerivAt (fun x => H (a, x)) (ContinuousLinearMap.id ℂ E) 0)
    (hconj : ∀ z ∈ U ×ˢ ball (0 : E) r,
      NormalizedParameterChart.lift H (T z) = A (NormalizedParameterChart.lift H z)) :
    ∃ δ > 0, ball p δ ⊆ U ∧
      IsOpen (basin T (ball p δ ×ˢ ball (0 : E) δ)) ∧
      basin T (ball p δ ×ˢ ball (0 : E) δ) ⊆ ball p δ ×ˢ univ ∧
      HasHolomorphicProductTrivialization
        (basin T (ball p δ ×ˢ ball (0 : E) δ)) (ball p δ) := by
  obtain ⟨e, he, _, _, hsource, hed, heid, hef, heif, _, _, δ, hδ, heS⟩ :=
    NormalizedParameterChart.exists_localBiholomorph hU hr hH hzero hder hp
  have hbase : ball p δ ⊆ U := by
    intro a ha
    have hm : (a, (0 : E)) ∈ e.source := by rw [heS]; exact ⟨ha, mem_ball_self hδ⟩
    exact (hsource hm).1
  have hinv : MapsTo T e.source e.source := by
    intro z hz
    have hzr := hsource hz
    have hzδ : z ∈ ball p δ ×ˢ ball (0 : E) δ := heS ▸ hz
    rw [heS]
    refine ⟨by simpa only [hTf] using hzδ.1, ?_⟩
    rw [mem_ball, dist_zero_right]
    calc
      ‖(T z).2‖ ≤ q * ‖z.2‖ := hbound z ⟨hzr.1, ball_subset_closedBall hzr.2⟩
      _ ≤ 1 * ‖z.2‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      _ < δ := by simpa only [one_mul, mem_ball, dist_zero_right] using hzδ.2
  let D : LocalConjugacy T A e.source e.target := {
    toFun := e
    invFun := e.symm
    source_open := e.open_source
    target_open := e.open_target
    mapsTo := e.mapsTo
    invMapsTo := e.symm.mapsTo
    left_inv := fun _ hz => e.left_inv hz
    right_inv := fun _ hz => e.right_inv hz
    continuousOn_toFun := e.continuousOn
    continuousOn_invFun := e.symm.continuousOn
    forward_invariant := hinv
    conjugacy := fun z hz => by simpa only [he] using hconj z (hsource hz) }
  have htbase : e.target ⊆ ball p δ ×ˢ (univ : Set E) := by
    intro z hz
    have hi : e.symm z ∈ e.source := e.symm.mapsTo hz
    rw [heS] at hi
    exact ⟨by simpa only [heif z hz] using hi.1, mem_univ _⟩
  have htzero : ∀ a ∈ ball p δ, (a, (0 : E)) ∈ e.target := by
    intro a ha
    have hm : (a, (0 : E)) ∈ e.source := by rw [heS]; exact ⟨ha, mem_ball_self hδ⟩
    have hfix : e (a, (0 : E)) = (a, (0 : E)) := by
      rw [he]
      simp only [NormalizedParameterChart.lift, hzero a (hbase ha)]
    simpa only [hfix] using e.mapsTo hm
  obtain ⟨F, h, k, hhd, hkd, hF, hFi, hFf, hFif, _⟩ :=
    exists_biholomorphic_product D hTf hAf (fun z _ => hef z) htbase htzero
      (fun a ha => hattract a (hbase ha)) hT hTinv hA hAinv hed heid
  have htriv : HasHolomorphicProductTrivialization (basin T e.source) (ball p δ) :=
    ⟨F, h, k, hhd, hkd, hF, hFi, hFf, hFif⟩
  refine ⟨δ, hδ, hbase, isOpen_basin T (isOpen_ball.prod isOpen_ball),
    basin_subset_product T hTf (fun _ hz => ⟨hz.1, mem_univ _⟩), ?_⟩
  simpa only [heS] using htriv

end AutomaticContinuity.ParameterBasin
