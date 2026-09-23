import AutomaticContinuity.SchwarzDerivativeBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# Continuous and strict derivatives of finite-dimensional holomorphic maps

Compactness of closed balls and the Schwarz derivative estimate turn uniform
continuity of a holomorphic map into continuity of its Fréchet derivative.
The source is any proper complex normed space. No completeness assumption on
the target, power-series representation, or separate holomorphy theorem is used.
-/

namespace AutomaticContinuity.FiniteHolomorphicRegularity

open Filter Metric Set
open scoped Topology

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {f : E → F} {U : Set E} {x : E}

/-- On a proper complex normed source, complex differentiability on an open
set implies continuity of the derivative at each point of that set. -/
theorem continuousAt_fderiv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : x ∈ U) : ContinuousAt (fderiv ℂ f) x := by
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R : ℝ := a / 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hbig : closedBall x (2 * R) ⊆ U := by
    apply Set.Subset.trans _ hsub
    apply closedBall_subset_ball
    dsimp [R]
    linarith
  have hsmall : ball x R ⊆ U := by
    apply Set.Subset.trans _ hbig
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have huc := (isCompact_closedBall x (2 * R)).uniformContinuousOn_of_continuous
    (hf.continuousOn.mono hbig)
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc
    (ε * R / 4) (by positivity)
  refine ⟨min R δ, lt_min hR hδ, ?_⟩
  intro y hy
  have hyR : dist y x < R := lt_of_lt_of_le hy (min_le_left _ _)
  have hyδ : dist y x < δ := lt_of_lt_of_le hy (min_le_right _ _)
  have hyU : y ∈ U := hsmall hyR
  let T : E → E := fun z => z - x + y
  have hTdist (z : E) : dist (T z) z = dist y x := by
    dsimp [T]
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hTbig : ∀ z ∈ ball x R, T z ∈ closedBall x (2 * R) := by
    intro z hz
    change dist (T z) x ≤ 2 * R
    calc
      dist (T z) x ≤ dist (T z) z + dist z x := dist_triangle _ _ _
      _ ≤ 2 * R := by rw [hTdist]; have hz' : dist z x < R := hz; linarith
  have hTder (z : E) : HasFDerivAt T (ContinuousLinearMap.id ℂ E) z := by
    simpa only [T, sub_eq_add_neg, id_eq] using
      ((hasFDerivAt_id z).add_const (-x)).add_const y
  have hg : DifferentiableOn ℂ (f ∘ T) (ball x R) := by
    intro z hz
    exact ((hf.differentiableAt (hU.mem_nhds (hbig (hTbig z hz)))).comp z
      (hTder z).differentiableAt).differentiableWithinAt
  have hbound : ∀ z ∈ ball x R, ‖(f ∘ T) z - f z‖ ≤ ε * R / 4 := by
    intro z hz
    rw [← dist_eq_norm]
    apply le_of_lt
    apply hclose (T z) (hTbig z hz) z
    · exact (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith : R ≤ 2 * R))) hz
    · rwa [hTdist]
  have hder := SchwarzDerivativeBounds.norm_fderiv_sub_le_closedBall hg (hf.mono hsmall)
    hbound (show (0 : ℝ) < R from hR) (show x ∈ closedBall x 0 by simp)
  have hTx : T x = y := by simp [T]
  have hcomp : fderiv ℂ (f ∘ T) x = fderiv ℂ f y := by
    have hdy : HasFDerivAt f (fderiv ℂ f y) (T x) := by
      rw [hTx]
      exact (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    simpa only [ContinuousLinearMap.comp_id] using (hdy.comp x (hTder x)).fderiv
  rw [hcomp, sub_zero] at hder
  rw [dist_eq_norm]
  calc
    ‖fderiv ℂ f y - fderiv ℂ f x‖ ≤ 2 * (ε * R / 4) / R := hder
    _ = ε / 2 := by field_simp; ring
    _ < ε := by linarith

/-- Finite-dimensional holomorphic maps have continuous first derivatives. -/
theorem continuousOn_fderiv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U :=
  fun _ hx => (continuousAt_fderiv hU hf hx).continuousWithinAt

/-- The strict derivative required by the inverse function theorem follows
from complex differentiability on an open set with proper source. -/
theorem hasStrictFDerivAt (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hx : x ∈ U) : HasStrictFDerivAt f (fderiv ℂ f x) x := by
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hf.differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  · exact continuousAt_fderiv hU hf hx

end AutomaticContinuity.FiniteHolomorphicRegularity
