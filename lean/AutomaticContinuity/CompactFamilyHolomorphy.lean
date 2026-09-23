import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false

/-! # Holomorphy of compact continuous-function families

Joint continuity and pointwise holomorphy imply holomorphy into the Banach
space of continuous functions on a compact parameter space. The proof uses
the actual Banach-valued Cauchy transform and commutation with evaluation.
No uniform derivative estimate or additional analytic-family hypothesis is
assumed.
-/

noncomputable section
namespace AutomaticContinuity.CompactFamilyHolomorphy
open Complex MeasureTheory Set Filter Metric
open scoped Interval Topology NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem map_circleIntegral (L : E →L[ℂ] F) {f : ℂ → E} {z : ℂ} {r : ℝ}
    (hf : CircleIntegrable f z r) :
    L (∮ w in C(z,r), f w) = ∮ w in C(z,r), L (f w) := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm hf.out]
  congr 1
  funext t
  exact L.map_smul _ _

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Sup-norm continuity and holomorphy of every evaluation suffice. -/
theorem differentiableOn_of_continuousOn (F : ℂ → C(K,E)) {O : Set ℂ}
    (hO : IsOpen O) (hF : ContinuousOn F O)
    (hhol : ∀ x : K, DifferentiableOn ℂ (fun z => F z x) O) :
    DifferentiableOn ℂ F O := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hz)
  lift r to ℝ≥0 using hr.le
  have hc : ContinuousOn F (closedBall z r) := hF.mono hball
  have hci : CircleIntegrable F z r := (hc.mono sphere_subset_closedBall).circleIntegrable r.coe_nonneg
  let G : ℂ → C(K,E) := fun y => (2 * Real.pi * I : ℂ)⁻¹ •
    ∮ w in C(z,(r:ℝ)), (w-y)⁻¹ • F w
  have hG : AnalyticAt ℂ G z := (hasFPowerSeriesOn_cauchy_integral hci hr).analyticAt
  have hEq : G =ᶠ[𝓝 z] F := by
    filter_upwards [Metric.ball_mem_nhds z hr] with y hy
    apply ContinuousMap.ext
    intro x
    have hkernel : ContinuousOn (fun w : ℂ => (w-y)⁻¹) (sphere z r) :=
      (continuousOn_id.sub continuousOn_const).inv₀ (fun w hw =>
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hw (ne_of_lt hy)))
    have hki : CircleIntegrable (fun w => (w-y)⁻¹ • F w) z r :=
      (hkernel.smul (hc.mono sphere_subset_closedBall)).circleIntegrable r.coe_nonneg
    change (ContinuousMap.evalCLM ℂ x) (G y) = F y x
    simp only [G, map_smul]
    rw [map_circleIntegral _ hki]
    simp only [map_smul, ContinuousMap.evalCLM_apply]
    apply Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty hy
    · exact (hhol x).continuousOn.mono hball
    · intro w hw
      exact (hhol x).differentiableAt
        (hO.mem_nhds (hball (ball_subset_closedBall hw.1)))
  exact (hG.differentiableAt.congr_of_eventuallyEq hEq.symm).differentiableWithinAt

/-- A jointly continuous family of pointwise holomorphic functions is
holomorphic for the actual sup norm on `C(K,E)`. -/
theorem differentiableOn_of_jointly_continuous (F : ℂ → C(K,E)) {O : Set ℂ}
    (hO : IsOpen O)
    (hjoint : ContinuousOn (fun p : ℂ × K => F p.1 p.2) (O ×ˢ univ))
    (hhol : ∀ x : K, DifferentiableOn ℂ (fun z => F z x) O) :
    DifferentiableOn ℂ F O :=
  differentiableOn_of_continuousOn F hO
    (ContinuousMap.continuousOn_of_continuousOn_uncurry F hjoint) hhol

end AutomaticContinuity.CompactFamilyHolomorphy
