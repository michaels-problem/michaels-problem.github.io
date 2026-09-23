import AutomaticContinuity.HolomorphicQuadraticRemainder
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

/-!
# Uniform quadratic time expansion on compact parameter sets

A jointly continuous, time-holomorphic family with a prescribed derivative at
time zero has a uniform quadratic remainder on every compact parameter set.
The proof uses the one-variable higher-order Schwarz estimate. Applied to a
finite composition of complete flows, it avoids bounds on every intermediate
point of the splitting composition.
-/

noncomputable section

namespace AutomaticContinuity.CompactFlowTaylor

open Filter Metric Set
open scoped Topology

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The compact set may include real time parameters, complex base parameters,
and starting points. No vector-space structure on this parameter space is
needed. Holomorphy is required only in the flow-time variable. -/
theorem exists_uniform_quadratic_remainder (F : ℂ × P → E) (b V : P → E)
    {K : Set P} (hK : IsCompact K)
    (hF : ContinuousOn F (closedBall (0 : ℂ) 1 ×ˢ K))
    (hb : ContinuousOn b K) (hV : ContinuousOn V K)
    (hzero : ∀ p ∈ K, F (0, p) = b p)
    (hhol : ∀ p ∈ K, DifferentiableOn ℂ (fun t => F (t, p)) (ball 0 1))
    (hderiv : ∀ p ∈ K, HasDerivAt (fun t => F (t, p)) (V p) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ t : ℂ, ‖t‖ < 1 →
      ‖F (t, p) - b p - t • V p‖ ≤ C * ‖t‖ ^ 2 := by
  let R : ℂ × P → E := fun z => F z - b z.2 - z.1 • V z.2
  have hbc : ContinuousOn (fun z : ℂ × P => b z.2) (closedBall (0 : ℂ) 1 ×ˢ K) :=
    hb.comp continuousOn_snd (fun _ hz => hz.2)
  have hVc : ContinuousOn (fun z : ℂ × P => V z.2) (closedBall (0 : ℂ) 1 ×ˢ K) :=
    hV.comp continuousOn_snd (fun _ hz => hz.2)
  have hRc : ContinuousOn R (closedBall (0 : ℂ) 1 ×ˢ K) :=
    (hF.sub hbc).sub (continuousOn_fst.smul hVc)
  obtain ⟨C₀, hC₀⟩ := ((isCompact_closedBall (0 : ℂ) 1).prod hK).exists_bound_of_continuousOn hRc
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro p hp t ht
  let r : ℂ → E := fun s => R (s, p)
  have hr0 : r 0 = 0 := by simp [r, R, hzero p hp]
  have hrd : HasDerivAt r (0 : E) 0 := by
    simpa only [one_smul, sub_zero, sub_self] using!
      ((hderiv p hp).sub_const (b p)).sub
        ((hasDerivAt_id (0 : ℂ)).smul_const (V p))
  have hrhol : DifferentiableOn ℂ r (ball 0 1) :=
    ((hhol p hp).sub_const (b p)).sub
      (differentiableOn_id.smul_const (V p))
  have hrmap : MapsTo r (ball (0 : ℂ) 1) (closedBall (r 0) C) := by
    intro s hs
    rw [mem_closedBall, hr0, dist_zero_right]
    exact (hC₀ (s, p) ⟨ball_subset_closedBall hs, hp⟩).trans (le_max_left _ _)
  have hlo : (fun s => r s - r 0) =o[𝓝 (0 : ℂ)] (fun s => ‖s - 0‖ ^ (1 : ℕ)) := by
    simpa only [smul_zero, sub_zero, pow_one] using hrd.isLittleO.norm_right
  have hschwarz := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    hrhol hrmap hlo (show t ∈ ball (0 : ℂ) 1 by simpa using ht)
  simpa only [hr0, dist_zero_right, div_one, Nat.reduceAdd] using hschwarz

/-- Uniform first-order accuracy with one positive step-size bound. This bound
works for every point of the compact parameter set and every complex time in
the punctured disk, including negative real times. -/
theorem exists_uniform_first_order_step (F : ℂ × P → E) (b V : P → E)
    {K : Set P} (hK : IsCompact K)
    (hF : ContinuousOn F (closedBall (0 : ℂ) 1 ×ˢ K))
    (hb : ContinuousOn b K) (hV : ContinuousOn V K)
    (hzero : ∀ p ∈ K, F (0, p) = b p)
    (hhol : ∀ p ∈ K, DifferentiableOn ℂ (fun t => F (t, p)) (ball 0 1))
    (hderiv : ∀ p ∈ K, HasDerivAt (fun t => F (t, p)) (V p) 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ p ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      ‖F (t, p) - b p - t • V p‖ < η * ‖t‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_quadratic_remainder F b V hK hF hb hV hzero hhol hderiv
  let τ : ℝ := min 1 (η / (C + 1))
  have hτ : 0 < τ := lt_min zero_lt_one (div_pos hη (by positivity))
  refine ⟨τ, hτ, ?_⟩
  intro p hp t ht htτ
  have ht1 : ‖t‖ < 1 := htτ.trans_le (min_le_left _ _)
  have hCt : C * ‖t‖ < η := by
    have hh : ‖t‖ * (C + 1) < η :=
      (lt_div_iff₀ (by positivity : 0 < C + 1)).mp (htτ.trans_le (min_le_right _ _))
    nlinarith
  calc
    ‖F (t, p) - b p - t • V p‖ ≤ C * ‖t‖ ^ 2 := hbound p hp t ht1
    _ = (C * ‖t‖) * ‖t‖ := by ring
    _ < η * ‖t‖ := mul_lt_mul_of_pos_right hCt ht

end AutomaticContinuity.CompactFlowTaylor
