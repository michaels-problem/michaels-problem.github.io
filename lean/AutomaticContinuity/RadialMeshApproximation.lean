import AutomaticContinuity.EuclideanTrajectoryStability
import AutomaticContinuity.FiniteFlowLocal

set_option autoImplicit false

/-!
# Actual finite mesh products track protected and radial trajectories

Every conclusion concerns a finite composition of actual equivalences.
Euler and field errors are required only in fixed tubes around the reference
trajectories. A first-exit bootstrap controls all intermediate points. The
inverse estimate uses the reversed actual inverse factors.
-/

noncomputable section

namespace AutomaticContinuity.RadialMeshApproximation

open Set FiniteFlowLocal EuclideanTrajectoryStability DiscreteTrajectoryStability

abbrev Pair := ℂ × ℂ

/-- A unit-time mesh can meet any prescribed uniform positive step bound. -/
theorem exists_unit_mesh {τ : ℝ} (hτ : 0 < τ) :
    ∃ (N : ℕ) (h : ℝ), 0 < N ∧ 0 < h ∧ h < τ ∧ (N : ℝ) * h = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / τ)
  have hNp : (0 : ℝ) < N := (one_div_pos.mpr hτ).trans hN
  refine ⟨N, 1 / N, Nat.cast_pos.mp hNp, one_div_pos.mpr hNp, ?_, ?_⟩
  · apply (div_lt_iff₀ hNp).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hτ).mp hN
  · field_simp

theorem radial_prefix_control (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {c h δ η ρ : ℝ}
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (horizon : (N : ℝ) * h ≤ 1) (hsmall : (δ + η) * Real.exp c < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - radialPoint c h j w) < ρ →
      euclideanPairNorm (e j z - z - h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - radialPoint c h j w) < ρ →
      euclideanPairNorm (V j z - radialField c h j z) ≤ δ) :
    ∀ j ≤ N,
      euclideanPairNorm (compose e j w - radialPoint c h j w) ≤
        errorBound 0 (δ + η) c h j ∧
      euclideanPairNorm (compose e j w - radialPoint c h j w) < ρ := by
  apply EuclideanTrajectoryStability.trajectory_bootstrap
    (fun i => e i) V (radialField c h) (fun j => compose e j w)
    (fun j => radialPoint c h j w) (by norm_num : (0 : ℝ) ≤ 0) hδ hη hc hh
    (by simp) horizon (by simpa using hsmall)
  · intro j _; rfl
  · intro j _; exact radialPoint_succ hc hh j w
  · exact hEuler
  · exact happrox
  · intro j _ z _
    exact radialField_error_le hc hh j z (radialPoint c h j w)

/-- A unit-time finite product approximates the prescribed dilation. The
constant involves the radial comparison field, not a polynomial Lipschitz constant. -/
theorem radial_compose_error (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {c h δ η ρ : ℝ}
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmesh : (N : ℝ) * h = 1) (hsmall : (δ + η) * Real.exp c < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - radialPoint c h j w) < ρ →
      euclideanPairNorm (e j z - z - h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - radialPoint c h j w) < ρ →
      euclideanPairNorm (V j z - radialField c h j z) ≤ δ) :
    euclideanPairNorm (compose e N w - (1 + c) • w) ≤ (δ + η) * Real.exp c := by
  have hb := (radial_prefix_control e V N w hc hh hδ hη hmesh.le hsmall hEuler happrox N le_rfl).1
  rw [radialPoint_terminal hmesh] at hb
  simpa only [errorBound, hmesh, zero_add, one_mul] using hb

theorem protected_prefix_control (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {h δ η ρ : ℝ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (horizon : (N : ℝ) * h ≤ 1) (hsmall : δ + η < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (e j z - z - h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (V j z) ≤ δ) :
    ∀ j ≤ N,
      euclideanPairNorm (compose e j w - w) ≤ errorBound 0 (δ + η) 0 h j ∧
      euclideanPairNorm (compose e j w - w) < ρ := by
  apply EuclideanTrajectoryStability.trajectory_bootstrap
    (fun i => e i) V (fun _ _ => 0) (fun j => compose e j w) (fun _ => w)
    (by norm_num : (0 : ℝ) ≤ 0) hδ hη (by norm_num : (0 : ℝ) ≤ 0) hh
    (by simp) horizon (by simpa using hsmall)
  · intro j _; rfl
  · intro j _; simp
  · exact hEuler
  · intro j hj z hz
    simpa only [sub_zero] using happrox j hj z hz
  · intro j _ z _; simp

theorem protected_compose_error (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {h δ η ρ : ℝ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmesh : (N : ℝ) * h = 1) (hsmall : δ + η < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (e j z - z - h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (V j z) ≤ δ) :
    euclideanPairNorm (compose e N w - w) ≤ δ + η := by
  have hb := (protected_prefix_control e V N w hh hδ hη hmesh.le hsmall hEuler happrox N le_rfl).1
  simpa only [errorBound, hmesh, zero_add, one_mul, mul_zero, Real.exp_zero, mul_one] using hb

/-- Reverse-order inverse factors, with their actual equivalence structure. -/
def inverseFactors (e : ℕ → Pair ≃ Pair) (N : ℕ) (j : ℕ) : Pair ≃ Pair :=
  (e (N - 1 - j)).symm

theorem inverse_prefix_identity (e : ℕ → Pair ≃ Pair) (N : ℕ) (w : Pair) :
    ∀ j ≤ N, compose (inverseFactors e N) j w =
      compose e (N - j) ((compose e N).symm w) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjle : j ≤ N := by omega
    have hidx : N - 1 - j = N - (j + 1) := by omega
    have hpred : N - j = N - (j + 1) + 1 := by omega
    rw [compose_succ_apply, ih hjle]
    change (e (N - 1 - j)).symm (compose e (N - j) ((compose e N).symm w)) = _
    rw [hidx, hpred, compose_succ_apply, Equiv.symm_apply_apply]

theorem inverseFactors_terminal (e : ℕ → Pair ≃ Pair) (N : ℕ) (w : Pair) :
    compose (inverseFactors e N) N w = (compose e N).symm w := by
  simpa using inverse_prefix_identity e N w N le_rfl

theorem inverse_protected_prefix_control (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {h δ η ρ : ℝ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (horizon : (N : ℝ) * h ≤ 1) (hsmall : δ + η < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm ((e j).symm z - z + h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (V j z) ≤ δ) :
    ∀ j ≤ N,
      euclideanPairNorm (compose (inverseFactors e N) j w - w) ≤ errorBound 0 (δ + η) 0 h j ∧
      euclideanPairNorm (compose (inverseFactors e N) j w - w) < ρ := by
  apply protected_prefix_control (inverseFactors e N) (fun i z => -V (N - 1 - i) z)
    N w hh hδ hη horizon hsmall
  · intro j hj z hz
    simpa only [inverseFactors, smul_neg, sub_neg_eq_add] using hEuler (N - 1 - j) (by omega) z hz
  · intro j hj z hz
    simpa [euclideanPairNorm] using happrox (N - 1 - j) (by omega) z hz

/-- The inverse displacement bound concerns the actual inverse of the full
mesh product, and every reversed intermediate point stays in the protected tube. -/
theorem inverse_protected_compose_error (e : ℕ → Pair ≃ Pair) (V : ℕ → Pair → Pair)
    (N : ℕ) (w : Pair) {h δ η ρ : ℝ}
    (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmesh : (N : ℝ) * h = 1) (hsmall : δ + η < ρ)
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm ((e j).symm z - z + h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - w) < ρ →
      euclideanPairNorm (V j z) ≤ δ) :
    euclideanPairNorm ((compose e N).symm w - w) ≤ δ + η := by
  have hb := (inverse_protected_prefix_control e V N w hh hδ hη hmesh.le hsmall
    hEuler happrox N le_rfl).1
  rw [inverseFactors_terminal] at hb
  simpa only [errorBound, hmesh, zero_add, one_mul, mul_zero, Real.exp_zero, mul_one] using hb

end AutomaticContinuity.RadialMeshApproximation
