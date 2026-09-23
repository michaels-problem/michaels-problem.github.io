import AutomaticContinuity.SmallScaleBasin

set_option autoImplicit false

/-!
# Attraction in parameter-preserving linear fibres

A uniform norm contraction in the linear fibres gives actual convergence to
the zero section. No continuity or holomorphic dependence of the linear family
is needed beyond the given product homeomorphism.
-/

noncomputable section

namespace AutomaticContinuity.LinearParameterAttraction

open Filter
open scoped Topology

variable {P E : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem tendsto_linear_fiber_pow
    (T : (P × E) ≃ₜ (P × E)) (A : P → E ≃L[ℂ] E)
    (hT : ∀ p y, T (p, y) = (p, A p y))
    {U : Set P} {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ∀ p ∈ U, ∀ y : E, ‖A p y‖ ≤ q * ‖y‖)
    {p : P} (hp : p ∈ U) (y : E) :
    Tendsto (fun n : ℕ => (T ^ n) (p, y)) atTop (𝓝 (p, 0)) := by
  have heq : ∀ n : ℕ, (T ^ n) (p, y) = (p, (A p)^[n] y) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Homeomorph.mul_apply, ih, hT, Function.iterate_succ_apply']
  have hnorm : ∀ n : ℕ, ‖(A p)^[n] y‖ ≤ q ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖A p ((A p)^[n] y)‖ ≤ q * ‖(A p)^[n] y‖ := hA p hp _
        _ ≤ q * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hattract : Tendsto (fun n : ℕ => (A p)^[n] y) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖y‖)
  simp_rw [heq]
  rw [nhds_prod_eq]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).prodMk hattract

end AutomaticContinuity.LinearParameterAttraction
