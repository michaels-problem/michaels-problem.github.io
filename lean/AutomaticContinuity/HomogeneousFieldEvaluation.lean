import AutomaticContinuity.HomogeneousFieldDecomposition
import AutomaticContinuity.DirectionalCompleteFlows

set_option autoImplicit false

/-! # The polynomial decomposition as an identity of explicit complete fields -/

noncomputable section

namespace AutomaticContinuity.HomogeneousFieldDecomposition

open MvPolynomial HomogeneousPowerBasis
open scoped BigOperators

def evaluation (w : ℂ × ℂ) : Field →ₗ[ℂ] (ℂ × ℂ) :=
  (((aeval ![w.1, w.2] : Poly →ₐ[ℂ] ℂ).toLinearMap).comp
    (LinearMap.fst ℂ Poly Poly)).prod
  (((aeval ![w.1, w.2] : Poly →ₐ[ℂ] ℂ).toLinearMap).comp
    (LinearMap.snd ℂ Poly Poly))

@[simp] theorem evaluation_apply (w : ℂ × ℂ) (P Q : Poly) :
    evaluation w (P, Q) = (eval ![w.1, w.2] P, eval ![w.1, w.2] Q) := by
  rfl

theorem evaluation_shear (w : ℂ × ℂ) (s c : ℂ) (d : ℕ) :
    evaluation w (c • shear s d) = DirectionalCompleteFlows.shearField s d c w := by
  apply Prod.ext <;>
    simp [evaluation, shear, linearForm, DirectionalCompleteFlows.shearField,
      DirectionalCompleteFlows.linearForm, DirectionalCompleteFlows.direction,
      smul_eq_mul]
  all_goals ring

theorem evaluation_overshear (w : ℂ × ℂ) (s c : ℂ) (m : ℕ) :
    evaluation w (c • overshear s m) = DirectionalCompleteFlows.overshearField s m c w := by
  apply Prod.ext <;>
    simp [evaluation, overshear, linearForm, DirectionalCompleteFlows.overshearField,
      DirectionalCompleteFlows.linearForm, DirectionalCompleteFlows.direction,
      smul_eq_mul]
  all_goals ring

/-- The exact evaluated vector-field identity uses the same explicit fields
whose complete flows and parameter holomorphy were proved separately. -/
theorem exists_evaluated_decomposition (m : ℕ) (P Q : Poly)
    (hP : P.IsHomogeneous (m + 1)) (hQ : Q.IsHomogeneous (m + 1)) :
    ∃ c : Fin (m + 1) → ℂ, ∃ b : Fin (m + 3) → ℂ,
      ∀ w : ℂ × ℂ,
        (eval ![w.1, w.2] P, eval ![w.1, w.2] Q) =
          (∑ j, DirectionalCompleteFlows.overshearField (j.val : ℂ) m (c j) w) +
          ∑ j, DirectionalCompleteFlows.shearField (j.val : ℂ) (m + 1) (b j) w := by
  obtain ⟨c, b, hb⟩ := exists_decomposition m P Q hP hQ
  refine ⟨c, b, fun w => ?_⟩
  have heq := congrArg (evaluation w) hb
  simpa only [map_add, map_sum, evaluation_apply, evaluation_shear,
    evaluation_overshear] using heq

end AutomaticContinuity.HomogeneousFieldDecomposition
