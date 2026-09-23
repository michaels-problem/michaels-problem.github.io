import AutomaticContinuity.OneVariableCauchy
import AutomaticContinuity.FiniteEmbeddingSupport

set_option autoImplicit false

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

@[simp] theorem circleCoeff_const {R : ℝ} (hR : 0 < R) (m : ℕ) (c : ℂ) :
    circleCoeff R m (fun _ => c) = if m = 0 then c else 0 := by
  rw [← OneVariableCauchy.coeff_eq_circleCoeff (differentiable_const c) hR]
  exact OneVariableCauchy.coeff_const c m

theorem prefixProjection_cons (n : ℕ) (z : ℂ) (w : FinitePoint (n + 1)) :
    prefixProjection (n + 1) (Fin.cons z w) = Fin.cons z (prefixProjection n w) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · rfl
  · rfl

/-- Adding an unused final variable adds only its zero exponent to the actual
iterated contour coefficients. No holomorphicity assumption is needed here. -/
theorem coefficient_prefixProjection {n : ℕ} {R : ℝ} (hR : 0 < R)
    (h : FinitePoint n → ℂ) (α : FiniteMultiIndex (n + 1)) :
    coefficient (fun _ => R) (fun z => h (prefixProjection n z)) α =
      liftFiniteCoefficients (coefficient (fun _ => R) h) α := by
  induction n with
  | zero =>
      have heq (z : ℂ) : prefixProjection 0 (Fin.cons z Fin.elim0) = Fin.elim0 := by
        funext j
        exact Fin.elim0 j
      simp only [coefficient_succ, coefficient_zero, heq]
      rw [circleCoeff_const hR]
      rfl
  | succ n ih =>
      rw [coefficient_succ]
      simp_rw [prefixProjection_cons]
      have heq (z : ℂ) :
          coefficient (Fin.tail (fun _ : Fin (n + 2) => R))
            (fun w => h (Fin.cons z (prefixProjection n w))) (Fin.tail α) =
          liftFiniteCoefficients (coefficient (fun _ => R) (fun w => h (Fin.cons z w)))
            (Fin.tail α) := ih (fun w => h (Fin.cons z w)) (Fin.tail α)
      simp_rw [heq]
      have hlast : Fin.tail α (Fin.last n) = α (Fin.last (n + 1)) := rfl
      by_cases hα : α (Fin.last (n + 1)) = 0
      · simp only [liftFiniteCoefficients, hlast, hα, ↓reduceIte, coefficient_succ]
        rfl
      · simp only [liftFiniteCoefficients, hlast, hα, ↓reduceIte]
        simp [circleCoeff_const hR]

end AutomaticContinuity.FiniteCauchy
