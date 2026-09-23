import AutomaticContinuity.FiniteCauchyFubini
import AutomaticContinuity.OneVariableCauchy

set_option autoImplicit false

/-!
# Radius-independent finite Taylor coefficient integrals

Fubini moves the coordinate whose radius changes to the innermost integral.
The existing one-variable Cauchy formula then applies to an entire coordinate
slice. No unproved multivariate analytic representation is used.
-/

namespace AutomaticContinuity.FiniteCauchy

theorem differentiable_cons_head {n : ℕ} (w : FinitePoint n) :
    Differentiable ℂ (fun z : ℂ => (Fin.cons z w : FinitePoint (n + 1))) := by
  apply differentiable_pi.mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]
    exact differentiable_fun_id
  · simpa only [Fin.cons_succ] using (differentiable_const (w j) :
      Differentiable ℂ (fun _ : ℂ => w j))

theorem differentiable_cons_tail {n : ℕ} (z : ℂ) :
    Differentiable ℂ (fun w : FinitePoint n => (Fin.cons z w : FinitePoint (n + 1))) := by
  apply differentiable_pi.mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [Fin.cons_zero] using (differentiable_const z :
      Differentiable ℂ (fun _ : FinitePoint n => z))
  · simpa only [Fin.cons_succ] using (differentiable_apply j :
      Differentiable ℂ (fun w : FinitePoint n => w j))

theorem continuous_cons_pair (n : ℕ) :
    Continuous (fun p : ℂ × FinitePoint n => (Fin.cons p.1 p.2 : FinitePoint (n + 1))) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [Fin.cons_zero] using (continuous_fst :
      Continuous (fun p : ℂ × FinitePoint n => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using ((continuous_apply j).comp continuous_snd :
      Continuous (fun p : ℂ × FinitePoint n => p.2 j))

/-- For an entire finite-variable function, contour coefficients do not depend
on the positive radius chosen in any coordinate. -/
theorem coefficient_eq_of_entire {n : ℕ} (R S : Fin n → ℝ)
    (hR : ∀ j, 0 < R j) (hS : ∀ j, 0 < S j)
    (h : FinitePoint n → ℂ) (hh : Differentiable ℂ h)
    (α : FiniteMultiIndex n) : coefficient R h α = coefficient S h α := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hcont : Continuous (fun p : ℂ × FinitePoint n => h (Fin.cons p.1 p.2)) :=
        hh.continuous.comp (continuous_cons_pair n)
      rw [coefficient_succ, coefficient_succ]
      calc
        circleCoeff (R 0) (α 0)
            (fun z => coefficient (Fin.tail R) (fun w => h (Fin.cons z w)) (Fin.tail α)) =
          circleCoeff (R 0) (α 0)
            (fun z => coefficient (Fin.tail S) (fun w => h (Fin.cons z w)) (Fin.tail α)) := by
              congr 1
              funext z
              exact ih (Fin.tail R) (Fin.tail S) (fun j => hR j.succ)
                (fun j => hS j.succ) _ (hh.comp (differentiable_cons_tail z)) (Fin.tail α)
        _ = coefficient (Fin.tail S)
            (fun w => circleCoeff (R 0) (α 0) (fun z => h (Fin.cons z w))) (Fin.tail α) :=
          coefficient_circleCoeff (hR 0) (α 0) (Fin.tail S) (fun j => hS j.succ)
            (fun z w => h (Fin.cons z w)) hcont (Fin.tail α)
        _ = coefficient (Fin.tail S)
            (fun w => circleCoeff (S 0) (α 0) (fun z => h (Fin.cons z w))) (Fin.tail α) := by
          congr 1
          funext w
          exact OneVariableCauchy.circleCoeff_radius_eq
            (hh.comp (differentiable_cons_head w)) (hR 0) (hS 0) (α 0)
        _ = circleCoeff (S 0) (α 0)
            (fun z => coefficient (Fin.tail S) (fun w => h (Fin.cons z w)) (Fin.tail α)) :=
          (coefficient_circleCoeff (hS 0) (α 0) (Fin.tail S) (fun j => hS j.succ)
            (fun z w => h (Fin.cons z w)) hcont (Fin.tail α)).symm

end AutomaticContinuity.FiniteCauchy
