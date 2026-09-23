import AutomaticContinuity.SeveralVariableUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false

/-!
# Quantitative estimates for rescaled iterates near an attracting fixed point

For a linear equivalence shrinking norms by `1/4` and a map with a quadratic
remainder and contraction bound `1/3`, the rescaled iterates have geometrically
summable increments. The quadratic remainder and contraction are explicit
hypotheses; this module does not assume a linearization or a basin theorem.
-/

noncomputable section

namespace AutomaticContinuity.KoenigsEstimates

open Function Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def inversePower (A : E ≃L[ℂ] E) (n : ℕ) : E →L[ℂ] E :=
  (A.symm : E →L[ℂ] E) ^ n

def rescaledIterate (A : E ≃L[ℂ] E) (T : E → E) (n : ℕ) (x : E) : E :=
  inversePower A n (T^[n] x)

theorem norm_symm (A : E ≃L[ℂ] E) (hA : ∀ x, ‖A x‖ = (1 / 4 : ℝ) * ‖x‖)
    (x : E) : ‖A.symm x‖ = 4 * ‖x‖ := by
  have h := hA (A.symm x)
  rw [A.apply_symm_apply] at h
  linarith

theorem norm_inversePower (A : E ≃L[ℂ] E)
    (hA : ∀ x, ‖A x‖ = (1 / 4 : ℝ) * ‖x‖) (n : ℕ) (x : E) :
    ‖inversePower A n x‖ = 4 ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp [inversePower]
  | succ n ih =>
      change ‖((A.symm : E →L[ℂ] E) ^ (n + 1)) x‖ = _
      rw [pow_succ, mul_apply_eq_comp]
      change ‖inversePower A n (A.symm x)‖ = _
      rw [ih, norm_symm A hA, pow_succ]
      ring

theorem inversePower_succ_apply (A : E ≃L[ℂ] E) (n : ℕ) (x : E) :
    inversePower A (n + 1) (A x) = inversePower A n x := by
  simp only [inversePower, pow_succ, mul_apply_eq_comp,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem rescaledIterate_sub (A : E ≃L[ℂ] E) (T : E → E) (n : ℕ) (x : E) :
    rescaledIterate A T (n + 1) x - rescaledIterate A T n x =
      inversePower A (n + 1) (T (T^[n] x) - A (T^[n] x)) := by
  rw [map_sub, inversePower_succ_apply]
  simp only [rescaledIterate, Function.iterate_succ_apply']

omit [NormedSpace ℂ E] in
theorem norm_iterate_le {T : E → E} {r : ℝ} (hr : 0 ≤ r)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ (1 / 3 : ℝ) * ‖x‖)
    {x : E} (hx : x ∈ closedBall (0 : E) r) (n : ℕ) :
    ‖T^[n] x‖ ≤ (1 / 3 : ℝ) ^ n * ‖x‖ ∧ T^[n] x ∈ closedBall (0 : E) r := by
  induction n with
  | zero => simpa using And.intro (le_refl ‖x‖) hx
  | succ n ih =>
      have hn : ‖T (T^[n] x)‖ ≤ (1 / 3 : ℝ) ^ (n + 1) * ‖x‖ := by
        calc
          _ ≤ (1 / 3 : ℝ) * ‖T^[n] x‖ := hT _ ih.2
          _ ≤ (1 / 3 : ℝ) * ((1 / 3 : ℝ) ^ n * ‖x‖) := by gcongr; exact ih.1
          _ = _ := by rw [pow_succ]; ring
      rw [Function.iterate_succ_apply']
      refine ⟨hn, ?_⟩
      apply mem_closedBall.mpr
      rw [dist_zero_right]
      have hi : ‖T^[n] x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using ih.2
      exact (hT _ ih.2).trans (by linarith)

theorem norm_rescaledIterate_sub_le {A : E ≃L[ℂ] E} {T : E → E} {r C : ℝ}
    (hA : ∀ x, ‖A x‖ = (1 / 4 : ℝ) * ‖x‖) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ (1 / 3 : ℝ) * ‖x‖)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2)
    (n : ℕ) (x : E) (hx : x ∈ closedBall (0 : E) r) :
    ‖rescaledIterate A T (n + 1) x - rescaledIterate A T n x‖ ≤
      (4 * C * r ^ 2) * (4 / 9 : ℝ) ^ n := by
  obtain ⟨hn, hmem⟩ := norm_iterate_le hr hT hx n
  rw [rescaledIterate_sub, norm_inversePower A hA]
  have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  calc
    _ ≤ 4 ^ (n + 1) * (C * ‖T^[n] x‖ ^ 2) := by gcongr; exact hrem _ hmem
    _ ≤ 4 ^ (n + 1) * (C * (((1 / 3 : ℝ) ^ n * r) ^ 2)) := by
      gcongr
      exact hn.trans (mul_le_mul_of_nonneg_left hxnorm (by positivity))
    _ = (4 * C * r ^ 2) * (4 / 9 : ℝ) ^ n := by
      rw [mul_pow, pow_succ]
      have hpow : ((1 / 3 : ℝ) ^ n) ^ 2 = ((1 / 3 : ℝ) ^ 2) ^ n :=
        (pow_mul _ n 2).symm.trans (by rw [Nat.mul_comm, pow_mul])
      rw [hpow]
      have hcombine : (4 : ℝ) ^ n * ((1 / 3 : ℝ) ^ 2) ^ n = (4 / 9 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      calc
        _ = (4 * C * r ^ 2) * ((4 : ℝ) ^ n * ((1 / 3 : ℝ) ^ 2) ^ n) := by ring
        _ = _ := by rw [hcombine]

theorem contraction_of_quadratic_remainder {A : E ≃L[ℂ] E} {T : E → E} {r C : ℝ}
    (hA : ∀ x, ‖A x‖ = (1 / 4 : ℝ) * ‖x‖) (hC : 0 ≤ C)
    (hsmall : C * r ≤ 1 / 12)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ (1 / 3 : ℝ) * ‖x‖ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hCr : C * ‖x‖ ≤ 1 / 12 := (mul_le_mul_of_nonneg_left hxnorm hC).trans hsmall
  have hn := norm_add_le (T x - A x) (A x)
  rw [sub_add_cancel, hA] at hn
  have herr := hrem x hx
  nlinarith [mul_le_mul_of_nonneg_right hCr (norm_nonneg x)]

theorem inversePower_comp_power (A : E ≃L[ℂ] E) (n : ℕ) :
    (inversePower A n).comp ((A : E →L[ℂ] E) ^ n) = ContinuousLinearMap.id ℂ E := by
  have hinv : (A.symm : E →L[ℂ] E) * (A : E →L[ℂ] E) = 1 := by
    ext x
    simp [mul_apply_eq_comp]
  have hcomm : Commute (A.symm : E →L[ℂ] E) (A : E →L[ℂ] E) := by
    show (A.symm : E →L[ℂ] E) * (A : E →L[ℂ] E) =
      (A : E →L[ℂ] E) * (A.symm : E →L[ℂ] E)
    ext x
    simp [mul_apply_eq_comp]
  change (A.symm : E →L[ℂ] E) ^ n * (A : E →L[ℂ] E) ^ n = _
  rw [← hcomm.mul_pow, hinv, one_pow]
  rfl

theorem differentiable_rescaledIterate (A : E ≃L[ℂ] E) {T : E → E}
    (hT : Differentiable ℂ T) (n : ℕ) : Differentiable ℂ (rescaledIterate A T n) :=
  (inversePower A n).differentiable.comp (hT.iterate n)

@[simp] theorem rescaledIterate_zero (A : E ≃L[ℂ] E) {T : E → E}
    (hT0 : T 0 = 0) (n : ℕ) : rescaledIterate A T n 0 = 0 := by
  have hiter : T^[n] 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hT0]
  simp only [rescaledIterate, hiter, map_zero]

theorem hasFDerivAt_rescaledIterate_zero (A : E ≃L[ℂ] E) {T : E → E}
    (hT0 : T 0 = 0) (hTd : HasFDerivAt T (A : E →L[ℂ] E) 0) (n : ℕ) :
    HasFDerivAt (rescaledIterate A T n) (ContinuousLinearMap.id ℂ E) 0 := by
  have h := (inversePower A n).hasFDerivAt.comp 0 (hTd.iterate hT0 n)
  rw [inversePower_comp_power] at h
  exact h

theorem rescaledIterate_comp (A : E ≃L[ℂ] E) (T : E → E) (n : ℕ) (x : E) :
    rescaledIterate A T n (T x) = A (rescaledIterate A T (n + 1) x) := by
  simp only [rescaledIterate, inversePower, pow_succ', mul_apply_eq_comp,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    Function.iterate_succ_apply]

end AutomaticContinuity.KoenigsEstimates
