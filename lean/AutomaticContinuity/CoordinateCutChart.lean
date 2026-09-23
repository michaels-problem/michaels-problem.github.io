import AutomaticContinuity.FlagApproximationTransfer
import AutomaticContinuity.RectangleSeparatedSplitting

set_option autoImplicit false

/-! # An actual affine chart isolating a complex coordinate cut -/

noncomputable section

namespace AutomaticContinuity.CoordinateCutChart

open Set

abbrev Remaining {n : ℕ} (j : Fin n) := {i : Fin n // i ≠ j} → ℂ

def chart {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    FinitePoint n ≃ Remaining j × ℂ where
  toFun z := (fun i => z i, a * z j - (b : ℂ))
  invFun q i := if h : i = j then (q.2 + (b : ℂ)) / a else q.1 ⟨i, h⟩
  left_inv z := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [ha]
    · simp [hij]
  right_inv q := by
    apply Prod.ext
    · funext i
      simp [i.property]
    · simp only [dite_true]
      field_simp
      ring

@[simp] theorem chart_apply {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ)
    (z : FinitePoint n) : chart j a ha b z =
      (fun i : {i : Fin n // i ≠ j} => z i, a * z j - (b : ℂ)) := rfl

theorem differentiable_chart {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    Differentiable ℂ (chart j a ha b) := by
  change Differentiable ℂ (fun z : FinitePoint n => (fun i : {i : Fin n // i ≠ j} => z i,
    a * z j - (b : ℂ)))
  fun_prop

theorem differentiable_chart_symm {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    Differentiable ℂ (chart j a ha b).symm := by
  apply differentiable_pi.mpr
  intro i
  change Differentiable ℂ (fun q : Remaining j × ℂ =>
    if h : i = j then (q.2 + (b : ℂ)) / a else q.1 ⟨i, h⟩)
  split_ifs <;> fun_prop

def homeomorph {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ) :
    FinitePoint n ≃ₜ Remaining j × ℂ where
  toEquiv := chart j a ha b
  continuous_toFun := (differentiable_chart j a ha b).continuous
  continuous_invFun := (differentiable_chart_symm j a ha b).continuous

@[simp] theorem second_re {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ)
    (z : FinitePoint n) : ((chart j a ha b z).2).re = (a * z j).re - b := by
  simp

end AutomaticContinuity.CoordinateCutChart
