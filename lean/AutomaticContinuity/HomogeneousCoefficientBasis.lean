import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

/-!
# Finite homogeneous-power coefficient basis

The coefficient arrays of the powers `(x + j*y)^m`, for `0 ≤ j ≤ m`,
form a basis: their coefficient matrix is a Vandermonde matrix with nonzero
binomial row factors. The theorem below is the exact finite-array statement;
it does not presuppose any homogeneous-polynomial infrastructure.
-/

noncomputable section

namespace AutomaticContinuity.HomogeneousCoefficientBasis

open scoped BigOperators

/-- Every degree-`m` two-variable coefficient array has a unique expansion
in the coefficient arrays of `(x + j*y)^m`, `j = 0,...,m`. -/
theorem existsUnique_coefficients (m : ℕ) (a : Fin (m + 1) → ℂ) :
    ∃! b : Fin (m + 1) → ℂ, ∀ k : Fin (m + 1),
      a k = (m.choose k.val : ℂ) *
        ∑ j : Fin (m + 1), b j * (j.val : ℂ) ^ k.val := by
  let V : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.vandermonde (fun j : Fin (m + 1) => (j.val : ℂ))
  have hdet : V.det ≠ 0 := by
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    apply Fin.ext
    change (i.val : ℂ) = (j.val : ℂ) at hij
    exact_mod_cast hij
  have hunit : IsUnit V :=
    (Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hchoose (k : Fin (m + 1)) : (m.choose k.val : ℂ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt_succ k.isLt)
  obtain ⟨b, hb⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hunit)
    (fun k : Fin (m + 1) => a k / (m.choose k.val : ℂ))
  have hbstmt (k : Fin (m + 1)) :
      a k = (m.choose k.val : ℂ) *
        ∑ j : Fin (m + 1), b j * (j.val : ℂ) ^ k.val := by
    have hk := congrFun hb k
    change (∑ j : Fin (m + 1), b j * (j.val : ℂ) ^ k.val) =
      a k / (m.choose k.val : ℂ) at hk
    rw [hk]
    exact (mul_div_cancel₀ (a k) (hchoose k)).symm
  refine ⟨b, hbstmt, ?_⟩
  intro c hc
  apply (Matrix.vecMul_injective_iff_isUnit.mpr hunit)
  funext k
  apply mul_left_cancel₀ (hchoose k)
  change (m.choose k.val : ℂ) *
      (∑ j : Fin (m + 1), c j * (j.val : ℂ) ^ k.val) =
    (m.choose k.val : ℂ) * (∑ j : Fin (m + 1), b j * (j.val : ℂ) ^ k.val)
  rw [← hc k, ← hbstmt k]


end AutomaticContinuity.HomogeneousCoefficientBasis
