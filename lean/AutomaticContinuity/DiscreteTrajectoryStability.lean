import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
# Finite trajectory stability with a first-exit bootstrap

The local recurrence need only hold while the error lies in the prescribed
tube. The exponential error bound proves that every intermediate point stays
there. Its Lipschitz constant belongs to the simple comparison field, not to
the approximating high-degree polynomial field.
-/

noncomputable section

namespace AutomaticContinuity.DiscreteTrajectoryStability

/-- A convenient exponential majorant for a constant-step error recurrence. -/
def errorBound (a d L h : ℝ) (j : ℕ) : ℝ :=
  (a + (j : ℝ) * h * d) * Real.exp ((j : ℝ) * h * L)

@[simp] theorem errorBound_zero (a d L h : ℝ) : errorBound a d L h 0 = a := by
  simp [errorBound]

theorem errorBound_nonneg {a d L h : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hh : 0 ≤ h) (j : ℕ) : 0 ≤ errorBound a d L h j := by
  unfold errorBound
  positivity

theorem errorBound_step {a d L h : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hL : 0 ≤ L) (hh : 0 ≤ h) (j : ℕ) :
    (1 + h * L) * errorBound a d L h j + h * d ≤ errorBound a d L h (j + 1) := by
  have he : 1 + h * L ≤ Real.exp (h * L) := by
    simpa only [add_comm] using Real.add_one_le_exp (h * L)
  have hj : 0 ≤ (j : ℝ) * h * L := by positivity
  have hj' : 0 ≤ ((j : ℝ) + 1) * h * L := by positivity
  have hbig : 1 ≤ Real.exp (((j : ℝ) + 1) * h * L) := Real.one_le_exp hj'
  calc
    (1 + h * L) * errorBound a d L h j + h * d
        ≤ Real.exp (h * L) * errorBound a d L h j +
          h * d * Real.exp (((j : ℝ) + 1) * h * L) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right he (errorBound_nonneg ha hd hh j))
              (le_mul_of_one_le_right (mul_nonneg hh hd) hbig)
    _ = errorBound a d L h (j + 1) := by
      simp only [errorBound, Nat.cast_add, Nat.cast_one]
      rw [show ((j : ℝ) + 1) * h * L = h * L + (j : ℝ) * h * L by ring,
        Real.exp_add]
      ring

/-- The majorant is controlled by elapsed time, independently of mesh size. -/
theorem errorBound_le_of_time_le {a d L h T : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (j : ℕ) (hj : (j : ℝ) * h ≤ T) :
    errorBound a d L h j ≤ (a + T * d) * Real.exp (T * L) := by
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg j) hh).trans hj
  unfold errorBound
  gcongr

/-- A conditional local error recurrence suffices: the error never leaves the
open tube if the a priori bound at total time `T` lies strictly inside it. -/
theorem recurrence_bootstrap {e : ℕ → ℝ} {a d L h T ρ : ℝ} {N : ℕ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hinit : e 0 ≤ a) (horizon : (N : ℝ) * h ≤ T)
    (hsmall : (a + T * d) * Real.exp (T * L) < ρ)
    (hstep : ∀ j < N, e j < ρ → e (j + 1) ≤ (1 + h * L) * e j + h * d) :
    ∀ j ≤ N, e j ≤ errorBound a d L h j ∧ e j < ρ := by
  have ht (j : ℕ) (hj : j ≤ N) : (j : ℝ) * h ≤ T :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh).trans horizon
  intro j hj
  induction j with
  | zero =>
      constructor
      · simpa only [errorBound_zero] using hinit
      · have hab : a ≤ (a + T * d) * Real.exp (T * L) := by
          simpa only [errorBound_zero] using
            errorBound_le_of_time_le ha hd hL hh 0 (ht 0 (Nat.zero_le N))
        exact hinit.trans_lt (hab.trans_lt hsmall)
  | succ j ih =>
      obtain ⟨hle, hlt⟩ := ih (Nat.le_of_succ_le hj)
      have hnext : e (j + 1) ≤ errorBound a d L h (j + 1) := calc
        e (j + 1) ≤ (1 + h * L) * e j + h * d := hstep j (by omega) hlt
        _ ≤ (1 + h * L) * errorBound a d L h j + h * d := by
          gcongr
        _ ≤ errorBound a d L h (j + 1) := errorBound_step ha hd hL hh j
      exact ⟨hnext, hnext.trans_lt
        ((errorBound_le_of_time_le ha hd hL hh (j + 1) (ht (j + 1) hj)).trans_lt hsmall)⟩

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One actual numerical/map step compared to an exact Euler trajectory.
Only the comparison field needs a Lipschitz estimate. -/
theorem norm_error_next_le (A : E → E) (V W : E → E) (x y : E)
    {h η δ L : ℝ} (hh : 0 ≤ h)
    (hEuler : ‖A x - x - h • V x‖ ≤ h * η)
    (happrox : ‖V x - W x‖ ≤ δ)
    (hcompare : ‖W x - W y‖ ≤ L * ‖x - y‖) :
    ‖A x - (y + h • W y)‖ ≤ (1 + h * L) * ‖x - y‖ + h * (δ + η) := by
  have hid : A x - (y + h • W y) =
      (A x - x - h • V x) + (x - y) + h • (V x - W x) + h • (W x - W y) := by
    simp only [smul_sub]
    abel
  rw [hid]
  calc
    ‖(A x - x - h • V x) + (x - y) + h • (V x - W x) + h • (W x - W y)‖
        ≤ ‖A x - x - h • V x‖ + ‖x - y‖ + ‖h • (V x - W x)‖ +
          ‖h • (W x - W y)‖ := by
            have h1 := norm_add_le (A x - x - h • V x) (x - y)
            have h2 := norm_add_le ((A x - x - h • V x) + (x - y)) (h • (V x - W x))
            have h3 := norm_add_le
              ((A x - x - h • V x) + (x - y) + h • (V x - W x)) (h • (W x - W y))
            linarith
    _ ≤ h * η + ‖x - y‖ + h * δ + h * (L * ‖x - y‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
      gcongr
    _ = (1 + h * L) * ‖x - y‖ + h * (δ + η) := by ring

/-- Uniform control of every intermediate map iterate from estimates valid
only inside a tube about the specified exact Euler trajectory. -/
theorem trajectory_bootstrap (A V W : ℕ → E → E) (x y : ℕ → E)
    {a δ η L h T ρ : ℝ} {N : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hinit : ‖x 0 - y 0‖ ≤ a) (horizon : (N : ℝ) * h ≤ T)
    (hsmall : (a + T * (δ + η)) * Real.exp (T * L) < ρ)
    (hx : ∀ j < N, x (j + 1) = A j (x j))
    (hy : ∀ j < N, y (j + 1) = y j + h • W j (y j))
    (hEuler : ∀ j < N, ∀ z, ‖z - y j‖ < ρ →
      ‖A j z - z - h • V j z‖ ≤ h * η)
    (happrox : ∀ j < N, ∀ z, ‖z - y j‖ < ρ → ‖V j z - W j z‖ ≤ δ)
    (hcompare : ∀ j < N, ∀ z, ‖z - y j‖ < ρ →
      ‖W j z - W j (y j)‖ ≤ L * ‖z - y j‖) :
    ∀ j ≤ N,
      ‖x j - y j‖ ≤ errorBound a (δ + η) L h j ∧ ‖x j - y j‖ < ρ := by
  apply recurrence_bootstrap ha (add_nonneg hδ hη) hL hh hinit horizon hsmall
  intro j hj hjtube
  rw [hx j hj, hy j hj]
  exact norm_error_next_le (A j) (V j) (W j) (x j) (y j) hh
    (hEuler j hj (x j) hjtube) (happrox j hj (x j) hjtube)
    (hcompare j hj (x j) hjtube)

end NormedSpace

end AutomaticContinuity.DiscreteTrajectoryStability
