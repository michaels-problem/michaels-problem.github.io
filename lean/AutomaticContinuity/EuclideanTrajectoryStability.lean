import AutomaticContinuity.DiscreteTrajectoryStability
import AutomaticContinuity.EuclideanBallGeometry

set_option autoImplicit false

/-!
# Euclidean trajectory estimates for the actual two-coordinate fibre

The quantitative norm is `euclideanPairNorm`, not the product maximum norm.
The comparison estimate is local to each reference trajectory; no Lipschitz
constant across disjoint protected and moving regions is asserted.
-/

noncomputable section

namespace AutomaticContinuity.EuclideanTrajectoryStability

open DiscreteTrajectoryStability

theorem error_next_le (A : (ℂ × ℂ) → ℂ × ℂ)
    (V W : (ℂ × ℂ) → ℂ × ℂ) (x y : ℂ × ℂ)
    {h η δ L : ℝ} (hh : 0 ≤ h)
    (hEuler : euclideanPairNorm (A x - x - h • V x) ≤ h * η)
    (happrox : euclideanPairNorm (V x - W x) ≤ δ)
    (hcompare : euclideanPairNorm (W x - W y) ≤ L * euclideanPairNorm (x - y)) :
    euclideanPairNorm (A x - (y + h • W y)) ≤
      (1 + h * L) * euclideanPairNorm (x - y) + h * (δ + η) := by
  have hid : A x - (y + h • W y) =
      (A x - x - h • V x) + (x - y) + h • (V x - W x) + h • (W x - W y) := by
    simp only [smul_sub]
    abel
  rw [hid]
  calc
    euclideanPairNorm ((A x - x - h • V x) + (x - y) + h • (V x - W x) + h • (W x - W y))
        ≤ euclideanPairNorm (A x - x - h • V x) + euclideanPairNorm (x - y) +
          euclideanPairNorm (h • (V x - W x)) + euclideanPairNorm (h • (W x - W y)) := by
            have h1 := euclideanPairNorm_add_le (A x - x - h • V x) (x - y)
            have h2 := euclideanPairNorm_add_le ((A x - x - h • V x) + (x - y)) (h • (V x - W x))
            have h3 := euclideanPairNorm_add_le
              ((A x - x - h • V x) + (x - y) + h • (V x - W x)) (h • (W x - W y))
            linarith
    _ ≤ h * η + euclideanPairNorm (x - y) + h * δ + h * (L * euclideanPairNorm (x - y)) := by
      simp only [euclideanPairNorm_real_smul hh]
      gcongr
    _ = (1 + h * L) * euclideanPairNorm (x - y) + h * (δ + η) := by ring

theorem trajectory_bootstrap (A V W : ℕ → (ℂ × ℂ) → ℂ × ℂ) (x y : ℕ → ℂ × ℂ)
    {a δ η L h T ρ : ℝ} {N : ℕ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hinit : euclideanPairNorm (x 0 - y 0) ≤ a) (horizon : (N : ℝ) * h ≤ T)
    (hsmall : (a + T * (δ + η)) * Real.exp (T * L) < ρ)
    (hx : ∀ j < N, x (j + 1) = A j (x j))
    (hy : ∀ j < N, y (j + 1) = y j + h • W j (y j))
    (hEuler : ∀ j < N, ∀ z, euclideanPairNorm (z - y j) < ρ →
      euclideanPairNorm (A j z - z - h • V j z) ≤ h * η)
    (happrox : ∀ j < N, ∀ z, euclideanPairNorm (z - y j) < ρ →
      euclideanPairNorm (V j z - W j z) ≤ δ)
    (hcompare : ∀ j < N, ∀ z, euclideanPairNorm (z - y j) < ρ →
      euclideanPairNorm (W j z - W j (y j)) ≤ L * euclideanPairNorm (z - y j)) :
    ∀ j ≤ N,
      euclideanPairNorm (x j - y j) ≤ errorBound a (δ + η) L h j ∧
      euclideanPairNorm (x j - y j) < ρ := by
  apply recurrence_bootstrap ha (add_nonneg hδ hη) hL hh hinit horizon hsmall
  intro j hj hjtube
  rw [hx j hj, hy j hj]
  exact error_next_le (A j) (V j) (W j) (x j) (y j) hh
    (hEuler j hj (x j) hjtube) (happrox j hj (x j) hjtube)
    (hcompare j hj (x j) hjtube)

/-- The affine radial trajectory at mesh index `j`. -/
def radialPoint (c h : ℝ) (j : ℕ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (1 + (j : ℝ) * h * c) • w

/-- Its frozen-time comparison field. -/
def radialField (c h : ℝ) (j : ℕ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (c / (1 + (j : ℝ) * h * c)) • z

theorem radial_rate_bounds {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (j : ℕ) :
    0 ≤ c / (1 + (j : ℝ) * h * c) ∧ c / (1 + (j : ℝ) * h * c) ≤ c := by
  have hd : 1 ≤ 1 + (j : ℝ) * h * c := le_add_of_nonneg_right (by positivity)
  exact ⟨div_nonneg hc (by linarith), div_le_self hc hd⟩

/-- The radial target has an exact Euler step, so no time-discretization
remainder is needed for the target trajectory. -/
theorem radialPoint_succ {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (j : ℕ) (w : ℂ × ℂ) :
    radialPoint c h (j + 1) w =
      radialPoint c h j w + h • radialField c h j (radialPoint c h j w) := by
  have hd : (1 + (j : ℝ) * h * c) ≠ 0 := ne_of_gt (by positivity)
  simp only [radialPoint, radialField, smul_smul, ← add_smul, Nat.cast_add, Nat.cast_one]
  congr 1
  field_simp
  ring

/-- The comparison-field Lipschitz constant is `c`, independent of the
polynomial cutoff degree and the number of mesh steps. -/
theorem radialField_error_le {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h)
    (j : ℕ) (z w : ℂ × ℂ) :
    euclideanPairNorm (radialField c h j z - radialField c h j w) ≤
      c * euclideanPairNorm (z - w) := by
  obtain ⟨h0, hle⟩ := radial_rate_bounds hc hh j
  simp only [radialField, ← smul_sub, euclideanPairNorm_real_smul h0]
  exact mul_le_mul_of_nonneg_right hle (euclideanPairNorm_nonneg _)

@[simp] theorem radialPoint_zero (c h : ℝ) (w : ℂ × ℂ) : radialPoint c h 0 w = w := by
  simp [radialPoint]

theorem radialPoint_terminal {c h : ℝ} {N : ℕ} (hmesh : (N : ℝ) * h = 1) (w : ℂ × ℂ) :
    radialPoint c h N w = (1 + c) • w := by simp [radialPoint, hmesh]

end AutomaticContinuity.EuclideanTrajectoryStability
