import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Dyadic radii and geometric error budgets for radial push iteration -/

noncomputable section

namespace AutomaticContinuity.RadialIterationBudgets

def radius (a₀ : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ n * a₀

def entryRadius (a₀ : ℝ) (n : ℕ) : ℝ := radius a₀ n / 2

def budget (a₀ : ℝ) (n : ℕ) : ℝ := (a₀ / 4) * (1 / 2 : ℝ) ^ n

@[simp] theorem radius_zero (a₀ : ℝ) : radius a₀ 0 = a₀ := by simp [radius]

theorem radius_pos {a₀ : ℝ} (ha₀ : 0 < a₀) (n : ℕ) : 0 < radius a₀ n := by
  unfold radius
  positivity

theorem radius_succ (a₀ : ℝ) (n : ℕ) : radius a₀ (n + 1) = 2 * radius a₀ n := by
  simp only [radius, pow_succ]
  ring

theorem radius_monotone {a₀ : ℝ} (ha₀ : 0 ≤ a₀) : Monotone (radius a₀) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [radius_succ]
  have hn : 0 ≤ radius a₀ n := mul_nonneg (by positivity) ha₀
  linarith

theorem initial_le_radius {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) : a₀ ≤ radius a₀ n := by
  simpa only [radius_zero] using radius_monotone ha₀ (Nat.zero_le n)

theorem radius_mono {a₀ : ℝ} (ha₀ : 0 ≤ a₀) : Monotone (radius a₀) :=
  radius_monotone ha₀

theorem exists_radius_gt {a₀ : ℝ} (ha₀ : 0 < a₀) (R : ℝ) :
    ∃ n : ℕ, R < radius a₀ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / a₀) (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, (div_lt_iff₀ ha₀).mp hn⟩

theorem radius_exhaustive {a₀ : ℝ} (ha₀ : 0 < a₀) (R : ℝ) :
    ∃ n : ℕ, R ≤ radius a₀ n := by
  obtain ⟨n, hn⟩ := exists_radius_gt ha₀ R
  exact ⟨n, hn.le⟩

theorem entryRadius_pos {a₀ : ℝ} (ha₀ : 0 < a₀) (n : ℕ) :
    0 < entryRadius a₀ n := div_pos (radius_pos ha₀ n) (by norm_num)

theorem entryRadius_succ (a₀ : ℝ) (n : ℕ) :
    entryRadius a₀ (n + 1) = 2 * entryRadius a₀ n := by
  rw [entryRadius, radius_succ, entryRadius]
  ring

theorem entryRadius_le_radius {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) :
    entryRadius a₀ n ≤ radius a₀ n := by
  have hn : 0 ≤ radius a₀ n := mul_nonneg (by positivity) ha₀
  unfold entryRadius
  linarith

theorem entryRadius_monotone {a₀ : ℝ} (ha₀ : 0 ≤ a₀) : Monotone (entryRadius a₀) :=
  fun _ _ h => div_le_div_of_nonneg_right (radius_monotone ha₀ h) (by norm_num)

theorem entry_le_radius {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) :
    entryRadius a₀ n ≤ radius a₀ n := entryRadius_le_radius ha₀ n

theorem exists_entryRadius_gt {a₀ : ℝ} (ha₀ : 0 < a₀) (R : ℝ) :
    ∃ n : ℕ, R < entryRadius a₀ n := by
  obtain ⟨n, hn⟩ := exists_radius_gt ha₀ (2 * R)
  exact ⟨n, by unfold entryRadius; linarith⟩

@[simp] theorem budget_zero (a₀ : ℝ) : budget a₀ 0 = a₀ / 4 := by simp [budget]

theorem budget_pos {a₀ : ℝ} (ha₀ : 0 < a₀) (n : ℕ) : 0 < budget a₀ n := by
  unfold budget
  positivity

theorem budget_nonneg {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) : 0 ≤ budget a₀ n := by
  unfold budget
  positivity

theorem budget_half (a₀ : ℝ) (n : ℕ) : budget a₀ (n + 1) = budget a₀ n / 2 := by
  simp only [budget, pow_succ]
  ring

theorem budget_le_initial {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) : budget a₀ n ≤ a₀ / 4 := by
  apply mul_le_of_le_one_right (div_nonneg ha₀ (by norm_num))
  exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)

theorem entry_gap {a₀ : ℝ} (ha₀ : 0 ≤ a₀) (n : ℕ) :
    entryRadius a₀ n + budget a₀ n / 4 ≤ entryRadius a₀ (n + 1) := by
  rw [entryRadius_succ]
  have hr := initial_le_radius ha₀ n
  have hb := budget_le_initial ha₀ n
  unfold entryRadius
  linarith

/-- One stage leaves room for both the prescribed target radius and the
entire inverse error tail strictly inside the entry ball. -/
theorem exists_entry_margin {a₀ : ℝ} (ha₀ : 0 < a₀) (R : ℝ) :
    ∃ j : ℕ, R + budget a₀ j / 2 < entryRadius a₀ j := by
  obtain ⟨j, hj⟩ := exists_entryRadius_gt ha₀ (R + a₀ / 8)
  refine ⟨j, lt_of_le_of_lt ?_ hj⟩
  linarith [budget_le_initial ha₀.le j]

/-- A common closed intermediate radius can be selected below the entry
radius and every later protected radius. -/
theorem exists_closed_entry_margin {a₀ : ℝ} (ha₀ : 0 < a₀) (R : ℝ) :
    ∃ (j : ℕ) (S : ℝ), R + budget a₀ j / 2 ≤ S ∧ S < entryRadius a₀ j ∧
      ∀ i, j ≤ i → S ≤ radius a₀ i := by
  obtain ⟨j, hj⟩ := exists_entry_margin ha₀ R
  refine ⟨j, R + budget a₀ j / 2, le_rfl, hj, ?_⟩
  intro i hi
  exact hj.le.trans ((entryRadius_le_radius ha₀.le j).trans (radius_monotone ha₀.le hi))

end AutomaticContinuity.RadialIterationBudgets
