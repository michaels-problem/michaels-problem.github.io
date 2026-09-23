import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Positivity

/-!
# Nonempty inverse limits for dense contractions

This is the metric lemma needed for the Banach solution fibres in an Arens
finite-Bézout argument. The spaces may be noncompact and the bonding maps need
only have dense range; no surjectivity is assumed.
-/

set_option autoImplicit false

open Filter
open scoped Topology

noncomputable section

namespace AutomaticContinuity.DenseInverseLimit

universe u

variable {E : ℕ → Type u} (f : (n : ℕ) → E (n+1) → E n)

/-- Compose the bonding maps from level `n` down to level `m`. -/
def down {m n : ℕ} (h : m ≤ n) : E n → E m :=
  Nat.leRecOn h (fun {k} g => g ∘ f k) id

@[simp] theorem down_self (n : ℕ) : down f (Nat.le_refl n) = id := by
  exact Nat.leRecOn_self _

theorem down_succ {m n : ℕ} (h : m ≤ n) (h' : m ≤ n+1) :
    down f h' = down f h ∘ f n := by
  exact Nat.leRecOn_succ h _

theorem down_succ_left {m n : ℕ} (h : m+1 ≤ n) (h' : m ≤ n) :
    f m ∘ down f h = down f h' := by
  induction h with
  | refl =>
      rw [down_self, down_succ f (Nat.le_refl m), down_self]
      rfl
  | @step n h ih =>
      rw [down_succ f h, down_succ f (Nat.le_trans (Nat.le_succ m) h)]
      exact congrArg (fun g => g ∘ f n) (ih _)

variable [∀ n, MetricSpace (E n)]

theorem down_lipschitz (hf : ∀ n, LipschitzWith 1 (f n)) {m n : ℕ} (h : m ≤ n) :
    LipschitzWith 1 (down f h) := by
  induction h with
  | refl => simpa using (LipschitzWith.id : LipschitzWith 1 (id : E m → E m))
  | @step n h ih =>
      rw [down_succ f h]
      simpa using ih.comp (hf n)

/-- A countable inverse system of nonempty complete metric spaces with dense,
one-Lipschitz bonding maps has a compatible point. -/
theorem exists_compatible [∀ n, CompleteSpace (E n)] [∀ n, Nonempty (E n)]
    (hf : ∀ n, LipschitzWith 1 (f n)) (hd : ∀ n, DenseRange (f n)) :
    ∃ x : (n : ℕ) → E n, ∀ n, f n (x (n+1)) = x n := by
  classical
  have hlift (n : ℕ) (a : E n) : ∃ b : E (n+1),
      dist a (f n b) < (1/2 : ℝ)^n := by
    simpa [dist_comm] using (hd n).exists_dist_lt a (by positivity : 0 < (1/2 : ℝ)^n)
  choose next hnext using hlift
  let y : (n : ℕ) → E n := Nat.rec (Classical.choice inferInstance) (fun n a => next n a)
  have hy (n : ℕ) : dist (y n) (f n (y (n+1))) ≤ (1/2 : ℝ)^n := (hnext n (y n)).le
  let row (r n : ℕ) : E r := if h : r ≤ n then down f h (y n) else y r
  have hrow {r n : ℕ} (h : r ≤ n) : row r n = down f h (y n) := by
    simp only [row, dite_eq_left h]
  have hstep (r n : ℕ) : dist (row r n) (row r (n+1)) ≤ (1/2 : ℝ)^n := by
    by_cases h : r ≤ n
    · rw [hrow h, hrow (Nat.le_trans h (Nat.le_succ n)), down_succ f h]
      exact ((down_lipschitz f hf h).dist_le_mul _ _).trans
        (by simpa using hy n)
    · have hn : n+1 ≤ r := Nat.lt_of_not_ge h
      have heq : row r n = row r (n+1) := by
        by_cases h' : r ≤ n+1
        · have hr : r = n+1 := Nat.le_antisymm h' hn
          subst r
          simp [row, h]
        · simp only [row, dite_eq_right h, dite_eq_right h']
      rw [heq, dist_self]
      positivity
  have hlim (r : ℕ) : ∃ a : E r, Tendsto (row r) atTop (𝓝 a) := by
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_geometric (1/2 : ℝ) 1 (by norm_num)
    simpa using hstep r
  choose x hx using hlim
  refine ⟨x, ?_⟩
  intro r
  have heq : (fun n => f r (row (r+1) n)) =ᶠ[atTop] row r := by
    filter_upwards [eventually_ge_atTop (r+1)] with n hn
    rw [hrow hn, hrow ((Nat.le_succ r).trans hn)]
    exact congrFun (down_succ_left f hn ((Nat.le_succ r).trans hn)) (y n)
  exact tendsto_nhds_unique (((hf r).continuous.tendsto _).comp (hx (r+1)))
    ((hx r).congr' heq.symm)

end AutomaticContinuity.DenseInverseLimit
