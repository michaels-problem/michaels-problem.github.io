import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform limits under adaptive geometric error budgets

Errors are controlled on an increasing exhaustion, with positive budgets that
may depend on all previous choices and decrease by at least a factor of two.
The limit is uniform on each exhaustion set and retains the explicit tail
bound. No continuity of the maps or compactness of the exhaustion sets is needed.
-/

noncomputable section

namespace AutomaticContinuity.AdaptiveUniformLimit

open Filter
open scoped Topology

universe u v

theorem budget_add_le {b : ℕ → ℝ} (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (m n : ℕ) : b (n + m) ≤ b m * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        b (n + 1 + m) = b (n + m + 1) := by congr 1; omega
        _ ≤ b (n + m) / 2 := hb _
        _ ≤ (b m * (1 / 2 : ℝ) ^ n) / 2 := by linarith
        _ = b m * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

/-- Increasing exhaustive sets and geometrically shrinking adaptive budgets
produce one global limit, uniform on each set, with half-budget tail error. -/
theorem exists_limit {X : Type u} {Y : Type v}
    [NormedAddCommGroup Y] [CompleteSpace Y]
    (K : ℕ → Set X) (hK : Monotone K) (hcover : ∀ x, ∃ n, x ∈ K n)
    (F : ℕ → X → Y) (b : ℕ → ℝ) (_hbpos : ∀ n, 0 < b n)
    (hb : ∀ n, b (n + 1) ≤ b n / 2)
    (hstep : ∀ n, ∀ x ∈ K n, ‖F (n + 1) x - F n x‖ ≤ b n / 4) :
    ∃ G : X → Y,
      (∀ m, TendstoUniformlyOn F G atTop (K m)) ∧
      ∀ m, ∀ x ∈ K m, ‖G x - F m x‖ ≤ b m / 2 := by
  have htailStep (m : ℕ) (x : X) (hx : x ∈ K m) (n : ℕ) :
      dist (F (n + m) x) (F (n + 1 + m) x) ≤
        (b m / 4) * (1 / 2 : ℝ) ^ n := by
    have hx' : x ∈ K (n + m) := hK (by omega) hx
    have he := hstep (n + m) x hx'
    have hgeo := budget_add_le hb m n
    rw [dist_comm, dist_eq_norm]
    have hidx : n + 1 + m = n + m + 1 := by omega
    rw [hidx]
    exact he.trans (by nlinarith)
  have hex (x : X) : ∃ y : Y, Tendsto (fun n => F n x) atTop (𝓝 y) := by
    obtain ⟨m, hm⟩ := hcover x
    have hc : CauchySeq (fun n => F (n + m) x) :=
      cauchySeq_of_le_geometric (1 / 2 : ℝ) (b m / 4) (by norm_num)
        (htailStep m x hm)
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨y, (tendsto_add_atTop_iff_nat m).mp hy⟩
  choose G hG using hex
  have htail (m : ℕ) (x : X) (hx : x ∈ K m) :
      ‖G x - F m x‖ ≤ b m / 2 := by
    have hlim : Tendsto (fun n => F (n + m) x) atTop (𝓝 (G x)) :=
      (tendsto_add_atTop_iff_nat m).mpr (hG x)
    have he := dist_le_of_le_geometric_of_tendsto₀ (1 / 2 : ℝ) (b m / 4)
      (by norm_num) (htailStep m x hx) hlim
    simp only [zero_add, dist_comm (F m x), dist_eq_norm] at he
    convert he using 1
    ring
  refine ⟨G, ?_, htail⟩
  intro m
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hzero : Tendsto (fun n : ℕ => (b 0 / 2) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (b 0 / 2)
  filter_upwards [eventually_ge_atTop m, (tendsto_order.mp hzero).2 ε hε] with n hn he
  intro x hx
  rw [dist_eq_norm]
  have hgeo := budget_add_le hb 0 n
  simp only [add_zero] at hgeo
  exact (htail n x (hK hn hx)).trans_lt (by nlinarith)

end AutomaticContinuity.AdaptiveUniformLimit
