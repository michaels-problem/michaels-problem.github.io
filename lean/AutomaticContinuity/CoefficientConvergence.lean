import AutomaticContinuity.CoefficientCompleteness
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

/-!
# Convergence from coefficient seminorm estimates

These results formalise the summation part of Section 3.3. They use the proved
completeness of the coefficient algebra. Obtaining the geometric coefficient
estimates from holomorphic approximants is still a separate analytic obligation.
-/

noncomputable section

namespace AutomaticContinuity
namespace CoefficientSeries

open Filter
open scoped Topology

/-- Absolute summability in every defining seminorm implies summability in the
full coefficient algebra; no single norm on that algebra is selected. -/
theorem summable_of_q_summable {ι : Type*} (f : ι → CoefficientSeries)
    (hf : ∀ r : ℕ, Summable (fun i => q (r + 1) (f i))) : Summable f := by
  rw [summable_iff_cauchySeq_finset]
  change Cauchy (uniformSpace := ⨅ n : ℕ,
    (definingSeminorm n).toSeminormedAddCommGroup.toUniformSpace)
    (Filter.map (fun s : Finset ι => ∑ i ∈ s, f i) atTop)
  rw [cauchy_iInf_uniformSpace]
  intro r
  let _ := (definingSeminorm r).toSeminormedAddCommGroup
  let _ : UniformSpace CoefficientSeries :=
    (definingSeminorm r).toSeminormedAddCommGroup.toUniformSpace
  exact cauchySeq_finset_of_norm_bounded (hf r) fun _ => le_rfl

/-- A geometric estimate may start at a different index in each seminorm. -/
theorem summable_of_q_eventually_le_geometric (f : ℕ → CoefficientSeries)
    (hf : ∀ r : ℕ, ∀ᶠ n in atTop, q (r + 1) (f n) ≤ (1 / 4 : ℝ) ^ n) :
    Summable f := by
  apply summable_of_q_summable
  intro r
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).of_norm_bounded_eventually_nat
  exact (hf r).mono fun n hn => by
    simpa only [Real.norm_of_nonneg (q_nonneg (r + 1) (f n))] using hn

/-- The diagonal estimate used in the manuscript is enough, because the
coefficient seminorms increase with the radius. The first two terms are unrestricted. -/
theorem summable_of_diagonal_geometric_bound (f : ℕ → CoefficientSeries)
    (hf : ∀ n : ℕ, 2 ≤ n → q n (f n) ≤ (1 / 4 : ℝ) ^ n) : Summable f := by
  apply summable_of_q_eventually_le_geometric
  intro r
  filter_upwards [eventually_ge_atTop (max 2 (r + 1))] with n hn
  exact (q_mono ((le_max_right _ _).trans hn) (f n)).trans
    (hf n ((le_max_left _ _).trans hn))

/-- Summable successive differences reconstruct the limit of the approximants. -/
theorem tendsto_of_summable_differences (f : ℕ → CoefficientSeries)
    (hf : Summable (fun n => f (n + 1) - f n)) :
    Tendsto f atTop (𝓝 ((∑' n : ℕ, (f (n + 1) - f n)) + f 0)) := by
  simpa only [Finset.sum_range_sub, sub_add_cancel] using
    hf.hasSum.tendsto_sum_nat.add_const (f 0)

/-- Coefficient estimates of the size proved from the Cauchy estimate in the
manuscript give an actual limit in the coefficient algebra. The function `f 0`
is unrestricted; the inequalities begin with the second positive-dimensional stage. -/
theorem exists_limit_of_successive_q_bound (f : ℕ → CoefficientSeries)
    (hf : ∀ n : ℕ, 1 ≤ n →
      q (n + 1) (f (n + 1) - f n) ≤ (1 / 4 : ℝ) ^ (n + 1)) :
    ∃ g : CoefficientSeries, Tendsto f atTop (𝓝 g) := by
  have hsum : Summable (fun n => f (n + 1) - f n) := by
    apply summable_of_q_eventually_le_geometric
    intro r
    filter_upwards [eventually_ge_atTop (max 1 r)] with n hn
    calc
      q (r + 1) (f (n + 1) - f n) ≤ q (n + 1) (f (n + 1) - f n) :=
        q_mono (Nat.succ_le_succ ((le_max_right _ _).trans hn)) _
      _ ≤ (1 / 4 : ℝ) ^ (n + 1) := hf n ((le_max_left _ _).trans hn)
      _ ≤ (1 / 4 : ℝ) ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg (by norm_num) n) (by norm_num)
  exact ⟨_, tendsto_of_summable_differences f hsum⟩

end CoefficientSeries
end AutomaticContinuity
