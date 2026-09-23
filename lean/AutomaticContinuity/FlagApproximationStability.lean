import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# Uniform stability of the strict flag constraints on compact sets

A continuous section whose graph lies in the actual open total space has a
uniform positive tube over a compact set. Consequently a sufficiently close
approximation preserves all flag inequalities on that compact set. This is a
local stability statement: it does not assert preservation on the entire flags
and is not the remaining holomorphic approximation theorem.
-/

namespace AutomaticContinuity.FlagTotalSpace

open Set Metric

/-- Compactness gives one positive tolerance for all flag constraints over `K`.
Only continuity on `K` is needed. -/
theorem exists_uniform_tube {n : ℕ} {K : Set (FinitePoint n)} (hK : IsCompact K)
    {h : FinitePoint n → ℂ × ℂ} (hh : ContinuousOn h K)
    (hb : ∀ z ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ n →
      z ∈ finiteFlag n k → (k : ℝ) < euclideanPairNorm (h z)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, ∀ v : ℂ × ℂ,
      euclideanPairNorm (v - h z) ≤ δ → (z, v) ∈ totalSet n := by
  let graph : Set (FinitePoint n × (ℂ × ℂ)) := (fun z => (z, h z)) '' K
  have hg : IsCompact graph := hK.image_of_continuousOn (continuousOn_id.prodMk hh)
  have hsub : graph ⊆ totalSet n := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_totalSet_iff.mpr (hb z hz)
  obtain ⟨δ, hδ, htube⟩ := hg.exists_cthickening_subset_open (isOpen_totalSet n) hsub
  refine ⟨δ, hδ, ?_⟩
  intro z hz v hv
  apply htube
  apply mem_cthickening_of_dist_le (z, v) (z, h z) δ graph ⟨z, hz, rfl⟩
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
  exact (norm_le_euclideanPairNorm (v - h z)).trans hv

/-- A uniform approximation tolerance preserves every strict flag inequality
on the compact approximation set. -/
theorem exists_tolerance_preserving_bounds {n : ℕ} {K : Set (FinitePoint n)}
    (hK : IsCompact K) {h : FinitePoint n → ℂ × ℂ} (hh : ContinuousOn h K)
    (hb : ∀ z ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ n →
      z ∈ finiteFlag n k → (k : ℝ) < euclideanPairNorm (h z)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : FinitePoint n → ℂ × ℂ,
      (∀ z ∈ K, euclideanPairNorm (H z - h z) ≤ δ) →
        ∀ z ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ n →
          z ∈ finiteFlag n k → (k : ℝ) < euclideanPairNorm (H z) := by
  obtain ⟨δ, hδ, htube⟩ := exists_uniform_tube hK hh hb
  refine ⟨δ, hδ, ?_⟩
  intro H hH z hz
  exact mem_totalSet_iff.mp (htube z hz (H z) (hH z hz))

end AutomaticContinuity.FlagTotalSpace
