import AutomaticContinuity.FlagTotalSpace
import AutomaticContinuity.PairLinearSeparation
import AutomaticContinuity.StageStep

/-!
# Compact convex Euclidean balls in the target pair space

The existing product topology is retained. These lemmas compare its maximum
norm with the explicit Euclidean norm and prove the compactness and real
convexity needed for the forbidden compact graph.
-/

namespace AutomaticContinuity

open Set Metric

theorem norm_le_euclideanPairNorm (v : ℂ × ℂ) : ‖v‖ ≤ euclideanPairNorm v := by
  rw [Prod.norm_def]
  exact max_le (norm_fst_le_euclideanPairNorm v) (norm_snd_le_euclideanPairNorm v)

theorem euclideanPairNorm_le_two_mul_norm (v : ℂ × ℂ) :
    euclideanPairNorm v ≤ 2 * ‖v‖ := by
  have h₁ : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h₂ : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  exact (euclideanPairNorm_le_sum v).trans (by linarith)

@[simp] theorem euclideanPairNorm_zero : euclideanPairNorm (0 : ℂ × ℂ) = 0 := by
  simp [euclideanPairNorm]

@[simp] theorem euclideanPairNorm_eq_zero_iff (v : ℂ × ℂ) :
    euclideanPairNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    exact le_antisymm (h ▸ norm_le_euclideanPairNorm v) (norm_nonneg _)
  · rintro rfl
    exact euclideanPairNorm_zero

/-- The supporting functional gives the triangle inequality without imposing
a different norm instance on the pair type. -/
theorem euclideanPairNorm_add_le (v w : ℂ × ℂ) :
    euclideanPairNorm (v + w) ≤ euclideanPairNorm v + euclideanPairNorm w := by
  by_cases hpos : 0 < euclideanPairNorm (v + w)
  · obtain ⟨ℓ, hℓ, heq⟩ := exists_pair_norming_functional (v + w) hpos
    rw [← heq, map_add]
    exact (norm_add_le (ℓ v) (ℓ w)).trans (add_le_add (hℓ v) (hℓ w))
  · exact (le_of_not_gt hpos).trans
      (add_nonneg (euclideanPairNorm_nonneg v) (euclideanPairNorm_nonneg w))

namespace FlagTotalSpace

theorem closedEuclideanBall_subset_closedBall (r : ℝ) :
    closedEuclideanBall r ⊆ Metric.closedBall 0 r := by
  intro v hv
  exact Metric.mem_closedBall.mpr (by
    simpa only [dist_zero_right] using (norm_le_euclideanPairNorm v).trans hv)

/-- Euclidean closed balls are compact in the unchanged product topology. -/
theorem isCompact_closedEuclideanBall (r : ℝ) : IsCompact (closedEuclideanBall r) :=
  (isCompact_closedBall (0 : ℂ × ℂ) r).of_isClosed_subset
    (isClosed_closedEuclideanBall r) (closedEuclideanBall_subset_closedBall r)

theorem convex_closedEuclideanBall (r : ℝ) : Convex ℝ (closedEuclideanBall r) := by
  intro v hv w hw a b ha hb hab
  apply (euclideanPairNorm_add_le (a • v) (b • w)).trans
  rw [euclideanPairNorm_real_smul ha, euclideanPairNorm_real_smul hb]
  calc
    a * euclideanPairNorm v + b * euclideanPairNorm w ≤ a * r + b * r :=
      add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
    _ = r := by rw [← add_mul, hab, one_mul]

@[simp] theorem closedEuclideanBall_nonempty_iff (r : ℝ) :
    (closedEuclideanBall r).Nonempty ↔ 0 ≤ r := by
  constructor
  · rintro ⟨v, hv⟩
    exact (euclideanPairNorm_nonneg v).trans hv
  · intro hr
    exact ⟨0, by simpa only [closedEuclideanBall, mem_ofPred_eq, euclideanPairNorm_zero] using hr⟩

theorem closedEuclideanBall_eq_empty {r : ℝ} (hr : r < 0) :
    closedEuclideanBall r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact (not_le_of_gt hr) ((euclideanPairNorm_nonneg v).trans hv)

end FlagTotalSpace

end AutomaticContinuity
