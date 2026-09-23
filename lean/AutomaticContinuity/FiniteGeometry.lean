import AutomaticContinuity.FiniteStages
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Elementary geometry of the finite approximation sets

The finite flags are genuine closed complex affine subspaces. Positive finite
flags are proper, and successive flags are strictly nested while there remain
coordinates to fix. The approximation polydiscs are compact and real convex.
These elementary properties supply part of the setup for the unproved holomorphic
approximation step; no Oka or polynomial-convexity theorem is asserted here.
-/

namespace AutomaticContinuity

/-- The flag viewed as a complex affine subspace, with the exact same carrier as
the explicit coordinate definition. -/
def finiteAffineFlag (n k : ℕ) : AffineSubspace ℂ (FinitePoint n) where
  carrier := finiteFlag n k
  smul_vsub_vadd_mem' c x y z hx hy hz := by
    intro j hj
    change c * (_ - _) + _ = _
    rw [hx j hj, hy j hj, hz j hj]
    simp

@[simp] theorem coe_finiteAffineFlag (n k : ℕ) :
    (finiteAffineFlag n k : Set (FinitePoint n)) = finiteFlag n k := rfl

theorem isClosed_finiteFlag (n k : ℕ) : IsClosed (finiteFlag n k) := by
  have heq : finiteFlag n k =
      ⋂ (j : Fin n) (_hj : j.val < k), {z | z j = prescribedCoordinate j.val} := by
    ext z
    simp [finiteFlag]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_iInter fun _hj =>
    isClosed_eq (continuous_apply j) continuous_const

theorem finiteFlag_succ_ssubset {n k : ℕ} (hk : k < n) :
    finiteFlag n (k + 1) ⊂ finiteFlag n k := by
  apply ssubset_iff_subset_not_subset.mpr
  refine ⟨finiteFlag_antitone n (Nat.le_succ k), ?_⟩
  intro hreverse
  have hm : restrictSequence n (truncatedPrescribed k) ∈ finiteFlag n (k + 1) :=
    hreverse (restrictSequence_mem_finiteFlag (truncatedPrescribed_mem k))
  have heq := hm ⟨k, hk⟩ (Nat.lt_succ_self k)
  change (if k < k then prescribedCoordinate k else 0) = prescribedCoordinate k at heq
  simp only [lt_self_iff_false, ↓reduceIte] at heq
  have hnorm := congrArg norm heq
  rw [norm_zero, norm_prescribedCoordinate] at hnorm
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem finiteFlag_proper {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    finiteFlag n k ≠ Set.univ := by
  intro heq
  have hn : 0 < n := hk.trans_le hkn
  have hstrict := finiteFlag_succ_ssubset (n := n) (k := 0) hn
  have hsub : finiteFlag n k ⊆ finiteFlag n 1 :=
    finiteFlag_antitone n (Nat.succ_le_of_lt hk)
  rw [heq] at hsub
  have hfull : finiteFlag n 1 = Set.univ := Set.eq_univ_iff_forall.mpr (fun z => hsub trivial)
  simp [hfull] at hstrict

/-- On `Fin n → ℂ`, Mathlib's default supremum norm gives exactly the coordinate
polydisc. This concerns the source norm, not the target Euclidean pair norm. -/
theorem polydisc_eq_closedBall (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    polydisc n r = Metric.closedBall 0 r := by
  ext z
  simp only [polydisc, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg hr).symm

theorem isCompact_polydisc (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (polydisc n r) := by
  rw [polydisc_eq_closedBall n hr]
  exact isCompact_closedBall 0 r

theorem convex_polydisc (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Convex ℝ (polydisc n r) := by
  rw [polydisc_eq_closedBall n hr]
  exact convex_closedBall 0 r

end AutomaticContinuity
