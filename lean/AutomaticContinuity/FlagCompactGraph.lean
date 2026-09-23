import AutomaticContinuity.EuclideanBallGeometry

/-!
# The compact forbidden graph over a finite polydisc

This is the restriction of the actual deleted set to the compact source
polydisc. Its target fibres remain the Euclidean balls from the flag problem.
-/

namespace AutomaticContinuity.FlagTotalSpace

open Set

/-- Restrict the actual finite deleted union to a compact source polydisc. -/
def compactForbiddenGraph (n : ℕ) (R : ℝ) : Set (FinitePoint n × (ℂ × ℂ)) :=
  forbiddenSet n ∩ (polydisc n R ×ˢ Set.univ)

theorem mem_compactForbiddenGraph_iff {n : ℕ} {R : ℝ}
    {p : FinitePoint n × (ℂ × ℂ)} :
    p ∈ compactForbiddenGraph n R ↔ p.1 ∈ polydisc n R ∧
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ p.1 ∈ finiteFlag n k ∧
        euclideanPairNorm p.2 ≤ (k : ℝ) := by
  constructor
  · intro hp
    exact ⟨hp.2.1, mem_forbiddenSet_iff.mp hp.1⟩
  · rintro ⟨hz, hp⟩
    exact ⟨mem_forbiddenSet_iff.mpr hp, hz, trivial⟩

theorem compactForbiddenGraph_eq_union (n : ℕ) (R : ℝ) :
    compactForbiddenGraph n R =
      ⋃ k ∈ Finset.Icc 1 n,
        (finiteFlag n k ∩ polydisc n R) ×ˢ closedEuclideanBall (k : ℝ) := by
  ext p
  rw [mem_compactForbiddenGraph_iff]
  simp only [mem_iUnion, Finset.mem_Icc, mem_prod, mem_inter_iff,
    closedEuclideanBall, mem_ofPred_eq]
  aesop

theorem compactForbiddenGraph_subset_product (n : ℕ) (R : ℝ) :
    compactForbiddenGraph n R ⊆ polydisc n R ×ˢ closedEuclideanBall (n : ℝ) := by
  intro p hp
  exact ⟨hp.2.1, (forbiddenSet_subset_ball n hp.1).2⟩

theorem isClosed_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsClosed (compactForbiddenGraph n R) :=
  (isClosed_forbiddenSet n).inter ((isCompact_polydisc n hR).isClosed.prod isClosed_univ)

theorem isCompact_flagBallPiece (n k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact ((finiteFlag n k ∩ polydisc n R) ×ˢ closedEuclideanBall (k : ℝ)) := by
  have hbase : IsCompact (finiteFlag n k ∩ polydisc n R) :=
    (isCompact_polydisc n hR).inter_left (isClosed_finiteFlag n k)
  exact hbase.prod (isCompact_closedEuclideanBall k)

/-- The entire restricted deleted set is compact, including the empty case n=0. -/
theorem isCompact_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (compactForbiddenGraph n R) :=
  ((isCompact_polydisc n hR).prod (isCompact_closedEuclideanBall n)).of_isClosed_subset
    (isClosed_compactForbiddenGraph n hR) (compactForbiddenGraph_subset_product n R)

@[simp] theorem compactForbiddenGraph_zero (R : ℝ) : compactForbiddenGraph 0 R = ∅ := by
  simp [compactForbiddenGraph]

def compactForbiddenFiber (n : ℕ) (R : ℝ) (z : FinitePoint n) : Set (ℂ × ℂ) :=
  {v | (z, v) ∈ compactForbiddenGraph n R}

theorem compactForbiddenFiber_subset_ball (n : ℕ) (R : ℝ) (z : FinitePoint n) :
    compactForbiddenFiber n R z ⊆ closedEuclideanBall (n : ℝ) := by
  intro v hv
  exact (compactForbiddenGraph_subset_product n R hv).2

theorem isCompact_compactForbiddenFiber (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (z : FinitePoint n) : IsCompact (compactForbiddenFiber n R z) := by
  apply (isCompact_closedEuclideanBall n).of_isClosed_subset
  · exact (isClosed_compactForbiddenGraph n hR).preimage
      (continuous_const.prodMk continuous_id)
  · exact compactForbiddenFiber_subset_ball n R z

theorem compactForbiddenFiber_eq_empty_of_outside {n : ℕ} {R : ℝ}
    {z : FinitePoint n} (hz : z ∉ polydisc n R) :
    compactForbiddenFiber n R z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hz ((mem_compactForbiddenGraph_iff.mp hv).1)

theorem compactForbiddenFiber_eq_ball_of_stratum {n k : ℕ} {R : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) {z : FinitePoint n}
    (hz : z ∈ stratum n k) (hzR : z ∈ polydisc n R) :
    compactForbiddenFiber n R z = closedEuclideanBall (k : ℝ) := by
  ext v
  change (z, v) ∈ compactForbiddenGraph n R ↔ _
  rw [mem_compactForbiddenGraph_iff]
  constructor
  · rintro ⟨_, j, hj, hjn, hzj, hv⟩
    by_cases hjk : j ≤ k
    · exact hv.trans (Nat.cast_le.mpr hjk)
    · exact False.elim (hz.2 (by omega) (finiteFlag_antitone n (by omega : k + 1 ≤ j) hzj))
  · intro hv
    exact ⟨hzR, k, hk, hkn, hz.1, hv⟩

theorem isCompact_baseProjection (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (Prod.fst '' compactForbiddenGraph n R) :=
  (isCompact_compactForbiddenGraph n hR).image continuous_fst

theorem isCompact_targetProjection (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (Prod.snd '' compactForbiddenGraph n R) :=
  (isCompact_compactForbiddenGraph n hR).image continuous_snd

theorem baseProjection_eq {n : ℕ} (hn : 1 ≤ n) (R : ℝ) :
    Prod.fst '' compactForbiddenGraph n R = finiteFlag n 1 ∩ polydisc n R := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hzR, k, hk, _hkn, hzk, _hv⟩ := mem_compactForbiddenGraph_iff.mp hp
    exact ⟨finiteFlag_antitone n hk hzk, hzR⟩
  · rintro ⟨hz, hzR⟩
    refine ⟨(z, 0), mem_compactForbiddenGraph_iff.mpr ?_, rfl⟩
    exact ⟨hzR, 1, le_rfl, hn, hz, by simp⟩

end AutomaticContinuity.FlagTotalSpace
