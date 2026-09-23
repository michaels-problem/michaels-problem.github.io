import AutomaticContinuity.BallComplementSprays
import AutomaticContinuity.FlagTotalSpace

set_option autoImplicit false

/-!
# Entire-parameter vertical sprays preserving every finite flag constraint

Each point of the actual total space has an open neighborhood with one jointly
entire vertical spray, normalized by the identity parameter derivative. The
next closed flag is excluded from the source neighborhood, so the target
ball-complement spray preserves every relevant constraint, for all parameters.
This is local in the total-space point; compact holomorphic gluing is not
asserted.
-/

noncomputable section

namespace AutomaticContinuity.FlagLocalSprays

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ
abbrev Point (n : ℕ) := FinitePoint n × Pair

/-- Near a source point, no flag deeper than its own stratum can occur. -/
theorem exists_source_neighborhood (n : ℕ) (z : FinitePoint n) :
    ∃ k : ℕ, k ≤ n ∧ z ∈ finiteFlag n k ∧
      ∃ B : Set (FinitePoint n), IsOpen B ∧ z ∈ B ∧
        ∀ y ∈ B, ∀ j : ℕ, j ≤ n → y ∈ finiteFlag n j → j ≤ k := by
  obtain ⟨k, hkn, hzk⟩ := exists_stratum n z
  refine ⟨k, hkn, hzk.1, ?_⟩
  by_cases hlt : k < n
  · refine ⟨(finiteFlag n (k + 1))ᶜ, (isClosed_finiteFlag n (k + 1)).isOpen_compl,
      hzk.2 hlt, ?_⟩
    intro y hy j _hjn hyj
    by_contra hnot
    exact hy (finiteFlag_antitone n (by omega : k + 1 ≤ j) hyj)
  · refine ⟨univ, isOpen_univ, mem_univ z, ?_⟩
    intro y _hy j hjn _hyj
    omega

/-- Every admissible point admits a single open-neighborhood vertical spray
whose entire parameter fibres remain in the complete flag total space. -/
theorem exists_normalized_vertical_spray (n : ℕ) (q : Point n)
    (hq : q ∈ totalSet n) :
    ∃ W : Set (Point n), IsOpen W ∧ q ∈ W ∧
      ∃ S : Point n × Pair → Pair,
        Differentiable ℂ S ∧
        (∀ x : Point n, S (x, 0) = x.2) ∧
        (∀ x : Point n, Function.Injective (fun t => S (x, t))) ∧
        (∀ x : Point n, HasFDerivAt (fun t => S (x, t))
          (ContinuousLinearMap.id ℂ Pair) 0) ∧
        ∀ x ∈ W, ∀ t : Pair, (x.1, S (x, t)) ∈ totalSet n := by
  obtain ⟨k, hkn, hzk, B, hB, hzB, hBk⟩ := exists_source_neighborhood n q.1
  by_cases hk : k = 0
  · subst k
    refine ⟨B ×ˢ univ, hB.prod isOpen_univ, ⟨hzB, mem_univ _⟩,
      (fun xt => xt.1.2 + xt.2), ?_, ?_, ?_, ?_, ?_⟩
    · fun_prop
    · intro x; simp
    · intro x t u htu; exact add_left_cancel htu
    · intro x
      exact (hasFDerivAt_id (0 : Pair)).const_add x.2
    · intro x hx t
      apply mem_totalSet_iff.mpr
      intro j hj hjn hxj
      have hj0 := hBk x.1 hx.1 j hjn hxj
      omega
  · have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    have hqk : (k : ℝ) < euclideanPairNorm q.2 :=
      (mem_totalSet_iff.mp hq) k (by omega) hkn hzk
    obtain ⟨δ, hδ, S, hS, hS0, hSinj, hSd, hSout, _hcharts⟩ :=
      BallComplementSprays.exists_normalized_local_spray hkpos q.2 hqk
    let Y : Set Pair := {y | euclideanPairNorm (y - q.2) < δ}
    have hY : IsOpen Y :=
      isOpen_lt (continuous_euclideanPairNorm.comp (continuous_id.sub continuous_const))
        continuous_const
    have hqY : q.2 ∈ Y := by
      simpa only [Y, mem_ofPred_eq, sub_self, euclideanPairNorm_zero] using hδ
    refine ⟨B ×ˢ Y, hB.prod hY, ⟨hzB, hqY⟩,
      (fun xt => S (xt.1.2, xt.2)), ?_, ?_, ?_, ?_, ?_⟩
    · exact hS.comp (by fun_prop)
    · intro x; exact hS0 x.2
    · intro x; exact hSinj x.2
    · intro x; exact hSd x.2
    · intro x hx t
      apply mem_totalSet_iff.mpr
      intro j _hj hjn hxj
      exact (Nat.cast_le.mpr (hBk x.1 hx.1 j hjn hxj)).trans_lt
        (hSout x.2 hx.2 t)

end AutomaticContinuity.FlagLocalSprays
