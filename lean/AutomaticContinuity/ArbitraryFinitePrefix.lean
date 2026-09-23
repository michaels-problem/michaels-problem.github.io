import AutomaticContinuity.ThreeStageConstruction

/-!
# Actual finite prefixes through every prescribed dimension

For each cutoff `N`, choose the third-stage distinguished value larger than
`N`, and let every subsequent stage depend only on the first three coordinates.
All later stage errors vanish. The escape bounds then hold through dimension
`N`, since every flag of level at least three fixes those first coordinates.

The quantifiers are `∀ N, ∃ F_N`. The chosen third map depends on the cutoff.
This does not give a single coherent family with bounds at every dimension.
-/

noncomputable section

namespace AutomaticContinuity.ArbitraryFinitePrefix

open ThreeStageConstruction
open Filter
open scoped Topology

/-- The first three coordinates, for a source with at least three coordinates. -/
def firstThree {n : ℕ} (hn : 3 ≤ n) (z : FinitePoint n) : FinitePoint 3 :=
  fun j => z ⟨j.val, j.isLt.trans_le hn⟩

theorem differentiable_firstThree {n : ℕ} (hn : 3 ≤ n) :
    Differentiable ℂ (firstThree hn) :=
  differentiable_pi.mpr fun j => differentiable_apply (⟨j.val, j.isLt.trans_le hn⟩ : Fin n)

@[simp] theorem firstThree_self (z : FinitePoint 3) : firstThree (by omega) z = z := rfl

theorem firstThree_eq_prescribed {n k : ℕ} (hn : 3 ≤ n) (hk : 3 ≤ k)
    {z : FinitePoint n} (hz : z ∈ finiteFlag n k) :
    firstThree hn z = prescribedPoint 3 := by
  funext j
  exact hz ⟨j.val, j.isLt.trans_le hn⟩ (j.isLt.trans_le hk)

theorem firstThree_prefixProjection {n : ℕ} (hn : 3 ≤ n) (z : FinitePoint (n + 1)) :
    firstThree hn (prefixProjection n z) =
      firstThree (hn.trans (Nat.le_succ n)) z := rfl

/-- Freeze every stage after the third by pulling it back along the first
three coordinates. The zero stage is unused. -/
def family (H : FinitePoint 3 → Pair) (n : ℕ) (z : FinitePoint n) : Pair :=
  if hn : 3 ≤ n then H (firstThree hn z)
  else if n = 1 then (2, 0) else secondValue

@[simp] theorem family_one (H : FinitePoint 3 → Pair) (z : FinitePoint 1) :
    family H 1 z = (2, 0) := by simp [family]

@[simp] theorem family_two (H : FinitePoint 3 → Pair) (z : FinitePoint 2) :
    family H 2 z = secondValue := by simp [family]

theorem family_large (H : FinitePoint 3 → Pair) {n : ℕ} (hn : 3 ≤ n)
    (z : FinitePoint n) : family H n z = H (firstThree hn z) := by
  simp only [family, dite_eq_left hn]

@[simp] theorem family_three (H : FinitePoint 3 → Pair) (z : FinitePoint 3) :
    family H 3 z = H z := by rw [family_large H (by omega), firstThree_self]

theorem family_succ_eq_prefix (H : FinitePoint 3 → Pair) {n : ℕ} (hn : 3 ≤ n)
    (z : FinitePoint (n + 1)) : family H (n + 1) z = family H n (prefixProjection n z) := by
  rw [family_large H (hn.trans (Nat.le_succ n)), family_large H hn,
    firstThree_prefixProjection]

/-- Every finite cutoff admits an actual family with the original escape
bounds up to that cutoff. Holomorphicity and the exact stage error inequalities
hold at all stages; the later errors are zero. The family may depend on `N`. -/
theorem exists_stage_family_up_to (N : ℕ) :
    ∃ F : (n : ℕ) → FinitePoint n → Pair,
      (∀ n : ℕ, 1 ≤ n → Differentiable ℂ (F n)) ∧
      (∀ z : FinitePoint 1, F 1 z = (2, 0)) ∧
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → n ≤ N →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (F n z)) ∧
      (∀ n : ℕ, 1 ≤ n →
        ∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
          euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z)) <
            ((2 : ℝ) ^ (3 * (n + 1)))⁻¹) := by
  obtain ⟨H, hHd, hHout, hHpoint, hHapprox⟩ := exists_third_stage_above (N : ℝ)
  refine ⟨family H, ?_, family_one H, ?_, ?_⟩
  · intro n hn
    by_cases hn3 : 3 ≤ n
    · change Differentiable ℂ (fun z => family H n z)
      simp only [family, dite_eq_left hn3]
      exact hHd.comp (differentiable_firstThree hn3)
    · have hn12 : n = 1 ∨ n = 2 := by omega
      rcases hn12 with rfl | rfl
      · change Differentiable ℂ (fun z => family H 1 z)
        simpa only [family_one] using differentiable_const (2, 0)
      · change Differentiable ℂ (fun z => family H 2 z)
        simpa only [family_two] using differentiable_const secondValue
  · intro n k hk hkn hnN z hz
    by_cases hn3 : 3 ≤ n
    · rw [family_large H hn3]
      by_cases hk3 : 3 ≤ k
      · rw [firstThree_eq_prescribed hn3 hk3 hz]
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast hkn.trans hnN
        exact hkN.trans_lt hHpoint
      · have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
        exact hk2.trans_lt (hHout _)
    · have hn12 : n = 1 ∨ n = 2 := by omega
      rcases hn12 with rfl | rfl
      · have hk1 : k = 1 := by omega
        subst k
        rw [family_one, euclideanPairNorm_fst]
        norm_num
      · rw [family_two, norm_secondValue]
        have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast hkn
        linarith
  · intro n hn z hz
    by_cases hn3 : 3 ≤ n
    · rw [family_succ_eq_prefix H hn3, sub_self, euclideanPairNorm_zero]
      positivity
    · have hn12 : n = 1 ∨ n = 2 := by omega
      rcases hn12 with rfl | rfl
      · rw [family_two, family_one, norm_secondValue_sub_first]
        norm_num
      · rw [family_three, family_two]
        exact hHapprox z (by convert hz using 1; norm_num)

/-- The specific large-height construction has a genuine obstruction to a
normal-family argument: its values at one fixed point escape every bounded
set. Even passage to a cofinal subsequence cannot give a pointwise limit there.
This concerns this construction, not every possible choice of finite prefixes. -/
theorem not_tendsto_of_growing_third_height
    (H : ℕ → FinitePoint 3 → Pair)
    (hheight : ∀ N : ℕ, (N : ℝ) < euclideanPairNorm (H N (prescribedPoint 3)))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (v : Pair) :
    ¬ Tendsto (fun n => H (a n) (prescribedPoint 3)) atTop (𝓝 v) := by
  have hgrowth : Tendsto (fun N => euclideanPairNorm (H N (prescribedPoint 3))) atTop atTop :=
    tendsto_atTop_mono (fun N => (hheight N).le) tendsto_natCast_atTop_atTop
  intro hlim
  have hnorm := continuous_euclideanPairNorm.continuousAt.tendsto.comp hlim
  have hlarge := (hgrowth.comp ha).eventually_ge_atTop (euclideanPairNorm v + 1)
  have hsmall := hnorm.eventually (gt_mem_nhds (by linarith :
    euclideanPairNorm v < euclideanPairNorm v + 1))
  obtain ⟨n, hnlarge, hnsmall⟩ := (hlarge.and hsmall).exists
  exact (not_lt_of_ge hnlarge) hnsmall

end AutomaticContinuity.ArbitraryFinitePrefix
