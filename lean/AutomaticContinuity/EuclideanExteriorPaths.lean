import AutomaticContinuity.EuclideanPairRotations
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false

/-!
# Paths in the complement of an actual Euclidean pair ball

The default product norm is not used as the ball's defining norm. A path
avoiding zero is radially pushed beyond a chosen intermediate Euclidean
radius, with both endpoints fixed.
-/

noncomputable section

namespace AutomaticContinuity.EuclideanExteriorPaths

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ

theorem isPathConnected_complex_ne_zero : IsPathConnected {z : ℂ | z ≠ 0} := by
  let e := unitsHomeomorphNeZero (G₀ := ℂ)
  apply isPathConnected_iff_pathConnectedSpace.mpr
  exact e.surjective.pathConnectedSpace e.continuous

theorem isPathConnected_pair_ne_zero : IsPathConnected {z : Pair | z ≠ 0} := by
  have hC := isPathConnected_complex_ne_zero
  have hU : IsPathConnected (univ : Set ℂ) := convex_univ.isPathConnected (by simp)
  have h := (hC.prod hU).union (hU.prod hC)
    (show (({z : ℂ | z ≠ 0} ×ˢ univ) ∩ (univ ×ˢ {z : ℂ | z ≠ 0})).Nonempty
      from ⟨(1, 1), by simp⟩)
  convert h using 1
  ext z
  simp only [mem_union, mem_prod, mem_ofPred_eq, mem_univ, and_true, true_and]
  simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  tauto

def radialPush (s : ℝ) (z : Pair) : Pair :=
  max 1 (s / euclideanPairNorm z) • z

theorem continuousOn_radialPush (s : ℝ) :
    ContinuousOn (radialPush s) {z : Pair | z ≠ 0} := by
  unfold radialPush
  have hfactor : ContinuousOn (fun z : Pair => max 1 (s / euclideanPairNorm z))
      {z : Pair | z ≠ 0} := by
    have hd : ContinuousOn (fun z : Pair => s / euclideanPairNorm z)
        {z : Pair | z ≠ 0} := continuousOn_const.div continuous_euclideanPairNorm.continuousOn
      (fun z hz => (euclideanPairNorm_eq_zero_iff z).not.mpr hz)
    exact continuous_max.comp_continuousOn (continuousOn_const.prodMk hd)
  exact hfactor.smul continuousOn_id

theorem radialPush_eq_self {s : ℝ} {z : Pair} (hz : 0 < euclideanPairNorm z)
    (hs : s ≤ euclideanPairNorm z) : radialPush s z = z := by
  rw [radialPush, max_eq_left ((div_le_one hz).mpr hs), one_smul]

theorem le_norm_radialPush {s : ℝ} {z : Pair} (hz : 0 < euclideanPairNorm z) :
    s ≤ euclideanPairNorm (radialPush s z) := by
  rw [radialPush, euclideanPairNorm_real_smul (le_trans (by norm_num) (le_max_left _ _))]
  calc
    s = (s / euclideanPairNorm z) * euclideanPairNorm z :=
      (div_mul_cancel₀ s hz.ne').symm
    _ ≤ max 1 (s / euclideanPairNorm z) * euclideanPairNorm z :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hz.le

theorem joinedIn_exterior {r : ℝ} (hr : 0 ≤ r) {v w : Pair}
    (hv : r < euclideanPairNorm v) (hw : r < euclideanPairNorm w) :
    JoinedIn (exteriorEuclideanBall r) v w := by
  have hvpos : 0 < euclideanPairNorm v := hr.trans_lt hv
  have hwpos : 0 < euclideanPairNorm w := hr.trans_lt hw
  obtain ⟨s, hrs, hsv, hsw⟩ : ∃ s : ℝ, r < s ∧ s < euclideanPairNorm v ∧
      s < euclideanPairNorm w := by
    obtain ⟨s, hrs, hs⟩ := exists_between (lt_min hv hw)
    exact ⟨s, hrs, (lt_min_iff.mp hs).1, (lt_min_iff.mp hs).2⟩
  have hv0 : v ≠ 0 := (euclideanPairNorm_eq_zero_iff v).not.mp hvpos.ne'
  have hw0 : w ≠ 0 := (euclideanPairNorm_eq_zero_iff w).not.mp hwpos.ne'
  have hpath := isPathConnected_pair_ne_zero.joinedIn v hv0 w hw0
  have hmap := hpath.map (continuousOn_radialPush s)
  rw [radialPush_eq_self hvpos hsv.le, radialPush_eq_self hwpos hsw.le] at hmap
  apply hmap.mono
  rintro _ ⟨z, hz, rfl⟩
  exact hrs.trans_le (le_norm_radialPush
    (lt_of_le_of_ne (euclideanPairNorm_nonneg z)
      (Ne.symm ((euclideanPairNorm_eq_zero_iff z).not.mpr hz))))

end AutomaticContinuity.EuclideanExteriorPaths
