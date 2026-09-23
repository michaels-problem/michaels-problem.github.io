import AutomaticContinuity.FlagBumpChart
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# Scaling an admissible section inward on a compact buffer

Compactness and openness give a single factor `lambda > 1` for which
`lambda⁻¹ • h` is still admissible on a neighbourhood of the compact set.
Scaling any admissible fibre value outward then supplies the uniform additive
margin `lambda - 1`, independent of the fibre parameter and active flag index.
-/

noncomputable section

namespace AutomaticContinuity.FlagScalingBuffer

open Set Metric FlagTotalSpace

abbrev Pair := ℂ × ℂ

/-- Uniform inward scaling is chosen from the actual open total space. The
section need only be continuous on the given open domain and admissible on
the compact set, not on that whole domain. -/
theorem exists_scaling_neighbourhood {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (h : FinitePoint n → Pair) (hh : ContinuousOn h U)
    (hadm : ∀ z ∈ K, (z, h z) ∈ totalSet n) :
    ∃ (l : ℝ) (V : Set (FinitePoint n)), 1 < l ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ z ∈ V, (z, l⁻¹ • h z) ∈ totalSet n := by
  let T : Set (ℝ × FinitePoint n) := Ioi 0 ×ˢ U
  let F : ℝ × FinitePoint n → FinitePoint n × Pair :=
    fun z => (z.2, z.1⁻¹ • h z.2)
  have hc : ContinuousOn F T := by
    have hi : ContinuousOn (fun z : ℝ × FinitePoint n => z.1⁻¹) T :=
      continuousOn_fst.inv₀ (fun z hz => ne_of_gt hz.1)
    exact continuousOn_snd.prodMk (hi.smul
      (hh.comp continuousOn_snd (fun z hz => hz.2)))
  let W : Set (ℝ × FinitePoint n) := T ∩ F ⁻¹' totalSet n
  have hW : IsOpen W := hc.isOpen_inter_preimage (isOpen_Ioi.prod hU) (isOpen_totalSet n)
  have hC : IsCompact (({1} : Set ℝ) ×ˢ K) := isCompact_singleton.prod hK
  have hCW : ({1} : Set ℝ) ×ˢ K ⊆ W := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht1 : t = 1 := ht
    subst t
    refine ⟨⟨by norm_num, hKU hz⟩, ?_⟩
    change (z, (1 : ℝ)⁻¹ • h z) ∈ totalSet n
    simpa only [inv_one, one_smul] using hadm z hz
  obtain ⟨δ, hδ, hδW⟩ := hC.exists_cthickening_subset_open hW hCW
  let l : ℝ := 1 + δ / 2
  let V : Set (FinitePoint n) := (fun z => (l, z)) ⁻¹' W
  have hl : 1 < l := by dsimp [l]; linarith
  have hV : IsOpen V := hW.preimage (by fun_prop)
  have hKV : K ⊆ V := by
    intro z hz
    apply hδW
    apply mem_cthickening_of_dist_le (l, z) (1, z) δ (({1} : Set ℝ) ×ˢ K)
      ⟨rfl, hz⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
    have hdiff : l - 1 = δ / 2 := by dsimp [l]; ring
    rw [hdiff, abs_of_pos (half_pos hδ)]
    exact half_le_self hδ.le
  exact ⟨l, V, hl, hV, hKV, fun z hz => hz.1.2, fun z hz => hz.2⟩

/-- Every active flag has index at least one. Therefore outward scaling
provides the same additive margin for every flag and every fibre value. -/
theorem admissible_smul_add {n : ℕ} {z : FinitePoint n} {w e : Pair} {l : ℝ}
    (hl : 1 < l) (hadm : (z, w) ∈ totalSet n)
    (he : euclideanPairNorm e ≤ l - 1) :
    (z, l • w + e) ∈ totalSet n := by
  apply mem_totalSet_iff.mpr
  intro k hk hkn hzk
  have hkw := (mem_totalSet_iff.mp hadm) k hk hkn hzk
  have hlpos : 0 < l := lt_trans zero_lt_one hl
  have hscaled : l * (k : ℝ) < euclideanPairNorm (l • w) := by
    rw [euclideanPairNorm_real_smul hlpos.le]
    exact mul_lt_mul_of_pos_left hkw hlpos
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  apply FlagBumpChart.norm_add_gt_of_margin hscaled
  exact he.trans (by nlinarith)

end AutomaticContinuity.FlagScalingBuffer
