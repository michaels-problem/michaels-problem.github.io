import AutomaticContinuity.BallComplementEmbeddings
import AutomaticContinuity.LocalPointInterpolation
import AutomaticContinuity.LocalFlagInterpolation
import Mathlib.Analysis.Complex.Liouville

/-!
# An actual escape construction through dimension three

The first two stages are constant, with their exact required small error.
The third stage is an entire map into the complement of the radius-two ball,
composed with an exterior polynomial peak. It stays close to the second stage
on the radius-six polydisc and exceeds three at the final flag point.

This is a finite prefix only. No continuation to arbitrary dimension and no
instance of `FiniteStageConstructionStatement` is asserted.
-/

noncomputable section

namespace AutomaticContinuity.ThreeStageConstruction

open Set Filter Metric
open scoped Topology

abbrev Pair := ℂ × ℂ

/-- The slightly enlarged constant value at the second stage. -/
def secondValue : Pair := ((2 + 1 / 128 : ℂ), 0)

theorem euclideanPairNorm_fst (c : ℂ) : euclideanPairNorm (c, 0) = ‖c‖ := by
  simp only [euclideanPairNorm, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact Real.sqrt_sq (norm_nonneg c)

theorem norm_secondValue : euclideanPairNorm secondValue = 2 + 1 / 128 := by
  rw [secondValue, euclideanPairNorm_fst]
  norm_num

theorem norm_secondValue_sub_first :
    euclideanPairNorm (secondValue - (2, 0)) = 1 / 128 := by
  change euclideanPairNorm ((2 + 1 / 128 : ℂ) - 2, (0 : ℂ) - 0) = _
  simp only [sub_self]
  rw [euclideanPairNorm_fst]
  norm_num

/-- An injective entire map has values beyond every Euclidean radius. This is
an application of the checked vector-valued complex Liouville theorem. -/
theorem exists_large_value {φ : Pair → Pair} (hφ : Differentiable ℂ φ)
    (hφinj : Function.Injective φ) (R : ℝ) : ∃ t : Pair, R < euclideanPairNorm (φ t) := by
  by_contra! hbound
  have hb : Bornology.IsBounded (Set.range φ) :=
    isBounded_iff_forall_norm_le.mpr ⟨R, by
      rintro _ ⟨t, rfl⟩
      exact (norm_le_euclideanPairNorm _).trans (hbound t)⟩
  have heq := hφinj (hφ.apply_eq_apply_of_bounded hb (0 : Pair) (1, 0))
  have hc := congrArg Prod.fst heq
  norm_num at hc

/-- The distinguished third-stage value can exceed any prescribed finite
height while retaining global radius-two avoidance and the exact small error. -/
theorem exists_third_stage_above (height : ℝ) :
    ∃ F : FinitePoint 3 → Pair,
      Differentiable ℂ F ∧
      (∀ z, 2 < euclideanPairNorm (F z)) ∧
      height < euclideanPairNorm (F (prescribedPoint 3)) ∧
      ∀ z ∈ polydisc 3 6,
        euclideanPairNorm (F z - secondValue) < ((2 : ℝ) ^ (3 * 3))⁻¹ := by
  obtain ⟨φ, hφ, hφinj, hφ0, _hφd, hφout⟩ :=
    BallComplementEmbeddings.exists_normalized_entire_embedding (by norm_num : (0 : ℝ) < 2)
      secondValue (by rw [norm_secondValue]; norm_num)
  obtain ⟨t, ht⟩ := exists_large_value hφ hφinj height
  have hcont : ContinuousAt (fun v : Pair => euclideanPairNorm (φ v - secondValue)) 0 :=
    (continuous_euclideanPairNorm.comp (hφ.continuous.sub continuous_const)).continuousAt
  have hnear : {v : Pair | euclideanPairNorm (φ v - secondValue) < ((2 : ℝ) ^ (3 * 3))⁻¹}
      ∈ 𝓝 (0 : Pair) := by
    have heps : euclideanPairNorm (φ 0 - secondValue) < ((2 : ℝ) ^ (3 * 3))⁻¹ := by
      simp only [hφ0, sub_self, euclideanPairNorm_zero]
      positivity
    exact hcont.eventually (gt_mem_nhds heps)
  obtain ⟨η, hη, hηnear⟩ := Metric.mem_nhds_iff.mp hnear
  have htden : 0 < ‖t‖ + 1 := by positivity
  have hpoint : prescribedPoint 3 ∉ polydisc 3 6 := by
    convert prescribedPoint_not_mem_polydisc (by norm_num : 0 < (3 : ℕ)) using 1
    norm_num
  obtain ⟨q, hqpoint, hqsmall⟩ := FiniteCauchy.exists_polynomial_peak
    (by norm_num : (0 : ℝ) ≤ 6)
    hpoint
    (div_pos hη htden)
  let P : FinitePoint 3 → Pair := fun z => MvPolynomial.eval z q • t
  let F : FinitePoint 3 → Pair := fun z => φ (P z)
  have hP : Differentiable ℂ P := (differentiable_polynomial_eval q).smul_const t
  refine ⟨F, hφ.comp hP, fun z => hφout (P z), ?_, ?_⟩
  · simpa only [F, P, hqpoint, one_smul] using ht
  · intro z hz
    apply hηnear
    rw [Metric.mem_ball, dist_zero_right]
    change ‖MvPolynomial.eval z q • t‖ < η
    rw [norm_smul]
    have hq := hqsmall z hz
    calc
      ‖MvPolynomial.eval z q‖ * ‖t‖ ≤ ‖MvPolynomial.eval z q‖ * (‖t‖ + 1) := by
        gcongr
        linarith
      _ < (η / (‖t‖ + 1)) * (‖t‖ + 1) := mul_lt_mul_of_pos_right hq htden
      _ = η := div_mul_cancel₀ η (ne_of_gt htden)

/-- The original height-three specialization. -/
theorem exists_third_stage :
    ∃ F : FinitePoint 3 → Pair,
      Differentiable ℂ F ∧
      (∀ z, 2 < euclideanPairNorm (F z)) ∧
      3 < euclideanPairNorm (F (prescribedPoint 3)) ∧
      ∀ z ∈ polydisc 3 6,
        euclideanPairNorm (F z - secondValue) < ((2 : ℝ) ^ (3 * 3))⁻¹ :=
  exists_third_stage_above 3

/-- Extend the three explicitly constructed stages by unused zero maps, so
the result has precisely the dependent function-family type of the full problem. -/
def prefixFamily (F : FinitePoint 3 → Pair) : (n : ℕ) → FinitePoint n → Pair
  | 0 => fun _ => 0
  | 1 => fun _ => (2, 0)
  | 2 => fun _ => secondValue
  | 3 => F
  | _ + 4 => fun _ => 0

/-- A genuine finite prefix of the required construction. Bounds are asserted
only through dimension three, and successive-stage errors only for stages two
and three, with exactly the original polydiscs and reciprocal powers of two. -/
theorem exists_stage_family_through_three :
    ∃ F : (n : ℕ) → FinitePoint n → Pair,
      (∀ n : ℕ, 1 ≤ n → n ≤ 3 → Differentiable ℂ (F n)) ∧
      (∀ z : FinitePoint 1, F 1 z = (2, 0)) ∧
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → n ≤ 3 →
        ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (F n z)) ∧
      (∀ n : ℕ, 1 ≤ n → n + 1 ≤ 3 →
        ∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
          euclideanPairNorm (F (n + 1) z - F n (prefixProjection n z)) <
            ((2 : ℝ) ^ (3 * (n + 1)))⁻¹) := by
  obtain ⟨H, hHd, hHout, hHpoint, hHapprox⟩ := exists_third_stage
  refine ⟨prefixFamily H, ?_, fun _ => rfl, ?_, ?_⟩
  · intro n hn hn3
    interval_cases n
    · exact differentiable_const _
    · exact differentiable_const _
    · exact hHd
  · intro n k hk hkn hn z hz
    have hn0 : 1 ≤ n := hk.trans hkn
    interval_cases n
    · have hk1 : k = 1 := by omega
      subst k
      simp only [prefixFamily, Nat.cast_one]
      rw [euclideanPairNorm_fst]
      norm_num
    · have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast hkn
      change (k : ℝ) < euclideanPairNorm secondValue
      rw [norm_secondValue]
      linarith
    · by_cases hk3 : k = 3
      · subst k
        rw [finiteFlag_self] at hz
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact hHpoint
      · have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
        exact hk2.trans_lt (hHout z)
  · intro n hn hn3 z hz
    have hn2 : n ≤ 2 := by omega
    interval_cases n
    · change euclideanPairNorm (secondValue - (2, 0)) < ((2 : ℝ) ^ (3 * 2))⁻¹
      rw [norm_secondValue_sub_first]
      norm_num
    · exact hHapprox z (by convert hz using 1; norm_num)

end AutomaticContinuity.ThreeStageConstruction
