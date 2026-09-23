import AutomaticContinuity.FiniteStages
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring

/-!
# The elementary continuous modification at one finite stage

This replaces the manuscript's compactly supported bump by an explicit continuous
nonnegative factor depending on the last coordinate. It is zero on an open
neighbourhood of the approximation polydisc and equals one at the prescribed
point. Compact support and an upper bound of one are not needed by the restricted
`FiniteFlagApproximationStatement`; nonnegativity is exactly what preserves the
old escape bounds. The holomorphic approximation input itself remains unproved.
-/

namespace AutomaticContinuity

theorem euclideanPairNorm_real_smul {c : ℝ} (hc : 0 ≤ c) (v : ℂ × ℂ) :
    euclideanPairNorm (c • v) = c * euclideanPairNorm v := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _) (mul_nonneg hc (euclideanPairNorm_nonneg v))).mp
  rw [euclideanPairNorm_sq, mul_pow, euclideanPairNorm_sq]
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

theorem differentiable_prefixProjection (n : ℕ) : Differentiable ℂ (prefixProjection n) := by
  exact differentiable_pi.mpr fun j => differentiable_apply j.castSucc

theorem continuous_prefixProjection (n : ℕ) : Continuous (prefixProjection n) :=
  (differentiable_prefixProjection n).continuous

/-- A continuous nonnegative cutoff. It is allowed to grow away from the
approximation region, since only nonnegativity and two exact values are used. -/
noncomputable def stageCutoff (n : ℕ) (z : FinitePoint (n + 1)) : ℝ :=
  max 0 ((‖z (Fin.last n)‖ - 3 * ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))

/-- An open neighbourhood on which the cutoff vanishes. -/
def stageNeighbourhood (n : ℕ) : Set (FinitePoint (n + 1)) :=
  {z | ‖z (Fin.last n)‖ < 3 * ((n + 1 : ℕ) : ℝ)}

theorem stageCutoff_nonneg (n : ℕ) (z : FinitePoint (n + 1)) :
    0 ≤ stageCutoff n z := le_max_left _ _

theorem continuous_stageCutoff (n : ℕ) : Continuous (stageCutoff n) := by
  exact continuous_const.max
    (((continuous_apply (Fin.last n)).norm.sub continuous_const).div_const _)

theorem isOpen_stageNeighbourhood (n : ℕ) : IsOpen (stageNeighbourhood n) :=
  isOpen_lt (continuous_apply (Fin.last n)).norm continuous_const

theorem polydisc_subset_stageNeighbourhood (n : ℕ) :
    polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)) ⊆ stageNeighbourhood n := by
  intro z hz
  have h := hz (Fin.last n)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  change ‖z (Fin.last n)‖ < 3 * ((n + 1 : ℕ) : ℝ)
  linarith

theorem stageCutoff_eq_zero_on {n : ℕ} {z : FinitePoint (n + 1)}
    (hz : z ∈ stageNeighbourhood n) : stageCutoff n z = 0 := by
  apply max_eq_left
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr hz.le
  · positivity

@[simp] theorem stageCutoff_prescribedPoint (n : ℕ) :
    stageCutoff n (prescribedPoint (n + 1)) = 1 := by
  unfold stageCutoff prescribedPoint
  rw [norm_prescribedCoordinate]
  simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have heq : 4 * ((n : ℝ) + 1) - 3 * ((n : ℝ) + 1) = (n : ℝ) + 1 := by ring
  rw [heq, div_self hn]
  norm_num

/-- The preceding stage, lifted to one extra coordinate and multiplied by a
nonnegative real factor which doubles it at the new constrained point. -/
noncomputable def modifiedSection (n : ℕ) (H : FinitePoint n → ℂ × ℂ)
    (z : FinitePoint (n + 1)) : ℂ × ℂ :=
  (1 + stageCutoff n z) • H (prefixProjection n z)

theorem continuous_modifiedSection {n : ℕ} {H : FinitePoint n → ℂ × ℂ}
    (hH : Continuous H) : Continuous (modifiedSection n H) := by
  exact (continuous_const.add (continuous_stageCutoff n)).smul
    (hH.comp (continuous_prefixProjection n))

theorem modifiedSection_eq_lift_on {n : ℕ} {H : FinitePoint n → ℂ × ℂ}
    {z : FinitePoint (n + 1)} (hz : z ∈ stageNeighbourhood n) :
    modifiedSection n H z = H (prefixProjection n z) := by
  simp [modifiedSection, stageCutoff_eq_zero_on hz]

theorem differentiableOn_modifiedSection {n : ℕ} {H : FinitePoint n → ℂ × ℂ}
    (hH : Differentiable ℂ H) :
    DifferentiableOn ℂ (modifiedSection n H) (stageNeighbourhood n) := by
  apply (hH.comp (differentiable_prefixProjection n)).differentiableOn.congr
  intro z hz
  exact modifiedSection_eq_lift_on hz

theorem norm_modifiedSection (n : ℕ) (H : FinitePoint n → ℂ × ℂ)
    (z : FinitePoint (n + 1)) :
    euclideanPairNorm (modifiedSection n H z) =
      (1 + stageCutoff n z) * euclideanPairNorm (H (prefixProjection n z)) := by
  exact euclideanPairNorm_real_smul (by linarith [stageCutoff_nonneg n z]) _

theorem norm_lift_le_modifiedSection (n : ℕ) (H : FinitePoint n → ℂ × ℂ)
    (z : FinitePoint (n + 1)) :
    euclideanPairNorm (H (prefixProjection n z)) ≤
      euclideanPairNorm (modifiedSection n H z) := by
  rw [norm_modifiedSection]
  nlinarith [stageCutoff_nonneg n z, euclideanPairNorm_nonneg (H (prefixProjection n z))]

@[simp] theorem prefixProjection_prescribedPoint (n : ℕ) :
    prefixProjection n (prescribedPoint (n + 1)) = prescribedPoint n := rfl

theorem prefixProjection_mem_finiteFlag {n k : ℕ} {z : FinitePoint (n + 1)}
    (hz : z ∈ finiteFlag (n + 1) k) : prefixProjection n z ∈ finiteFlag n k := by
  intro j hj
  exact hz j.castSucc hj

/-- The continuous modification meets every required lower bound at the next
stage. This proof uses no holomorphic approximation theorem. -/
theorem modifiedSection_finite_bounds {n : ℕ} (hn : 1 ≤ n)
    {H : FinitePoint n → ℂ × ℂ}
    (hH : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
      ∀ z ∈ finiteFlag (n + 1) k, (k : ℝ) < euclideanPairNorm (modifiedSection n H z) := by
  intro k hk hkn z hz
  by_cases hle : k ≤ n
  · exact (hH k hk hle (prefixProjection n z) (prefixProjection_mem_finiteFlag hz)).trans_le
      (norm_lift_le_modifiedSection n H z)
  · have hkeq : k = n + 1 := by omega
    subst k
    rw [finiteFlag_self] at hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hold := hH n hn le_rfl (prescribedPoint n) (prescribedPoint_mem_finiteFlag n n)
    rw [norm_modifiedSection, stageCutoff_prescribedPoint, prefixProjection_prescribedPoint]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith

/-- One inductive step, conditional on the precise restricted approximation
claim. The premise is deliberately visible: the Oka approximation is not proved
by this result. -/
theorem finiteStage_extension (hApprox : FiniteFlagApproximationStatement)
    {n : ℕ} (hn : 1 ≤ n) {H : FinitePoint n → ℂ × ℂ}
    (hEntire : Differentiable ℂ H)
    (hBounds : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (H z))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Hnext : FinitePoint (n + 1) → ℂ × ℂ,
      Differentiable ℂ Hnext ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
        ∀ z ∈ finiteFlag (n + 1) k, (k : ℝ) < euclideanPairNorm (Hnext z)) ∧
      (∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
        euclideanPairNorm (Hnext z - H (prefixProjection n z)) < ε) := by
  obtain ⟨Hnext, hNextEntire, hError, hNextBounds⟩ :=
    hApprox (n + 1) (by omega) (2 * ((n + 1 : ℕ) : ℝ)) (by positivity)
      (modifiedSection n H) (continuous_modifiedSection hEntire.continuous)
      ⟨stageNeighbourhood n, isOpen_stageNeighbourhood n,
        polydisc_subset_stageNeighbourhood n, differentiableOn_modifiedSection hEntire⟩
      (modifiedSection_finite_bounds hn hBounds) ε hε
  refine ⟨Hnext, hNextEntire, hNextBounds, ?_⟩
  intro z hz
  have heq := modifiedSection_eq_lift_on (H := H) (polydisc_subset_stageNeighbourhood n hz)
  rw [← heq]
  exact hError z hz

/-- A single entire finite stage together with its flag lower bounds. This data
structure does not assert that a stage exists. -/
structure FiniteStageDatum (n : ℕ) where
  toFun : FinitePoint n → ℂ × ℂ
  entire : Differentiable ℂ toFun
  bounds : ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ∀ z ∈ finiteFlag n k, (k : ℝ) < euclideanPairNorm (toFun z)

/-- The actual constant initial stage from the manuscript. -/
def initialFiniteStage : FiniteStageDatum 1 where
  toFun := fun _ => (2, 0)
  entire := differentiable_const _
  bounds := by
    intro k hk hk1 z _hz
    have hkeq : k = 1 := by omega
    subst k
    norm_num [euclideanPairNorm]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-- The finite-stage induction is elementary once the specialised approximation
claim is available. This conditional theorem does not discharge that claim and
therefore does not prove the unconditional finite-stage construction. -/
theorem finiteStageConstruction_of_approximation
    (hApprox : FiniteFlagApproximationStatement) : FiniteStageConstructionStatement := by
  classical
  have extension (n : ℕ) (D : FiniteStageDatum (n + 1)) :
      ∃ Dnext : FiniteStageDatum (n + 2),
        ∀ z ∈ polydisc (n + 2) (2 * ((n + 2 : ℕ) : ℝ)),
          euclideanPairNorm (Dnext.toFun z - D.toFun (prefixProjection (n + 1) z)) <
            ((2 : ℝ) ^ (3 * (n + 2)))⁻¹ := by
    obtain ⟨Hnext, hEntire, hBounds, hError⟩ := finiteStage_extension hApprox
      (n := n + 1) (by omega) D.entire D.bounds
      (ε := ((2 : ℝ) ^ (3 * (n + 2)))⁻¹) (by positivity)
    exact ⟨⟨Hnext, hEntire, hBounds⟩, hError⟩
  let next (n : ℕ) (D : FiniteStageDatum (n + 1)) : FiniteStageDatum (n + 2) :=
    Classical.choose (extension n D)
  have next_error (n : ℕ) (D : FiniteStageDatum (n + 1)) :
      ∀ z ∈ polydisc (n + 2) (2 * ((n + 2 : ℕ) : ℝ)),
        euclideanPairNorm ((next n D).toFun z - D.toFun (prefixProjection (n + 1) z)) <
          ((2 : ℝ) ^ (3 * (n + 2)))⁻¹ :=
    Classical.choose_spec (extension n D)
  let stages : (n : ℕ) → FiniteStageDatum (n + 1) :=
    fun n => Nat.rec initialFiniteStage (fun m D => next m D) n
  let F : (n : ℕ) → FinitePoint n → ℂ × ℂ
    | 0 => fun _ => 0
    | n + 1 => (stages n).toFun
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro n hn
    cases n with
    | zero => omega
    | succ n => exact (stages n).entire
  · intro z
    rfl
  · intro n k hk hkn z hz
    cases n with
    | zero => omega
    | succ n => exact (stages n).bounds k hk hkn z hz
  · intro n hn z hz
    cases n with
    | zero => omega
    | succ n => exact next_error n (stages n) z hz

end AutomaticContinuity
