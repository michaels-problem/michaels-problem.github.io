import AutomaticContinuity.RemainingInputs
import AutomaticContinuity.LocalPointInterpolation
import AutomaticContinuity.LocalFlagInterpolation
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

/-!
# A direct finite-stage construction from an entire parameter family

This is a sufficient alternative to general continuous-section approximation.
The required family is entire over the whole preceding source space, agrees
exactly with its given stage at fibre zero, and preserves every old flag bound
for every fibre value. A single large value over the prescribed point suffices.
An exterior polynomial peak then constructs the next stage at any accuracy.

Existence of the entire families is an explicit, unproved input. Neither a
pointwise family nor a family over just one compact parameter set is substituted.
-/

noncomputable section

namespace AutomaticContinuity

open Set Metric

universe u

/-- Data sufficient to extend one entire stage. No family is asserted to exist. -/
structure EntireStageFamily (n : ℕ) (H : FinitePoint n → ℂ × ℂ) where
  toFun : FinitePoint n × (ℂ × ℂ) → ℂ × ℂ
  entire : Differentiable ℂ toFun
  at_zero : ∀ z, toFun (z, 0) = H z
  bounds : ∀ k : ℕ, 1 ≤ k → k ≤ n →
    ∀ z ∈ finiteFlag n k, ∀ v : ℂ × ℂ,
      (k : ℝ) < euclideanPairNorm (toFun (z, v))
  next_height : ∃ v : ℂ × ℂ,
    ((n + 1 : ℕ) : ℝ) < euclideanPairNorm (toFun (prescribedPoint n, v))

namespace EntireStageFamily

/-- One positive fibre tolerance works over the entire compact parameter set. -/
theorem exists_uniform_fiber_tolerance {n : ℕ} {K : Set (FinitePoint n)}
    (hK : IsCompact K) (G : FinitePoint n × (ℂ × ℂ) → ℂ × ℂ)
    (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ v : ℂ × ℂ, ‖v‖ ≤ δ →
      euclideanPairNorm (G (z, v) - G (z, 0)) < ε := by
  let U : Set (FinitePoint n × (ℂ × ℂ)) :=
    {w | euclideanPairNorm (G w - G (w.1, 0)) < ε}
  have hU : IsOpen U := isOpen_lt
    (continuous_euclideanPairNorm.comp
      (hG.sub (hG.comp (continuous_fst.prodMk continuous_const)))) continuous_const
  have hsub : K ×ˢ ({0} : Set (ℂ × ℂ)) ⊆ U := by
    rintro ⟨z, v⟩ ⟨hz, hv⟩
    obtain rfl := Set.mem_singleton_iff.mp hv
    simpa only [U, mem_ofPred_eq, sub_self, euclideanPairNorm_zero] using hε
  obtain ⟨δ, hδ, htube⟩ := (hK.prod isCompact_singleton).exists_cthickening_subset_open hU hsub
  refine ⟨δ, hδ, ?_⟩
  intro z hz v hv
  apply htube
  apply mem_cthickening_of_dist_le (z, v) (z, (0 : ℂ × ℂ)) δ
    (K ×ˢ ({0} : Set (ℂ × ℂ))) ⟨hz, rfl⟩
  simpa only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg v)] using hv

/-- An entire family gives a genuine next stage, with the manuscript's exact
source polydisc and with arbitrarily small prescribed Euclidean error. -/
theorem exists_next_stage {n : ℕ} {H : FinitePoint n → ℂ × ℂ}
    (G : EntireStageFamily n H) {ε : ℝ} (hε : 0 < ε) :
    ∃ Hnext : FinitePoint (n + 1) → ℂ × ℂ,
      Differentiable ℂ Hnext ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
        ∀ z ∈ finiteFlag (n + 1) k, (k : ℝ) < euclideanPairNorm (Hnext z)) ∧
      (∀ z ∈ polydisc (n + 1) (2 * ((n + 1 : ℕ) : ℝ)),
        euclideanPairNorm (Hnext z - H (prefixProjection n z)) < ε) := by
  let R : ℝ := 2 * ((n + 1 : ℕ) : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨v, hv⟩ := G.next_height
  obtain ⟨δ, hδ, hδG⟩ := exists_uniform_fiber_tolerance
    (isCompact_polydisc n hR) G.toFun G.entire.continuous hε
  have hvden : 0 < ‖v‖ + 1 := by positivity
  obtain ⟨q, hqp, hq⟩ := FiniteCauchy.exists_polynomial_peak hR
    (prescribedPoint_not_mem_polydisc (Nat.succ_pos n)) (div_pos hδ hvden)
  let P : FinitePoint (n + 1) → ℂ × ℂ := fun z => MvPolynomial.eval z q • v
  let F : FinitePoint (n + 1) → ℂ × ℂ := fun z => G.toFun (prefixProjection n z, P z)
  have hP : Differentiable ℂ P := (differentiable_polynomial_eval q).smul_const v
  refine ⟨F, G.entire.comp ((differentiable_prefixProjection n).prodMk hP), ?_, ?_⟩
  · intro k hk hkn z hz
    by_cases hle : k ≤ n
    · exact G.bounds k hk hle _ (prefixProjection_mem_finiteFlag hz) (P z)
    · have heq : k = n + 1 := by omega
      subst k
      rw [finiteFlag_self] at hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      simpa only [F, P, hqp, one_smul, prefixProjection_prescribedPoint] using hv
  · intro z hz
    have hzbase : prefixProjection n z ∈ polydisc n R := fun j => hz j.castSucc
    have hPsmall : ‖P z‖ ≤ δ := by
      dsimp only [P]
      rw [norm_smul]
      apply le_of_lt
      calc
        ‖MvPolynomial.eval z q‖ * ‖v‖ ≤ ‖MvPolynomial.eval z q‖ * (‖v‖ + 1) := by
          gcongr
          linarith
        _ < (δ / (‖v‖ + 1)) * (‖v‖ + 1) :=
          mul_lt_mul_of_pos_right (hq z hz) hvden
        _ = δ := div_mul_cancel₀ δ hvden.ne'
    simpa only [F, G.at_zero] using hδG _ hzbase (P z) hPsmall

end EntireStageFamily

/-- A sufficient global-family input for each entire stage. It remains unproved. -/
def EntireStageFamilyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ D : FiniteStageDatum n, Nonempty (EntireStageFamily n D.toFun)

/-- This constructs one coherent infinite family of stages from the stated
global-family input; it does not infer coherence from arbitrary finite prefixes. -/
theorem finiteStageConstruction_of_entireStageFamilies
    (hFamilies : EntireStageFamilyStatement) : FiniteStageConstructionStatement := by
  classical
  have extension (n : ℕ) (D : FiniteStageDatum (n + 1)) :
      ∃ Dnext : FiniteStageDatum (n + 2),
        ∀ z ∈ polydisc (n + 2) (2 * ((n + 2 : ℕ) : ℝ)),
          euclideanPairNorm (Dnext.toFun z - D.toFun (prefixProjection (n + 1) z)) <
            ((2 : ℝ) ^ (3 * (n + 2)))⁻¹ := by
    obtain ⟨G⟩ := hFamilies (n + 1) (by omega) D
    obtain ⟨Hnext, hEntire, hBounds, hError⟩ := G.exists_next_stage
      (ε := ((2 : ℝ) ^ (3 * (n + 2)))⁻¹) (by positivity)
    exact ⟨⟨Hnext, hEntire, hBounds⟩, hError⟩
  let next (n : ℕ) (D : FiniteStageDatum (n + 1)) : FiniteStageDatum (n + 2) :=
    Classical.choose (extension n D)
  have next_error (n : ℕ) (D : FiniteStageDatum (n + 1)) :
      ∀ z ∈ polydisc (n + 2) (2 * ((n + 2 : ℕ) : ℝ)),
        euclideanPairNorm ((next n D).toFun z - D.toFun (prefixProjection (n + 1) z)) <
          ((2 : ℝ) ^ (3 * (n + 2)))⁻¹ := Classical.choose_spec (extension n D)
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

/-- The original target follows if the explicit entire-family construction is
supplied. This theorem leaves that new sufficient input visible. -/
theorem theoremA_of_entireStageFamilies
    (hFamilies : EntireStageFamilyStatement) : TheoremAStatement.{u} :=
  theoremA_of_finite_stage_construction (finiteStageConstruction_of_entireStageFamilies hFamilies)

end AutomaticContinuity
