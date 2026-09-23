import AutomaticContinuity.CoefficientTopology
import Mathlib.Analysis.Normed.Lp.lpSpace

set_option autoImplicit false

/-!
# Completeness through weighted coefficient spaces

The coefficient algebra embeds into a product of ordinary complete ℓ¹ spaces.
Its image consists precisely of families whose entries represent the same
coefficients at different radii. Those compatibility equations are closed.
-/

noncomputable section

namespace AutomaticContinuity
namespace CoefficientSeries

abbrev WeightedL1 := lp (fun _ : MultiIndex => ℂ) 1

/-- Multiplying coefficients by their radial weights turns `q_r` into an ℓ¹ norm. -/
def weightedCoefficient (r : ℕ) (f : CoefficientSeries) (α : MultiIndex) : ℂ :=
  (r : ℂ) ^ totalDegree α * coeff f α

theorem norm_weightedCoefficient (r : ℕ) (f : CoefficientSeries) (α : MultiIndex) :
    ‖weightedCoefficient r f α‖ = weightedTerm r (f : FormalSeries) α := by
  simp [weightedCoefficient, weightedTerm, coeff, norm_pow, mul_comm]

def weightedCoefficients (r : ℕ) (f : CoefficientSeries) : WeightedL1 :=
  ⟨weightedCoefficient r f, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, norm_weightedCoefficient] using
      f.summable_all r⟩

@[simp] theorem weightedCoefficients_apply (r : ℕ) (f : CoefficientSeries)
    (α : MultiIndex) :
    weightedCoefficients r f α = (r : ℂ) ^ totalDegree α * coeff f α := rfl

def weightedCoefficientsLinearMap (r : ℕ) : CoefficientSeries →ₗ[ℂ] WeightedL1 where
  toFun := weightedCoefficients r
  map_add' f g := by
    ext α
    simp [coeff, mul_add]
  map_smul' c f := by
    ext α
    simp [coeff, mul_left_comm]

theorem norm_weightedCoefficients (r : ℕ) (f : CoefficientSeries) :
    ‖weightedCoefficients r f‖ = q r f := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one, weightedCoefficients,
    norm_weightedCoefficient, q]

theorem weightedCoefficients_comap (n : ℕ) :
    UniformSpace.comap (weightedCoefficients (n + 1))
      (inferInstance : UniformSpace WeightedL1) =
      (definingSeminorm n).toSeminormedAddCommGroup.toUniformSpace := by
  let _ := (definingSeminorm n).toSeminormedAddCommGroup
  let _ : UniformSpace CoefficientSeries :=
    (definingSeminorm n).toSeminormedAddCommGroup.toUniformSpace
  have h : Isometry (weightedCoefficients (n + 1)) :=
    AddMonoidHomClass.isometry_of_norm (weightedCoefficientsLinearMap (n + 1))
      (fun f => norm_weightedCoefficients (n + 1) f)
  exact h.isUniformInducing.comap_uniformSpace

/-- Every radius at once, with the ordinary product uniformity in the target. -/
def allWeightedCoefficients (f : CoefficientSeries) : ℕ → WeightedL1 :=
  fun n => weightedCoefficients (n + 1) f

theorem allWeightedCoefficients_isUniformInducing :
    IsUniformInducing allWeightedCoefficients := by
  rw [isUniformInducing_iff_uniformSpace]
  change UniformSpace.comap allWeightedCoefficients
    (Pi.uniformSpace (fun _ : ℕ => WeightedL1)) = _
  simp only [Pi.uniformSpace_eq, UniformSpace.comap_iInf,
    ← UniformSpace.comap_comap]
  change (⨅ n : ℕ, UniformSpace.comap (weightedCoefficients (n + 1))
    (inferInstance : UniformSpace WeightedL1)) = _
  simp_rw [weightedCoefficients_comap]
  rfl

def CompatibleWeightedData (x : ℕ → WeightedL1) : Prop :=
  ∀ (n : ℕ) (α : MultiIndex),
    x n α = ((n + 1 : ℕ) : ℂ) ^ totalDegree α * x 0 α

theorem compatibleWeightedData_isClosed :
    IsClosed {x : ℕ → WeightedL1 | CompatibleWeightedData x} := by
  simp only [CompatibleWeightedData, Set.ofPred_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro α
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : MultiIndex => ℂ) 1 α).continuous.comp
      (continuous_apply n)
  · exact continuous_const.mul
      ((lp.evalCLM ℂ (fun _ : MultiIndex => ℂ) 1 α).continuous.comp
        (continuous_apply 0))

theorem range_allWeightedCoefficients :
    Set.range allWeightedCoefficients = {x | CompatibleWeightedData x} := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩ n α
    simp [allWeightedCoefficients]
  · intro hx
    let f : FormalSeries := fun α => x 0 α
    have hf : HasFiniteCoefficientNorms f := by
      intro r hr
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
      have hn : Summable (fun α => ‖x n α‖) := by
        simpa using (lp.memℓp (x n)).summable (by norm_num)
      convert hn using 1
      funext α
      change ‖x 0 α‖ * ((n.succ : ℕ) : ℝ) ^ totalDegree α = ‖x n α‖
      rw [hx n α]
      rw [norm_mul, norm_pow, Complex.norm_natCast, Nat.succ_eq_add_one]
      exact mul_comm _ _
    refine ⟨⟨f, hf⟩, ?_⟩
    funext n
    apply lp.ext
    funext α
    exact (hx n α).symm

/-- Completeness is a proved property of the concrete coefficient topology. -/
instance coefficientCompleteSpace : CompleteSpace CoefficientSeries :=
  allWeightedCoefficients_isUniformInducing.completeSpace
    (by rw [range_allWeightedCoefficients]; exact compatibleWeightedData_isClosed.isComplete)

end CoefficientSeries
end AutomaticContinuity
