import AutomaticContinuity.FiniteCauchyBounds
import AutomaticContinuity.Evaluation
import AutomaticContinuity.FiniteStages

/-!
# Embedding finite-variable coefficient families

A finite multiindex is extended by zero to the remaining countably many
coordinates. Coefficients are extended by zero outside the range of that
embedding. This gives exact coefficient norm and evaluation identities.
Membership in the coefficient algebra still requires the explicitly stated
summability assumptions; no holomorphic Taylor representation is asserted.
-/

noncomputable section

namespace AutomaticContinuity

open scoped BigOperators

/-- Extend a finite multiindex by zero outside the first `n` coordinates. -/
def finiteIndexEmbedding (n : ℕ) : FiniteMultiIndex n ↪ MultiIndex where
  toFun α := Finsupp.embDomain ⟨Fin.val, Fin.val_injective⟩
    (Finsupp.equivFunOnFinite.symm α)
  inj' := (Finsupp.embDomain_injective _).comp Finsupp.equivFunOnFinite.symm.injective

@[simp] theorem finiteIndexEmbedding_apply {n : ℕ} (α : FiniteMultiIndex n) (j : Fin n) :
    finiteIndexEmbedding n α j.val = α j := by
  exact Finsupp.embDomain_apply_self _ _ _

@[simp] theorem totalDegree_finiteIndexEmbedding {n : ℕ} (α : FiniteMultiIndex n) :
    totalDegree (finiteIndexEmbedding n α) = finiteTotalDegree α := by
  change Finsupp.degree (Finsupp.embDomain _ (Finsupp.equivFunOnFinite.symm α)) = _
  rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain, Finsupp.degree_apply]
  change (Finsupp.equivFunOnFinite.symm α).sum (fun _ m => m) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rfl

@[simp] theorem monomialValue_finiteIndexEmbedding {n : ℕ}
    (w : ℕ → ℂ) (α : FiniteMultiIndex n) :
    monomialValue w (finiteIndexEmbedding n α) = ∏ j : Fin n, w j.val ^ α j := by
  simp [monomialValue, finiteIndexEmbedding, Finsupp.prod_embDomain, Finsupp.prod_fintype]

/-- A formal coefficient family in countably many variables, supported on the
embedded finite multiindices. -/
def extendFiniteCoefficients {n : ℕ} (c : FiniteMultiIndex n → ℂ) : FormalSeries :=
  Function.extend (finiteIndexEmbedding n) c (fun _ => 0)

@[simp] theorem coeff_extendFiniteCoefficients {n : ℕ}
    (c : FiniteMultiIndex n → ℂ) (α : FiniteMultiIndex n) :
    MvPowerSeries.coeff (finiteIndexEmbedding n α) (extendFiniteCoefficients c) = c α := by
  rw [MvPowerSeries.coeff_apply]
  exact (finiteIndexEmbedding n).injective.extend_apply c (fun _ => 0) α

theorem coeff_extendFiniteCoefficients_outside {n : ℕ}
    (c : FiniteMultiIndex n → ℂ) {α : MultiIndex}
    (hα : α ∉ Set.range (finiteIndexEmbedding n)) :
    MvPowerSeries.coeff α (extendFiniteCoefficients c) = 0 := by
  rw [MvPowerSeries.coeff_apply]
  exact Function.extend_apply' c (fun _ => 0) α hα

@[simp] theorem weightedTerm_extendFiniteCoefficients {n : ℕ}
    (r : ℕ) (c : FiniteMultiIndex n → ℂ) (α : FiniteMultiIndex n) :
    weightedTerm r (extendFiniteCoefficients c) (finiteIndexEmbedding n α) =
      finiteWeightedTerm (r : ℝ) c α := by
  simp [weightedTerm, finiteWeightedTerm]

theorem summable_extendFiniteCoefficients_iff {n : ℕ}
    (r : ℕ) (c : FiniteMultiIndex n → ℂ) :
    Summable (weightedTerm r (extendFiniteCoefficients c)) ↔
      Summable (finiteWeightedTerm (r : ℝ) c) := by
  have hzero : ∀ α ∉ Set.range (finiteIndexEmbedding n),
      weightedTerm r (extendFiniteCoefficients c) α = 0 := by
    intro α hα
    simp [weightedTerm, coeff_extendFiniteCoefficients_outside c hα]
  simpa only [Function.comp_def, weightedTerm_extendFiniteCoefficients] using
    ((finiteIndexEmbedding n).injective.summable_iff hzero).symm

theorem tsum_weightedTerm_extendFiniteCoefficients {n : ℕ}
    (r : ℕ) (c : FiniteMultiIndex n → ℂ) :
    (∑' α : MultiIndex, weightedTerm r (extendFiniteCoefficients c) α) =
      ∑' α : FiniteMultiIndex n, finiteWeightedTerm (r : ℝ) c α := by
  have hzero : ∀ α ∉ Set.range (finiteIndexEmbedding n),
      weightedTerm r (extendFiniteCoefficients c) α = 0 := by
    intro α hα
    simp [weightedTerm, coeff_extendFiniteCoefficients_outside c hα]
  have hsupp : Function.support (weightedTerm r (extendFiniteCoefficients c)) ⊆
      Set.range (finiteIndexEmbedding n) := by
    intro α hα
    by_contra h
    exact hα (hzero α h)
  simpa only [Function.comp_def, weightedTerm_extendFiniteCoefficients] using
    ((finiteIndexEmbedding n).injective.tsum_eq hsupp).symm

/-- Construct an actual element of `𝓔` from a finite-variable coefficient family
which is absolutely summable at every positive integral radius. -/
def embedFiniteCoefficients {n : ℕ} (c : FiniteMultiIndex n → ℂ)
    (hc : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) c)) : CoefficientSeries :=
  ⟨extendFiniteCoefficients c, fun r hr =>
    (summable_extendFiniteCoefficients_iff r c).mpr (hc r hr)⟩

@[simp] theorem q_embedFiniteCoefficients {n : ℕ} (c : FiniteMultiIndex n → ℂ)
    (hc : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) c)) (r : ℕ) :
    CoefficientSeries.q r (embedFiniteCoefficients c hc) =
      ∑' α : FiniteMultiIndex n, finiteWeightedTerm (r : ℝ) c α :=
  tsum_weightedTerm_extendFiniteCoefficients r c

theorem evaluate_embedFiniteCoefficients {n : ℕ} (c : FiniteMultiIndex n → ℂ)
    (hc : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) c)) (w : BoundedSequence) :
    CoefficientSeries.evaluate w (embedFiniteCoefficients c hc) =
      ∑' α : FiniteMultiIndex n, c α * ∏ j : Fin n, (restrictSequence n w j) ^ α j := by
  have hzero : ∀ α ∉ Set.range (finiteIndexEmbedding n),
      MvPowerSeries.coeff α (extendFiniteCoefficients c) * monomialValue w.val α = 0 := by
    intro α hα
    rw [coeff_extendFiniteCoefficients_outside c hα, zero_mul]
  have hsupp : Function.support
      (fun α => MvPowerSeries.coeff α (extendFiniteCoefficients c) * monomialValue w.val α) ⊆
      Set.range (finiteIndexEmbedding n) := by
    intro α hα
    by_contra h
    exact hα (hzero α h)
  have heq := ((finiteIndexEmbedding n).injective.tsum_eq hsupp).symm
  simpa only [CoefficientSeries.evaluate, CoefficientSeries.coeff, embedFiniteCoefficients,
    Function.comp_def, coeff_extendFiniteCoefficients,
    monomialValue_finiteIndexEmbedding, restrictSequence] using heq

end AutomaticContinuity
