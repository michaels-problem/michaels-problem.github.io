import AutomaticContinuity.FiniteEmbedding

set_option autoImplicit false

noncomputable section

namespace AutomaticContinuity

open CoefficientSeries

theorem finiteIndexEmbedding_apply_of_ge {n : ℕ} (α : FiniteMultiIndex n)
    {j : ℕ} (hj : n ≤ j) : finiteIndexEmbedding n α j = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact (Nat.not_lt_of_ge hj) (hi ▸ i.isLt)

theorem mem_range_finiteIndexEmbedding_iff {n : ℕ} (α : MultiIndex) :
    α ∈ Set.range (finiteIndexEmbedding n) ↔ ∀ j, n ≤ j → α j = 0 := by
  constructor
  · rintro ⟨β, rfl⟩ j hj
    exact finiteIndexEmbedding_apply_of_ge β hj
  · intro h
    refine ⟨fun j : Fin n => α j.val, ?_⟩
    ext j
    by_cases hj : j < n
    · exact finiteIndexEmbedding_apply _ ⟨j, hj⟩
    · rw [finiteIndexEmbedding_apply_of_ge _ (Nat.le_of_not_gt hj),
        h j (Nat.le_of_not_gt hj)]

theorem coeff_extendFiniteCoefficients_eq {n : ℕ}
    (c : FiniteMultiIndex n → ℂ) (α : MultiIndex)
    (hα : ∀ j, n ≤ j → α j = 0) :
    MvPowerSeries.coeff α (extendFiniteCoefficients c) = c (fun j : Fin n => α j.val) := by
  obtain ⟨β, rfl⟩ := (mem_range_finiteIndexEmbedding_iff α).mpr hα
  simp

theorem embedFiniteCoefficients_sub {n : ℕ} (c d : FiniteMultiIndex n → ℂ)
    (hc : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) c))
    (hd : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) d))
    (hcd : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) (fun α => c α - d α))) :
    embedFiniteCoefficients (fun α => c α - d α) hcd =
      embedFiniteCoefficients c hc - embedFiniteCoefficients d hd := by
  ext α
  by_cases hα : α ∈ Set.range (finiteIndexEmbedding n)
  · obtain ⟨β, rfl⟩ := hα
    simp [coeff, embedFiniteCoefficients]
  · simp [coeff, embedFiniteCoefficients, coeff_extendFiniteCoefficients_outside _ hα]

/-- Adding an unused final variable leaves only exponent zero in that variable. -/
def liftFiniteCoefficients {n : ℕ} (c : FiniteMultiIndex n → ℂ)
    (β : FiniteMultiIndex (n + 1)) : ℂ :=
  if β (Fin.last n) = 0 then c (fun j => β j.castSucc) else 0

theorem coeff_extendFiniteCoefficients_succ {n : ℕ}
    (c : FiniteMultiIndex n → ℂ) (β : FiniteMultiIndex (n + 1)) :
    MvPowerSeries.coeff (finiteIndexEmbedding (n + 1) β) (extendFiniteCoefficients c) =
      liftFiniteCoefficients c β := by
  by_cases hlast : β (Fin.last n) = 0
  · have hzero : ∀ j, n ≤ j → finiteIndexEmbedding (n + 1) β j = 0 := by
      intro j hj
      by_cases hj' : j = n
      · subst j
        exact (finiteIndexEmbedding_apply β (Fin.last n)).trans hlast
      · exact finiteIndexEmbedding_apply_of_ge β (by omega)
    rw [coeff_extendFiniteCoefficients_eq c _ hzero]
    simp only [liftFiniteCoefficients, hlast, ↓reduceIte]
    congr 1
    funext j
    exact finiteIndexEmbedding_apply β j.castSucc
  · have hnot : finiteIndexEmbedding (n + 1) β ∉ Set.range (finiteIndexEmbedding n) := by
      intro h
      have hz := (mem_range_finiteIndexEmbedding_iff _).mp h n le_rfl
      exact hlast ((finiteIndexEmbedding_apply β (Fin.last n)).symm.trans hz)
    simp [coeff_extendFiniteCoefficients_outside c hnot, liftFiniteCoefficients, hlast]

theorem extendFiniteCoefficients_lift {n : ℕ} (c : FiniteMultiIndex n → ℂ) :
    extendFiniteCoefficients (liftFiniteCoefficients c) = extendFiniteCoefficients c := by
  apply MvPowerSeries.ext
  intro α
  by_cases hα : α ∈ Set.range (finiteIndexEmbedding (n + 1))
  · obtain ⟨β, rfl⟩ := hα
    rw [coeff_extendFiniteCoefficients, coeff_extendFiniteCoefficients_succ]
  · have hnot : α ∉ Set.range (finiteIndexEmbedding n) := by
      intro h
      apply hα
      apply (mem_range_finiteIndexEmbedding_iff α).mpr
      intro j hj
      exact (mem_range_finiteIndexEmbedding_iff α).mp h j (by omega)
    rw [coeff_extendFiniteCoefficients_outside _ hα,
      coeff_extendFiniteCoefficients_outside _ hnot]

theorem embedFiniteCoefficients_lift {n : ℕ} (c : FiniteMultiIndex n → ℂ)
    (hc : ∀ r : ℕ, 0 < r → Summable (finiteWeightedTerm (r : ℝ) c))
    (hlift : ∀ r : ℕ, 0 < r →
      Summable (finiteWeightedTerm (r : ℝ) (liftFiniteCoefficients c))) :
    embedFiniteCoefficients (liftFiniteCoefficients c) hlift = embedFiniteCoefficients c hc := by
  exact Subtype.ext (extendFiniteCoefficients_lift c)

end AutomaticContinuity
