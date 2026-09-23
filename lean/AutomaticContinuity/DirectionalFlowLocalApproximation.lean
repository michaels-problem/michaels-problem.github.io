import AutomaticContinuity.DirectionalFlowComposition

set_option autoImplicit false

/-!
# Compact first-order realization with local parameter coefficients

Coefficients are assumed continuous only on a specified parameter domain.
The compact set of base-point pairs lies over that domain. The resulting
maps are the explicit finite products already constructed, with their actual
inverses; no extension of a coefficient beyond the domain is required.
-/

noncomputable section

namespace AutomaticContinuity.DirectionalFlowComposition

open DirectionalCompleteFlows DirectionalFactors

variable {P : Type*} [TopologicalSpace P]

theorem continuousOn_factor (d : Factor) (c : P → ℂ) {U : Set P}
    (hc : ContinuousOn c U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => d.homeomorph (c z.2.1) z.1 z.2.2)
      {z | z.2.1 ∈ U} := by
  have hcoef : ContinuousOn (fun z : ℂ × (P × Pair) => c z.2.1)
      {z | z.2.1 ∈ U} :=
    hc.comp continuous_snd.fst.continuousOn (fun _ hz => hz)
  exact d.differentiable_joint.continuous.comp_continuousOn
    (hcoef.prodMk (continuous_fst.prodMk continuous_snd.snd).continuousOn)

theorem continuousOn_factor_symm (d : Factor) (c : P → ℂ) {U : Set P}
    (hc : ContinuousOn c U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => (d.homeomorph (c z.2.1) z.1).symm z.2.2)
      {z | z.2.1 ∈ U} := by
  simp only [Factor.homeomorph_symm_apply]
  exact (continuousOn_factor d c hc).comp
    (continuous_fst.neg.prodMk continuous_snd).continuousOn (fun _ hz => hz)

theorem continuousOn_product (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    {U : Set P} (hc : ∀ i < n, ContinuousOn (c i) U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => product d c n z.2.1 z.1 z.2.2)
      {z | z.2.1 ∈ U} := by
  induction n with
  | zero => exact continuous_snd.snd.continuousOn
  | succ n ih =>
    exact (continuousOn_factor (d n) (c n) (hc n (Nat.lt_succ_self n))).comp
      (continuous_fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk
        (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))))) (fun _ hz => hz)

theorem continuousOn_product_symm (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    {U : Set P} (hc : ∀ i < n, ContinuousOn (c i) U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => (product d c n z.2.1 z.1).symm z.2.2)
      {z | z.2.1 ∈ U} := by
  induction n with
  | zero => exact continuous_snd.snd.continuousOn
  | succ n ih =>
    exact (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))).comp
      (continuous_fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk
        (continuousOn_factor_symm (d n) (c n) (hc n (Nat.lt_succ_self n)))))
      (fun _ hz => hz)

theorem continuousOn_fieldSum (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    {U : Set P} (hc : ∀ i < n, ContinuousOn (c i) U) :
    ContinuousOn (fieldSum d c n) {z | z.1 ∈ U} := by
  apply continuousOn_finsetSum
  intro i hi
  have hcoef : ContinuousOn (fun z : P × Pair => c i z.1) {z | z.1 ∈ U} :=
    (hc i (Finset.mem_range.mp hi)).comp continuous_fst.continuousOn (fun _ hz => hz)
  exact (d i).differentiable_field.continuous.comp_continuousOn
    (hcoef.prodMk continuous_snd.continuousOn)

/-- Local coefficients, arbitrary compact families, and one common positive
step size for both the forward map and the actual inverse. -/
theorem exists_uniform_first_order_step_on
    (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ) {U : Set P}
    (hc : ∀ i < n, ContinuousOn (c i) U) {K : Set (P × Pair)} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, z.1 ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      ‖product d c n z.1 t z.2 - z.2 - t • fieldSum d c n z‖ < η * ‖t‖ ∧
      ‖(product d c n z.1 t).symm z.2 - z.2 + t • fieldSum d c n z‖ < η * ‖t‖ := by
  have hF := (continuousOn_product d c n hc).mono
    (show Metric.closedBall (0 : ℂ) 1 ×ˢ K ⊆ {z | z.2.1 ∈ U} from
      fun z hz => hKU z.2 hz.2)
  have hFi := (continuousOn_product_symm d c n hc).mono
    (show Metric.closedBall (0 : ℂ) 1 ×ˢ K ⊆ {z | z.2.1 ∈ U} from
      fun z hz => hKU z.2 hz.2)
  have hV := (continuousOn_fieldSum d c n hc).mono hKU
  have hh : ∀ z : P × Pair, Differentiable ℂ (fun t : ℂ => product d c n z.1 t z.2) := by
    intro z
    exact (differentiable_time_state d c n z.1).comp
      (differentiable_id.prodMk (differentiable_const z.2))
  have hhi : ∀ z : P × Pair,
      Differentiable ℂ (fun t : ℂ => (product d c n z.1 t).symm z.2) := by
    intro z
    exact (differentiable_time_state_symm d c n z.1).comp
      (differentiable_id.prodMk (differentiable_const z.2))
  obtain ⟨τ₁, hτ₁, hf⟩ := CompactFlowTaylor.exists_uniform_first_order_step
    (fun z : ℂ × (P × Pair) => product d c n z.2.1 z.1 z.2.2)
    (fun z : P × Pair => z.2) (fieldSum d c n) hK hF continuous_snd.continuousOn hV
    (fun z _ => product_zero_time d c n z.1 z.2)
    (fun z _ => (hh z).differentiableOn)
    (fun z _ => hasDerivAt_product_zero d c n z.1 z.2) hη
  obtain ⟨τ₂, hτ₂, hi⟩ := CompactFlowTaylor.exists_uniform_first_order_step
    (fun z : ℂ × (P × Pair) => (product d c n z.2.1 z.1).symm z.2.2)
    (fun z : P × Pair => z.2) (fun z => -fieldSum d c n z) hK hFi
    continuous_snd.continuousOn hV.neg
    (fun z _ => product_symm_zero_time d c n z.1 z.2)
    (fun z _ => (hhi z).differentiableOn)
    (fun z _ => hasDerivAt_product_symm_zero d c n z.1 z.2) hη
  refine ⟨min τ₁ τ₂, lt_min hτ₁ hτ₂, ?_⟩
  intro z hz t ht hτ
  refine ⟨hf z hz t ht (hτ.trans_le (min_le_left _ _)), ?_⟩
  simpa only [smul_neg, sub_neg_eq_add] using
    hi z hz t ht (hτ.trans_le (min_le_right _ _))

end AutomaticContinuity.DirectionalFlowComposition
