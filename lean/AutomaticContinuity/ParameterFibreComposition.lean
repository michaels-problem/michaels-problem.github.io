import AutomaticContinuity.FiniteFlowHolomorphy

set_option autoImplicit false

/-! # Local regularity of finite products of fibre automorphisms -/

noncomputable section

namespace AutomaticContinuity.ParameterFibreComposition

variable {P E : Type*} [NormedAddCommGroup E]

def product (e : ℕ → P → E ≃ₜ E) (n : ℕ) (p : P) : E ≃ₜ E :=
  FiniteFlowHolomorphy.compose (fun i => e i p) n

theorem product_origin (e : ℕ → P → E ≃ₜ E) (n : ℕ) (p : P)
    (he : ∀ i < n, e i p 0 = 0) : product e n p 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change e n p (product e n p 0) = 0
    rw [ih (fun i hi => he i (Nat.lt_succ_of_lt hi)), he n (Nat.lt_succ_self n)]

theorem product_symm_origin (e : ℕ → P → E ≃ₜ E) (n : ℕ) (p : P)
    (he : ∀ i < n, e i p 0 = 0) : (product e n p).symm 0 = 0 := by
  apply (product e n p).injective
  rw [Homeomorph.apply_symm_apply, product_origin e n p he]

section Continuous

variable [TopologicalSpace P]

theorem continuousOn_product (e : ℕ → P → E ≃ₜ E) (n : ℕ) (U : Set P)
    (he : ∀ i < n, ContinuousOn (fun z : P × E => e i z.1 z.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun z : P × E => product e n z.1 z.2) (U ×ˢ Set.univ) := by
  induction n with
  | zero => exact continuous_snd.continuousOn
  | succ n ih =>
    exact (he n (Nat.lt_succ_self n)).comp
      (continuous_fst.continuousOn.prodMk (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))))
      (fun _ hz => ⟨hz.1, Set.mem_univ _⟩)

theorem continuousOn_product_symm (e : ℕ → P → E ≃ₜ E) (n : ℕ) (U : Set P)
    (he : ∀ i < n, ContinuousOn (fun z : P × E => (e i z.1).symm z.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun z : P × E => (product e n z.1).symm z.2) (U ×ˢ Set.univ) := by
  induction n with
  | zero => exact continuous_snd.continuousOn
  | succ n ih =>
    exact (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))).comp
      (continuous_fst.continuousOn.prodMk (he n (Nat.lt_succ_self n)))
      (fun _ hz => ⟨hz.1, Set.mem_univ _⟩)

end Continuous

section Holomorphic

variable [NormedSpace ℂ E] [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_product (e : ℕ → P → E ≃ₜ E) (n : ℕ) (U : Set P)
    (he : ∀ i < n,
      DifferentiableOn ℂ (fun z : P × E => e i z.1 z.2) (U ×ˢ Set.univ)) :
    DifferentiableOn ℂ (fun z : P × E => product e n z.1 z.2) (U ×ˢ Set.univ) := by
  induction n with
  | zero => exact differentiable_snd.differentiableOn
  | succ n ih =>
    exact (he n (Nat.lt_succ_self n)).comp
      (differentiable_fst.differentiableOn.prodMk
        (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))))
      (fun _ hz => ⟨hz.1, Set.mem_univ _⟩)

theorem differentiableOn_product_symm (e : ℕ → P → E ≃ₜ E) (n : ℕ) (U : Set P)
    (he : ∀ i < n,
      DifferentiableOn ℂ (fun z : P × E => (e i z.1).symm z.2) (U ×ˢ Set.univ)) :
    DifferentiableOn ℂ (fun z : P × E => (product e n z.1).symm z.2) (U ×ˢ Set.univ) := by
  induction n with
  | zero => exact differentiable_snd.differentiableOn
  | succ n ih =>
    exact (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))).comp
      (differentiable_fst.differentiableOn.prodMk (he n (Nat.lt_succ_self n)))
      (fun _ hz => ⟨hz.1, Set.mem_univ _⟩)

end Holomorphic

end AutomaticContinuity.ParameterFibreComposition
