import AutomaticContinuity.PolynomialFieldFamily
import AutomaticContinuity.DirectionalFlowLocalApproximation

set_option autoImplicit false

/-!
# Actual automorphism realization of polynomial vector-field families

A bounded-degree fibre-polynomial vector field with zero constant term is
encoded by its finite homogeneous monomial arrays. A fixed linear change of
coefficients and a finite product of explicit complete factors realize its
first-order time expansion. The finite product is an actual automorphism,
with its actual inverse, but is not asserted to be the exact flow of the sum.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFieldRealization

open DirectionalCompleteFlows PolynomialFieldArrays PolynomialFieldFamily
open HomogeneousFieldDecomposition

variable {P : Type*}

def automorphism (N : ℕ) (a : P → Arrays N) (p : P) (t : ℂ) : Pair ≃ₜ Pair :=
  DirectionalFlowComposition.product (factor N)
    (fun i p => coefficient N i (a p)) (count N) p t

def field (N : ℕ) (a : P → Arrays N) (z : P × Pair) : Pair :=
  evaluation z.2 (polynomial N (a z.1))

@[simp] theorem automorphism_zero_time (N : ℕ) (a : P → Arrays N) (p : P) (w : Pair) :
    automorphism N a p 0 w = w := DirectionalFlowComposition.product_zero_time _ _ _ _ _

@[simp] theorem automorphism_symm_zero_time (N : ℕ) (a : P → Arrays N)
    (p : P) (w : Pair) : (automorphism N a p 0).symm w = w :=
  DirectionalFlowComposition.product_symm_zero_time _ _ _ _ _

@[simp] theorem automorphism_origin (N : ℕ) (a : P → Arrays N) (p : P) (t : ℂ) :
    automorphism N a p t 0 = 0 := DirectionalFlowComposition.product_origin _ _ _ _ _

@[simp] theorem automorphism_symm_origin (N : ℕ) (a : P → Arrays N) (p : P) (t : ℂ) :
    (automorphism N a p t).symm 0 = 0 :=
  DirectionalFlowComposition.product_symm_origin _ _ _ _ _

theorem differentiable_time_state (N : ℕ) (a : P → Arrays N) (p : P) :
    Differentiable ℂ (fun z : ℂ × Pair => automorphism N a p z.1 z.2) :=
  DirectionalFlowComposition.differentiable_time_state _ _ _ _

theorem differentiable_time_state_symm (N : ℕ) (a : P → Arrays N) (p : P) :
    Differentiable ℂ (fun z : ℂ × Pair => (automorphism N a p z.1).symm z.2) :=
  DirectionalFlowComposition.differentiable_time_state_symm _ _ _ _

theorem differentiable_automorphism (N : ℕ) (a : P → Arrays N) (p : P) (t : ℂ) :
    Differentiable ℂ (automorphism N a p t) :=
  (differentiable_time_state N a p).comp
    ((differentiable_const t).prodMk differentiable_id)

theorem differentiable_automorphism_symm (N : ℕ) (a : P → Arrays N) (p : P) (t : ℂ) :
    Differentiable ℂ (automorphism N a p t).symm :=
  (differentiable_time_state_symm N a p).comp
    ((differentiable_const t).prodMk differentiable_id)

theorem hasDerivAt_automorphism_zero (N : ℕ) (a : P → Arrays N) (p : P) (w : Pair) :
    HasDerivAt (fun t : ℂ => automorphism N a p t w) (field N a (p, w)) 0 := by
  simpa only [fieldSum_eq, field] using!
    DirectionalFlowComposition.hasDerivAt_product_zero (factor N)
      (fun i p => coefficient N i (a p)) (count N) p w

theorem hasDerivAt_automorphism_symm_zero (N : ℕ) (a : P → Arrays N) (p : P) (w : Pair) :
    HasDerivAt (fun t : ℂ => (automorphism N a p t).symm w) (-field N a (p, w)) 0 := by
  simpa only [fieldSum_eq, field] using!
    DirectionalFlowComposition.hasDerivAt_product_symm_zero (factor N)
      (fun i p => coefficient N i (a p)) (count N) p w

section ContinuousParameters

variable [TopologicalSpace P]

theorem continuousOn_joint_automorphism (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : ContinuousOn a U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => automorphism N a z.2.1 z.1 z.2.2)
      {z | z.2.1 ∈ U} :=
  DirectionalFlowComposition.continuousOn_product _ _ _
    (fun i _ => continuousOn_coefficient N i ha)

theorem continuousOn_joint_automorphism_symm (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : ContinuousOn a U) :
    ContinuousOn (fun z : ℂ × (P × Pair) => (automorphism N a z.2.1 z.1).symm z.2.2)
      {z | z.2.1 ∈ U} :=
  DirectionalFlowComposition.continuousOn_product_symm _ _ _
    (fun i _ => continuousOn_coefficient N i ha)

/-- An actual common first-order automorphism approximation on every compact
family, simultaneously forward and inverse. Auxiliary parameters may be real
or live in any other topological space. -/
theorem exists_uniform_first_order_step (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : ContinuousOn a U) {K : Set (P × Pair)} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, z.1 ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      ‖automorphism N a z.1 t z.2 - z.2 - t • field N a z‖ < η * ‖t‖ ∧
      ‖(automorphism N a z.1 t).symm z.2 - z.2 + t • field N a z‖ < η * ‖t‖ := by
  obtain ⟨τ, hτ, hb⟩ :=
    DirectionalFlowComposition.exists_uniform_first_order_step_on (factor N)
      (fun i p => coefficient N i (a p)) (count N)
      (fun i _ => continuousOn_coefficient N i ha) hK hKU hη
  refine ⟨τ, hτ, ?_⟩
  rintro ⟨p, w⟩ hz t ht htτ
  simpa only [fieldSum_eq, field] using! hb (p, w) hz t ht htτ

/-- The same common estimate in the actual Euclidean pair norm. -/
theorem exists_uniform_euclidean_first_order_step (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : ContinuousOn a U) {K : Set (P × Pair)} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, z.1 ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      euclideanPairNorm (automorphism N a z.1 t z.2 - z.2 - t • field N a z) < η * ‖t‖ ∧
      euclideanPairNorm ((automorphism N a z.1 t).symm z.2 - z.2 + t • field N a z) <
        η * ‖t‖ := by
  obtain ⟨τ, hτ, hb⟩ := exists_uniform_first_order_step N a ha hK hKU
    (half_pos hη)
  refine ⟨τ, hτ, ?_⟩
  intro z hz t ht htτ
  obtain ⟨hf, hi⟩ := hb z hz t ht htτ
  constructor
  · exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)
  · exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)

end ContinuousParameters

section LocalHolomorphicParameters

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_joint_automorphism (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : DifferentiableOn ℂ a U) :
    DifferentiableOn ℂ (fun z : ℂ × (P × Pair) => automorphism N a z.2.1 z.1 z.2.2)
      {z | z.2.1 ∈ U} :=
  DirectionalFlowComposition.differentiableOn_product _ _ _
    (fun i _ => differentiableOn_coefficient N i ha)

theorem differentiableOn_joint_automorphism_symm (N : ℕ) (a : P → Arrays N) {U : Set P}
    (ha : DifferentiableOn ℂ a U) :
    DifferentiableOn ℂ (fun z : ℂ × (P × Pair) => (automorphism N a z.2.1 z.1).symm z.2.2)
      {z | z.2.1 ∈ U} :=
  DirectionalFlowComposition.differentiableOn_product_symm _ _ _
    (fun i _ => differentiableOn_coefficient N i ha)

end LocalHolomorphicParameters

section ActualPolynomialFamilies

/-- Canonical realization of actual polynomial pairs. Only their finitely
many coefficients of positive degree at most `N` enter this map. -/
def polynomialAutomorphism (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly)
    (p : P) (t : ℂ) : Pair ≃ₜ Pair :=
  automorphism N (fun p => extract N (f p) (g p)) p t

@[simp] theorem polynomialAutomorphism_origin (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly)
    (p : P) (t : ℂ) : polynomialAutomorphism N f g p t 0 = 0 :=
  automorphism_origin _ _ _ _

theorem field_extract_eq (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) (p : P) (w : Pair)
    (hf : (f p).totalDegree ≤ N) (hg : (g p).totalDegree ≤ N)
    (hf0 : MvPolynomial.eval (0 : Fin 2 → ℂ) (f p) = 0)
    (hg0 : MvPolynomial.eval (0 : Fin 2 → ℂ) (g p) = 0) :
    field N (fun p => extract N (f p) (g p)) (p, w) = evaluation w (f p, g p) := by
  unfold field
  rw [polynomial_extract N (f p) (g p) hf hg hf0 hg0]

theorem hasDerivAt_polynomialAutomorphism_zero
    (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) (p : P) (w : Pair)
    (hf : (f p).totalDegree ≤ N) (hg : (g p).totalDegree ≤ N)
    (hf0 : MvPolynomial.eval (0 : Fin 2 → ℂ) (f p) = 0)
    (hg0 : MvPolynomial.eval (0 : Fin 2 → ℂ) (g p) = 0) :
    HasDerivAt (fun t : ℂ => polynomialAutomorphism N f g p t w)
      (evaluation w (f p, g p)) 0 := by
  simpa only [field_extract_eq N f g p w hf hg hf0 hg0] using!
    hasDerivAt_automorphism_zero N (fun p => extract N (f p) (g p)) p w

section Continuous

variable [TopologicalSpace P]

/-- Arbitrary bounded-degree polynomial families with zero constant term:
the approximation is by genuine entire automorphisms fixing zero. Local
coefficient continuity is sufficient even with auxiliary real parameters. -/
theorem exists_polynomial_uniform_first_order_step
    (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) {U : Set P}
    (hf : ∀ α, ContinuousOn (fun p => (f p).coeff α) U)
    (hg : ∀ α, ContinuousOn (fun p => (g p).coeff α) U)
    (hdegree : ∀ p ∈ U, (f p).totalDegree ≤ N ∧ (g p).totalDegree ≤ N)
    (hzero : ∀ p ∈ U, MvPolynomial.eval (0 : Fin 2 → ℂ) (f p) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → ℂ) (g p) = 0)
    {K : Set (P × Pair)} (hK : IsCompact K) (hKU : ∀ z ∈ K, z.1 ∈ U)
    {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      ‖polynomialAutomorphism N f g z.1 t z.2 - z.2 -
        t • evaluation z.2 (f z.1, g z.1)‖ < η * ‖t‖ ∧
      ‖(polynomialAutomorphism N f g z.1 t).symm z.2 - z.2 +
        t • evaluation z.2 (f z.1, g z.1)‖ < η * ‖t‖ := by
  obtain ⟨τ, hτ, hb⟩ := exists_uniform_first_order_step N
    (fun p => extract N (f p) (g p)) (continuousOn_extract N hf hg) hK hKU hη
  refine ⟨τ, hτ, ?_⟩
  intro z hz t ht htτ
  have hU := hKU z hz
  have he := field_extract_eq N f g z.1 z.2
    (hdegree z.1 hU).1 (hdegree z.1 hU).2 (hzero z.1 hU).1 (hzero z.1 hU).2
  simpa only [he] using! hb z hz t ht htτ

theorem exists_polynomial_uniform_euclidean_first_order_step
    (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) {U : Set P}
    (hf : ∀ α, ContinuousOn (fun p => (f p).coeff α) U)
    (hg : ∀ α, ContinuousOn (fun p => (g p).coeff α) U)
    (hdegree : ∀ p ∈ U, (f p).totalDegree ≤ N ∧ (g p).totalDegree ≤ N)
    (hzero : ∀ p ∈ U, MvPolynomial.eval (0 : Fin 2 → ℂ) (f p) = 0 ∧
      MvPolynomial.eval (0 : Fin 2 → ℂ) (g p) = 0)
    {K : Set (P × Pair)} (hK : IsCompact K) (hKU : ∀ z ∈ K, z.1 ∈ U)
    {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      euclideanPairNorm (polynomialAutomorphism N f g z.1 t z.2 - z.2 -
        t • evaluation z.2 (f z.1, g z.1)) < η * ‖t‖ ∧
      euclideanPairNorm ((polynomialAutomorphism N f g z.1 t).symm z.2 - z.2 +
        t • evaluation z.2 (f z.1, g z.1)) < η * ‖t‖ := by
  obtain ⟨τ, hτ, hb⟩ := exists_uniform_euclidean_first_order_step N
    (fun p => extract N (f p) (g p)) (continuousOn_extract N hf hg) hK hKU hη
  refine ⟨τ, hτ, ?_⟩
  intro z hz t ht htτ
  have hU := hKU z hz
  have he := field_extract_eq N f g z.1 z.2
    (hdegree z.1 hU).1 (hdegree z.1 hU).2 (hzero z.1 hU).1 (hzero z.1 hU).2
  simpa only [he] using! hb z hz t ht htτ

end Continuous

section Holomorphic

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_joint_polynomialAutomorphism
    (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) {U : Set P}
    (hf : ∀ α, DifferentiableOn ℂ (fun p => (f p).coeff α) U)
    (hg : ∀ α, DifferentiableOn ℂ (fun p => (g p).coeff α) U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => polynomialAutomorphism N f g z.2.1 z.1 z.2.2)
      {z | z.2.1 ∈ U} :=
  differentiableOn_joint_automorphism N _ (differentiableOn_extract N hf hg)

theorem differentiableOn_joint_polynomialAutomorphism_symm
    (N : ℕ) (f g : P → HomogeneousPowerBasis.Poly) {U : Set P}
    (hf : ∀ α, DifferentiableOn ℂ (fun p => (f p).coeff α) U)
    (hg : ∀ α, DifferentiableOn ℂ (fun p => (g p).coeff α) U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => (polynomialAutomorphism N f g z.2.1 z.1).symm z.2.2)
      {z | z.2.1 ∈ U} :=
  differentiableOn_joint_automorphism_symm N _ (differentiableOn_extract N hf hg)

end Holomorphic
end ActualPolynomialFamilies

end AutomaticContinuity.PolynomialFieldRealization
