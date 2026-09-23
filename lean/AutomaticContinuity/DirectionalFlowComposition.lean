import AutomaticContinuity.DirectionalFactors
import AutomaticContinuity.FiniteFlowHolomorphy
import AutomaticContinuity.CompactFlowTaylor

set_option autoImplicit false

/-!
# Finite products of complete directional flows

Every product is an actual automorphism fixing the origin. Its time derivative
is the sum of its prescribed fields. Compact families have a uniform first
order approximation, simultaneously for the product and its actual inverse.
The parameter space in this estimate may be any topological space.
-/

noncomputable section

namespace AutomaticContinuity.DirectionalFlowComposition

open DirectionalCompleteFlows DirectionalFactors
open scoped BigOperators

variable {P : Type*}

def product (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ) (p : P) (t : ℂ) : Pair ≃ₜ Pair :=
  FiniteFlowHolomorphy.compose (fun i => (d i).homeomorph (c i p) t) n

def fieldSum (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ) (z : P × Pair) : Pair :=
  ∑ i ∈ Finset.range n, (d i).field (c i z.1) z.2

@[simp] theorem product_zero_time (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (w : Pair) : product d c n p 0 w = w :=
  FiniteFlowHolomorphy.compose_at_zero (fun i t => (d i).homeomorph (c i p) t) n
    (fun i _ x => (d i).homeomorph_zero_time (c i p) x) w

@[simp] theorem product_symm_zero_time (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (w : Pair) : (product d c n p 0).symm w = w :=
  FiniteFlowHolomorphy.compose_symm_at_zero (fun i t => (d i).homeomorph (c i p) t) n
    (fun i _ x => (d i).homeomorph_zero_time (c i p) x) w

@[simp] theorem product_origin (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (t : ℂ) : product d c n p t 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (d n).homeomorph (c n p) t (product d c n p t 0) = 0
    rw [ih, Factor.homeomorph_origin]

@[simp] theorem product_symm_origin (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (t : ℂ) : (product d c n p t).symm 0 = 0 := by
  apply (product d c n p t).injective
  rw [Homeomorph.apply_symm_apply, product_origin]

theorem differentiable_time_state (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) :
    Differentiable ℂ (fun z : ℂ × Pair => product d c n p z.1 z.2) :=
  FiniteFlowHolomorphy.differentiable_compose _ n
    (fun i _ => (d i).differentiable_time_state (c i p))

theorem differentiable_time_state_symm (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) :
    Differentiable ℂ (fun z : ℂ × Pair => (product d c n p z.1).symm z.2) :=
  FiniteFlowHolomorphy.differentiable_compose_symm _ n
    (fun i _ => (d i).differentiable_time_state_symm (c i p))

theorem hasDerivAt_product_zero (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (w : Pair) :
    HasDerivAt (fun t : ℂ => product d c n p t w) (fieldSum d c n (p, w)) 0 :=
  FiniteFlowHolomorphy.hasDerivAt_compose_zero _ _ n
    (fun i _ => (d i).differentiable_time_state (c i p))
    (fun i _ x => (d i).homeomorph_zero_time (c i p) x)
    (fun i _ x => (d i).hasDerivAt_zero (c i p) x) w

theorem hasDerivAt_product_symm_zero (d : ℕ → Factor) (c : ℕ → P → ℂ)
    (n : ℕ) (p : P) (w : Pair) :
    HasDerivAt (fun t : ℂ => (product d c n p t).symm w) (-fieldSum d c n (p, w)) 0 :=
  FiniteFlowHolomorphy.hasDerivAt_compose_symm_zero _ _ n
    (fun i _ => (d i).differentiable_time_state (c i p))
    (fun i _ => (d i).differentiable_time_state_symm (c i p))
    (fun i _ x => (d i).homeomorph_zero_time (c i p) x)
    (fun i _ x => (d i).hasDerivAt_zero (c i p) x) w

section ContinuousParameters

variable [TopologicalSpace P]

theorem continuous_product (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    (hc : ∀ i < n, Continuous (c i)) :
    Continuous (fun z : ℂ × (P × Pair) => product d c n z.2.1 z.1 z.2.2) := by
  induction n with
  | zero => exact continuous_snd.snd
  | succ n ih =>
    exact ((d n).continuous_joint (c n) (hc n (Nat.lt_succ_self n))).comp
      (continuous_fst.prodMk (continuous_snd.fst.prodMk
        (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi)))))

theorem continuous_product_symm (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    (hc : ∀ i < n, Continuous (c i)) :
    Continuous (fun z : ℂ × (P × Pair) => (product d c n z.2.1 z.1).symm z.2.2) := by
  induction n with
  | zero => exact continuous_snd.snd
  | succ n ih =>
    exact (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))).comp
      (continuous_fst.prodMk (continuous_snd.fst.prodMk
        ((d n).continuous_joint_symm (c n) (hc n (Nat.lt_succ_self n)))))

theorem continuous_fieldSum (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    (hc : ∀ i < n, Continuous (c i)) : Continuous (fieldSum d c n) := by
  apply continuous_finsetSum
  intro i hi
  exact (d i).continuous_field (c i) (hc i (Finset.mem_range.mp hi))

/-- Both estimates use one common step bound. The inverse is the actual
reverse product, and the sign of its first-order term is negative. -/
theorem exists_uniform_first_order_step (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    (hc : ∀ i < n, Continuous (c i)) {K : Set (P × Pair)} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ K, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < τ →
      ‖product d c n z.1 t z.2 - z.2 - t • fieldSum d c n z‖ < η * ‖t‖ ∧
      ‖(product d c n z.1 t).symm z.2 - z.2 + t • fieldSum d c n z‖ < η * ‖t‖ := by
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
    (fun z : P × Pair => z.2) (fieldSum d c n) hK
    (continuous_product d c n hc).continuousOn continuous_snd.continuousOn
    (continuous_fieldSum d c n hc).continuousOn
    (fun z _ => product_zero_time d c n z.1 z.2)
    (fun z _ => (hh z).differentiableOn)
    (fun z _ => hasDerivAt_product_zero d c n z.1 z.2) hη
  obtain ⟨τ₂, hτ₂, hi⟩ := CompactFlowTaylor.exists_uniform_first_order_step
    (fun z : ℂ × (P × Pair) => (product d c n z.2.1 z.1).symm z.2.2)
    (fun z : P × Pair => z.2) (fun z => -fieldSum d c n z) hK
    (continuous_product_symm d c n hc).continuousOn continuous_snd.continuousOn
    (continuous_fieldSum d c n hc).neg.continuousOn
    (fun z _ => product_symm_zero_time d c n z.1 z.2)
    (fun z _ => (hhi z).differentiableOn)
    (fun z _ => hasDerivAt_product_symm_zero d c n z.1 z.2) hη
  refine ⟨min τ₁ τ₂, lt_min hτ₁ hτ₂, ?_⟩
  intro z hz t ht hτ
  refine ⟨hf z hz t ht (hτ.trans_le (min_le_left _ _)), ?_⟩
  simpa only [smul_neg, sub_neg_eq_add] using
    hi z hz t ht (hτ.trans_le (min_le_right _ _))

end ContinuousParameters

section LocalParameters

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The finite product is jointly holomorphic on the full fibres above the
given parameter domain; its coefficients need only be holomorphic there. -/
theorem differentiableOn_product (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    {U : Set P} (hc : ∀ i < n, DifferentiableOn ℂ (c i) U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => product d c n z.2.1 z.1 z.2.2) {z | z.2.1 ∈ U} := by
  induction n with
  | zero => exact differentiable_snd.snd.differentiableOn
  | succ n ih =>
    exact ((d n).differentiableOn_joint (c n) (hc n (Nat.lt_succ_self n))).comp
      (differentiable_fst.differentiableOn.prodMk
        (differentiable_snd.fst.differentiableOn.prodMk
          (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))))) (fun _ hz => hz)

theorem differentiableOn_product_symm (d : ℕ → Factor) (c : ℕ → P → ℂ) (n : ℕ)
    {U : Set P} (hc : ∀ i < n, DifferentiableOn ℂ (c i) U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => (product d c n z.2.1 z.1).symm z.2.2)
      {z | z.2.1 ∈ U} := by
  induction n with
  | zero => exact differentiable_snd.snd.differentiableOn
  | succ n ih =>
    exact (ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))).comp
      (differentiable_fst.differentiableOn.prodMk
        (differentiable_snd.fst.differentiableOn.prodMk
          ((d n).differentiableOn_joint_symm (c n) (hc n (Nat.lt_succ_self n)))))
      (fun _ hz => hz)

end LocalParameters

end AutomaticContinuity.DirectionalFlowComposition
