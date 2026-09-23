import AutomaticContinuity.DirectionalCompleteFlows

set_option autoImplicit false

/-!
# Origin-fixing directional factors

A tagged factor packages the explicit complete maps. The shear exponent is
the constructor index plus one, ensuring that every packaged factor fixes
the fibre origin. Overshears allow every nonnegative exponent.
-/

noncomputable section

namespace AutomaticContinuity.DirectionalFactors

open DirectionalCompleteFlows

inductive Factor where
  | shear (s : ℂ) (m : ℕ)
  | overshear (s : ℂ) (m : ℕ)

def Factor.field : Factor → ℂ → Pair → Pair
  | .shear s m => shearField s (m + 1)
  | .overshear s m => overshearField s m

def Factor.homeomorph : Factor → ℂ → ℂ → Pair ≃ₜ Pair
  | .shear s m => shearHomeomorph s (m + 1)
  | .overshear s m => overshearHomeomorph s m

@[simp] theorem Factor.homeomorph_zero_time (d : Factor) (c : ℂ) (w : Pair) :
    d.homeomorph c 0 w = w := by
  cases d <;> simp [Factor.homeomorph, shearHomeomorph, overshearHomeomorph]

@[simp] theorem Factor.homeomorph_origin (d : Factor) (c t : ℂ) :
    d.homeomorph c t 0 = 0 := by
  cases d <;> simp [Factor.homeomorph, shearHomeomorph, overshearHomeomorph,
    shearFlow_origin _ (Nat.succ_le_succ (Nat.zero_le _))]

theorem Factor.homeomorph_symm_apply (d : Factor) (c t : ℂ) (w : Pair) :
    (d.homeomorph c t).symm w = d.homeomorph c (-t) w := by cases d <;> rfl

theorem Factor.differentiable_joint (d : Factor) :
    Differentiable ℂ (fun z : ℂ × (ℂ × Pair) => d.homeomorph z.1 z.2.1 z.2.2) := by
  cases d with
  | shear s m => exact differentiable_joint_shearFlow s (m + 1)
  | overshear s m => exact differentiable_joint_overshearFlow s m

theorem Factor.differentiable_time_state (d : Factor) (c : ℂ) :
    Differentiable ℂ (fun z : ℂ × Pair => d.homeomorph c z.1 z.2) :=
  d.differentiable_joint.comp ((differentiable_const c).prodMk differentiable_id)

theorem Factor.differentiable_time_state_symm (d : Factor) (c : ℂ) :
    Differentiable ℂ (fun z : ℂ × Pair => (d.homeomorph c z.1).symm z.2) := by
  simp only [Factor.homeomorph_symm_apply]
  exact (d.differentiable_time_state c).comp
    (differentiable_fst.neg.prodMk differentiable_snd)

theorem Factor.hasDerivAt_zero (d : Factor) (c : ℂ) (w : Pair) :
    HasDerivAt (fun t : ℂ => d.homeomorph c t w) (d.field c w) 0 := by
  cases d with
  | shear s m => simpa only [shearFlow_zero_time] using! hasDerivAt_shearFlow s (m + 1) c 0 w
  | overshear s m => simpa only [overshearFlow_zero_time] using! hasDerivAt_overshearFlow s m c 0 w

theorem Factor.differentiable_field (d : Factor) :
    Differentiable ℂ (fun z : ℂ × Pair => d.field z.1 z.2) := by
  cases d <;> unfold Factor.field shearField overshearField linearForm <;> fun_prop

section Parameters

variable {P : Type*} [TopologicalSpace P]

theorem Factor.continuous_joint (d : Factor) (c : P → ℂ) (hc : Continuous c) :
    Continuous (fun z : ℂ × (P × Pair) => d.homeomorph (c z.2.1) z.1 z.2.2) :=
  d.differentiable_joint.continuous.comp
    ((hc.comp continuous_snd.fst).prodMk (continuous_fst.prodMk continuous_snd.snd))

theorem Factor.continuous_joint_symm (d : Factor) (c : P → ℂ) (hc : Continuous c) :
    Continuous (fun z : ℂ × (P × Pair) => (d.homeomorph (c z.2.1) z.1).symm z.2.2) := by
  simp only [Factor.homeomorph_symm_apply]
  exact (d.continuous_joint c hc).comp (continuous_fst.neg.prodMk continuous_snd)

theorem Factor.continuous_field (d : Factor) (c : P → ℂ) (hc : Continuous c) :
    Continuous (fun z : P × Pair => d.field (c z.1) z.2) :=
  d.differentiable_field.continuous.comp ((hc.comp continuous_fst).prodMk continuous_snd)

end Parameters

section LocalParameters

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem Factor.differentiableOn_joint (d : Factor) (c : P → ℂ) {U : Set P}
    (hc : DifferentiableOn ℂ c U) :
    DifferentiableOn ℂ (fun z : ℂ × (P × Pair) => d.homeomorph (c z.2.1) z.1 z.2.2)
      {z | z.2.1 ∈ U} := by
  cases d with
  | shear s m => exact (differentiableOn_joint_parameterShearFlow s (m + 1) c hc).snd
  | overshear s m => exact (differentiableOn_joint_parameterOvershearFlow s m c hc).snd

theorem Factor.differentiableOn_joint_symm (d : Factor) (c : P → ℂ) {U : Set P}
    (hc : DifferentiableOn ℂ c U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => (d.homeomorph (c z.2.1) z.1).symm z.2.2)
      {z | z.2.1 ∈ U} := by
  simp only [Factor.homeomorph_symm_apply]
  exact (d.differentiableOn_joint c hc).comp
    ((differentiable_fst.neg.prodMk differentiable_snd).differentiableOn)
    (fun _ hz => hz)

end LocalParameters

end AutomaticContinuity.DirectionalFactors
