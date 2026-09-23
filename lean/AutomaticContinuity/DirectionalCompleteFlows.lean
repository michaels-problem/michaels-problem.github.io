import AutomaticContinuity.ParameterOvershears
import AutomaticContinuity.OvershearEulerBounds
import AutomaticContinuity.EuclideanPairRotations

set_option autoImplicit false

/-!
# Complete shears and overshears along fixed complex directions

The invariant linear form is `x + s*y` and its kernel direction is `(-s,1)`.
Every map and inverse below is explicit. No finite-composition approximation
or decomposition of general vector fields is assumed.
-/

noncomputable section

namespace AutomaticContinuity.DirectionalCompleteFlows

abbrev Pair := ℂ × ℂ

def linearForm (s : ℂ) (w : Pair) : ℂ := w.1 + s * w.2

def direction (s : ℂ) : Pair := (-s, 1)

def shearField (s : ℂ) (m : ℕ) (c : ℂ) (w : Pair) : Pair :=
  (c * linearForm s w ^ m) • direction s

def overshearField (s : ℂ) (m : ℕ) (c : ℂ) (w : Pair) : Pair :=
  (c * linearForm s w ^ m * w.2) • direction s

def shearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) : Pair :=
  w + (t * (c * linearForm s w ^ m)) • direction s

def overshearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) : Pair :=
  w + ((Complex.exp (t * (c * linearForm s w ^ m)) - 1) * w.2) • direction s

@[simp] theorem linearForm_add_direction (s a : ℂ) (w : Pair) :
    linearForm s (w + a • direction s) = linearForm s w := by
  simp only [linearForm, direction, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  ring

@[simp] theorem linearForm_shearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    linearForm s (shearFlow s m c t w) = linearForm s w :=
  linearForm_add_direction _ _ _

@[simp] theorem linearForm_overshearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    linearForm s (overshearFlow s m c t w) = linearForm s w :=
  linearForm_add_direction _ _ _

@[simp] theorem shearFlow_snd (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    (shearFlow s m c t w).2 = w.2 + t * (c * linearForm s w ^ m) := by
  simp [shearFlow, direction]

@[simp] theorem overshearFlow_snd (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    (overshearFlow s m c t w).2 = Complex.exp (t * (c * linearForm s w ^ m)) * w.2 := by
  simp [overshearFlow, direction, smul_eq_mul]
  ring

theorem pair_eq_of_linearForm_snd {s : ℂ} {v w : Pair}
    (hl : linearForm s v = linearForm s w) (hy : v.2 = w.2) : v = w := by
  apply Prod.ext _ hy
  dsimp [linearForm] at hl
  rw [hy] at hl
  exact add_right_cancel hl

@[simp] theorem shearFlow_zero_time (s : ℂ) (m : ℕ) (c : ℂ) (w : Pair) :
    shearFlow s m c 0 w = w := by simp [shearFlow]

@[simp] theorem overshearFlow_zero_time (s : ℂ) (m : ℕ) (c : ℂ) (w : Pair) :
    overshearFlow s m c 0 w = w := by simp [overshearFlow]

theorem shearFlow_add (s : ℂ) (m : ℕ) (c t u : ℂ) (w : Pair) :
    shearFlow s m c (t + u) w = shearFlow s m c t (shearFlow s m c u w) := by
  apply pair_eq_of_linearForm_snd (s := s)
  · simp only [linearForm_shearFlow]
  · simp only [shearFlow_snd, linearForm_shearFlow]
    ring

theorem overshearFlow_add (s : ℂ) (m : ℕ) (c t u : ℂ) (w : Pair) :
    overshearFlow s m c (t + u) w = overshearFlow s m c t (overshearFlow s m c u w) := by
  apply pair_eq_of_linearForm_snd (s := s)
  · simp only [linearForm_overshearFlow]
  · simp only [overshearFlow_snd, linearForm_overshearFlow, add_mul, Complex.exp_add,
      mul_assoc]

@[simp] theorem shearFlow_neg_flow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    shearFlow s m c (-t) (shearFlow s m c t w) = w := by
  rw [← shearFlow_add, neg_add_cancel, shearFlow_zero_time]

@[simp] theorem shearFlow_flow_neg (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    shearFlow s m c t (shearFlow s m c (-t) w) = w := by
  rw [← shearFlow_add, add_neg_cancel, shearFlow_zero_time]

@[simp] theorem overshearFlow_neg_flow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    overshearFlow s m c (-t) (overshearFlow s m c t w) = w := by
  rw [← overshearFlow_add, neg_add_cancel, overshearFlow_zero_time]

@[simp] theorem overshearFlow_flow_neg (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    overshearFlow s m c t (overshearFlow s m c (-t) w) = w := by
  rw [← overshearFlow_add, add_neg_cancel, overshearFlow_zero_time]

@[simp] theorem shearFlow_origin (s : ℂ) {m : ℕ} (hm : 1 ≤ m) (c t : ℂ) :
    shearFlow s m c t 0 = 0 := by
  simp [shearFlow, linearForm, zero_pow (by omega : m ≠ 0)]

@[simp] theorem overshearFlow_origin (s : ℂ) (m : ℕ) (c t : ℂ) :
    overshearFlow s m c t 0 = 0 := by simp [overshearFlow]

theorem differentiable_joint_shearFlow (s : ℂ) (m : ℕ) :
    Differentiable ℂ (fun z : ℂ × (ℂ × Pair) => shearFlow s m z.1 z.2.1 z.2.2) := by
  unfold shearFlow linearForm
  fun_prop

theorem differentiable_joint_overshearFlow (s : ℂ) (m : ℕ) :
    Differentiable ℂ (fun z : ℂ × (ℂ × Pair) => overshearFlow s m z.1 z.2.1 z.2.2) := by
  unfold overshearFlow linearForm
  fun_prop

theorem differentiable_shearFlow (s : ℂ) (m : ℕ) (c t : ℂ) :
    Differentiable ℂ (shearFlow s m c t) := by
  unfold shearFlow linearForm
  fun_prop

theorem differentiable_overshearFlow (s : ℂ) (m : ℕ) (c t : ℂ) :
    Differentiable ℂ (overshearFlow s m c t) := by
  unfold overshearFlow linearForm
  fun_prop

def shearHomeomorph (s : ℂ) (m : ℕ) (c t : ℂ) : Pair ≃ₜ Pair where
  toFun := shearFlow s m c t
  invFun := shearFlow s m c (-t)
  left_inv := shearFlow_neg_flow s m c t
  right_inv := shearFlow_flow_neg s m c t
  continuous_toFun := (differentiable_shearFlow s m c t).continuous
  continuous_invFun := (differentiable_shearFlow s m c (-t)).continuous

def overshearHomeomorph (s : ℂ) (m : ℕ) (c t : ℂ) : Pair ≃ₜ Pair where
  toFun := overshearFlow s m c t
  invFun := overshearFlow s m c (-t)
  left_inv := overshearFlow_neg_flow s m c t
  right_inv := overshearFlow_flow_neg s m c t
  continuous_toFun := (differentiable_overshearFlow s m c t).continuous
  continuous_invFun := (differentiable_overshearFlow s m c (-t)).continuous

theorem hasDerivAt_shearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    HasDerivAt (fun u : ℂ => shearFlow s m c u w)
      (shearField s m c (shearFlow s m c t w)) t := by
  have hd := ((hasDerivAt_id t).mul_const (c * linearForm s w ^ m)).smul_const (direction s)
  simpa only [shearFlow, shearField, linearForm_add_direction, id_eq, one_mul] using!
    hd.const_add w

theorem hasDerivAt_overshearFlow (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    HasDerivAt (fun u : ℂ => overshearFlow s m c u w)
      (overshearField s m c (overshearFlow s m c t w)) t := by
  have he := (((hasDerivAt_id t).mul_const (c * linearForm s w ^ m)).cexp).sub_const 1
  have hd := (he.mul_const w.2).smul_const (direction s)
  have hd' := hd.const_add w
  simp only [overshearField, linearForm_overshearFlow, overshearFlow_snd]
  simpa only [overshearFlow, id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using! hd'

section Parameters

variable {P : Type*}

def parameterShearFlow (s : ℂ) (m : ℕ) (c : P → ℂ) (t : ℂ) (z : P × Pair) :
    P × Pair := (z.1, shearFlow s m (c z.1) t z.2)

def parameterOvershearFlow (s : ℂ) (m : ℕ) (c : P → ℂ) (t : ℂ) (z : P × Pair) :
    P × Pair := (z.1, overshearFlow s m (c z.1) t z.2)

@[simp] theorem parameterShearFlow_parameter (s : ℂ) (m : ℕ) (c : P → ℂ)
    (t : ℂ) (z : P × Pair) : (parameterShearFlow s m c t z).1 = z.1 := rfl

@[simp] theorem parameterOvershearFlow_parameter (s : ℂ) (m : ℕ) (c : P → ℂ)
    (t : ℂ) (z : P × Pair) : (parameterOvershearFlow s m c t z).1 = z.1 := rfl

@[simp] theorem parameterShearFlow_zero (s : ℂ) (m : ℕ) (c : P → ℂ) (z : P × Pair) :
    parameterShearFlow s m c 0 z = z := by simp [parameterShearFlow]

@[simp] theorem parameterOvershearFlow_zero (s : ℂ) (m : ℕ) (c : P → ℂ)
    (z : P × Pair) : parameterOvershearFlow s m c 0 z = z := by
  simp [parameterOvershearFlow]

theorem parameterShearFlow_add (s : ℂ) (m : ℕ) (c : P → ℂ) (t u : ℂ) (z : P × Pair) :
    parameterShearFlow s m c (t + u) z =
      parameterShearFlow s m c t (parameterShearFlow s m c u z) := by
  simp only [parameterShearFlow, shearFlow_add]

theorem parameterOvershearFlow_add (s : ℂ) (m : ℕ) (c : P → ℂ)
    (t u : ℂ) (z : P × Pair) :
    parameterOvershearFlow s m c (t + u) z =
      parameterOvershearFlow s m c t (parameterOvershearFlow s m c u z) := by
  simp only [parameterOvershearFlow, overshearFlow_add]

@[simp] theorem parameterShearFlow_origin (s : ℂ) {m : ℕ} (hm : 1 ≤ m)
    (c : P → ℂ) (t : ℂ) (p : P) : parameterShearFlow s m c t (p, 0) = (p, 0) := by
  simp only [parameterShearFlow, shearFlow_origin s hm]

@[simp] theorem parameterOvershearFlow_origin (s : ℂ) (m : ℕ)
    (c : P → ℂ) (t : ℂ) (p : P) : parameterOvershearFlow s m c t (p, 0) = (p, 0) := by
  simp only [parameterOvershearFlow, overshearFlow_origin]

section Continuous

variable [TopologicalSpace P]

theorem continuous_joint_parameterShearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) :
    Continuous (fun z : ℂ × (P × Pair) => parameterShearFlow s m c z.1 z.2) := by
  unfold parameterShearFlow shearFlow linearForm
  fun_prop

theorem continuous_joint_parameterOvershearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) :
    Continuous (fun z : ℂ × (P × Pair) => parameterOvershearFlow s m c z.1 z.2) := by
  unfold parameterOvershearFlow overshearFlow linearForm
  fun_prop

theorem continuous_parameterShearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) (t : ℂ) : Continuous (parameterShearFlow s m c t) :=
  (continuous_joint_parameterShearFlow s m c hc).comp
    (continuous_const.prodMk continuous_id)

theorem continuous_parameterOvershearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) (t : ℂ) : Continuous (parameterOvershearFlow s m c t) :=
  (continuous_joint_parameterOvershearFlow s m c hc).comp
    (continuous_const.prodMk continuous_id)

/-- A topological parameter space may itself be an open-domain subtype. -/
def parameterShearHomeomorph (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) (t : ℂ) : (P × Pair) ≃ₜ (P × Pair) where
  toFun := parameterShearFlow s m c t
  invFun := parameterShearFlow s m c (-t)
  left_inv z := by simp [parameterShearFlow]
  right_inv z := by simp [parameterShearFlow]
  continuous_toFun := continuous_parameterShearFlow s m c hc t
  continuous_invFun := continuous_parameterShearFlow s m c hc (-t)

def parameterOvershearHomeomorph (s : ℂ) (m : ℕ) (c : P → ℂ)
    (hc : Continuous c) (t : ℂ) : (P × Pair) ≃ₜ (P × Pair) where
  toFun := parameterOvershearFlow s m c t
  invFun := parameterOvershearFlow s m c (-t)
  left_inv z := by simp [parameterOvershearFlow]
  right_inv z := by simp [parameterOvershearFlow]
  continuous_toFun := continuous_parameterOvershearFlow s m c hc t
  continuous_invFun := continuous_parameterOvershearFlow s m c hc (-t)

end Continuous

section Holomorphic

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Local joint holomorphy on the entire fibre over the parameter domain.
The domain need not be open for this stronger within-set statement. -/
theorem differentiableOn_joint_parameterShearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    {U : Set P} (hc : DifferentiableOn ℂ c U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => parameterShearFlow s m c z.1 z.2)
      {z | z.2.1 ∈ U} := by
  have hbase : Differentiable ℂ (fun z : ℂ × (P × Pair) => z.2.1) :=
    differentiable_snd.fst
  have hcoef := hc.comp hbase.differentiableOn (fun _ hz => hz)
  have hrest : Differentiable ℂ (fun z : ℂ × (P × Pair) => (z.1, z.2.2)) :=
    differentiable_fst.prodMk differentiable_snd.snd
  have hdata := hcoef.prodMk hrest.differentiableOn
  exact hbase.differentiableOn.prodMk
    ((differentiable_joint_shearFlow s m).comp_differentiableOn hdata)

theorem differentiableOn_joint_parameterOvershearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    {U : Set P} (hc : DifferentiableOn ℂ c U) :
    DifferentiableOn ℂ
      (fun z : ℂ × (P × Pair) => parameterOvershearFlow s m c z.1 z.2)
      {z | z.2.1 ∈ U} := by
  have hbase : Differentiable ℂ (fun z : ℂ × (P × Pair) => z.2.1) :=
    differentiable_snd.fst
  have hcoef := hc.comp hbase.differentiableOn (fun _ hz => hz)
  have hrest : Differentiable ℂ (fun z : ℂ × (P × Pair) => (z.1, z.2.2)) :=
    differentiable_fst.prodMk differentiable_snd.snd
  have hdata := hcoef.prodMk hrest.differentiableOn
  exact hbase.differentiableOn.prodMk
    ((differentiable_joint_overshearFlow s m).comp_differentiableOn hdata)

theorem differentiableOn_parameterShearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    {U : Set P} (hc : DifferentiableOn ℂ c U) (t : ℂ) :
    DifferentiableOn ℂ (parameterShearFlow s m c t) {z | z.1 ∈ U} :=
  (differentiableOn_joint_parameterShearFlow s m c hc).comp
    (((differentiable_const t).prodMk differentiable_id).differentiableOn)
    (fun _ hz => hz)

theorem differentiableOn_parameterOvershearFlow (s : ℂ) (m : ℕ) (c : P → ℂ)
    {U : Set P} (hc : DifferentiableOn ℂ c U) (t : ℂ) :
    DifferentiableOn ℂ (parameterOvershearFlow s m c t) {z | z.1 ∈ U} :=
  (differentiableOn_joint_parameterOvershearFlow s m c hc).comp
    (((differentiable_const t).prodMk differentiable_id).differentiableOn)
    (fun _ hz => hz)

end Holomorphic
end Parameters

end AutomaticContinuity.DirectionalCompleteFlows
