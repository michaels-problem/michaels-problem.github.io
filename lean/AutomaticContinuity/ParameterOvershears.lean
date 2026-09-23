import AutomaticContinuity.PolynomialShears
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

/-!
# Parameter-dependent complete complex overshears

Explicit complete flows for compact-family constructions.
The flow fixes the parameter and first fibre coordinate, has inverse at
negative time, and is jointly holomorphic when its coefficient is entire.
No automorphism approximation theorem is assumed or asserted.
-/

noncomputable section

namespace AutomaticContinuity.ParameterOvershears

variable {P : Type*}

def flow (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) : P × (ℂ × ℂ) :=
  (z.1, z.2.1, Complex.exp (t * f (z.1, z.2.1)) * z.2.2)

@[simp] theorem flow_zero (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) :
    flow f 0 z = z := by
  simp [flow]

theorem flow_add (f : P × ℂ → ℂ) (s t : ℂ) (z : P × (ℂ × ℂ)) :
    flow f (s + t) z = flow f s (flow f t z) := by
  simp [flow, add_mul, Complex.exp_add, mul_assoc]

@[simp] theorem flow_neg_flow (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) :
    flow f (-t) (flow f t z) = z := by
  rw [← flow_add, neg_add_cancel, flow_zero]

@[simp] theorem flow_flow_neg (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) :
    flow f t (flow f (-t) z) = z := by
  rw [← flow_add, add_neg_cancel, flow_zero]

@[simp] theorem flow_parameter (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) :
    (flow f t z).1 = z.1 := rfl

@[simp] theorem flow_first_fiber (f : P × ℂ → ℂ) (t : ℂ) (z : P × (ℂ × ℂ)) :
    (flow f t z).2.1 = z.2.1 := rfl

/-- The entire coordinate hyperplane is fixed, so in particular every fibre
origin is fixed. No regularity of the coefficient is needed for this identity. -/
@[simp] theorem flow_fixed_hyperplane (f : P × ℂ → ℂ) (t : ℂ) (p : P) (x : ℂ) :
    flow f t (p, x, 0) = (p, x, 0) := by
  simp [flow]

def equiv (f : P × ℂ → ℂ) (t : ℂ) : (P × (ℂ × ℂ)) ≃ (P × (ℂ × ℂ)) where
  toFun := flow f t
  invFun := flow f (-t)
  left_inv := flow_neg_flow f t
  right_inv := flow_flow_neg f t

section Continuous

variable [TopologicalSpace P]

/-- Joint continuity only needs a topological parameter space, so the base
may be an open-domain subtype without an inherited vector-space structure. -/
theorem continuous_joint_flow (f : P × ℂ → ℂ) (hf : Continuous f) :
    Continuous (fun z : ℂ × (P × (ℂ × ℂ)) => flow f z.1 z.2) := by
  unfold flow
  fun_prop

theorem continuous_flow (f : P × ℂ → ℂ) (hf : Continuous f) (t : ℂ) :
    Continuous (flow f t) :=
  (continuous_joint_flow f hf).comp (continuous_const.prodMk continuous_id)

def continuousHomeomorph (f : P × ℂ → ℂ) (hf : Continuous f) (t : ℂ) :
    (P × (ℂ × ℂ)) ≃ₜ (P × (ℂ × ℂ)) where
  toEquiv := equiv f t
  continuous_toFun := continuous_flow f hf t
  continuous_invFun := continuous_flow f hf (-t)

end Continuous

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Holomorphy is joint in complex time, all base parameters, and both fibre
variables. The base is an arbitrary complex normed space. -/
theorem differentiable_joint_flow (f : P × ℂ → ℂ) (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z : ℂ × (P × (ℂ × ℂ)) => flow f z.1 z.2) := by
  unfold flow
  fun_prop

theorem differentiable_flow (f : P × ℂ → ℂ) (hf : Differentiable ℂ f) (t : ℂ) :
    Differentiable ℂ (flow f t) := by
  exact (differentiable_joint_flow f hf).comp
    ((differentiable_const t).prodMk differentiable_id)

def homeomorph (f : P × ℂ → ℂ) (hf : Differentiable ℂ f) (t : ℂ) :
    (P × (ℂ × ℂ)) ≃ₜ (P × (ℂ × ℂ)) :=
  continuousHomeomorph f hf.continuous t

theorem differentiable_homeomorph (f : P × ℂ → ℂ) (hf : Differentiable ℂ f) (t : ℂ) :
    Differentiable ℂ (homeomorph f hf t) := differentiable_flow f hf t

theorem differentiable_homeomorph_symm (f : P × ℂ → ℂ)
    (hf : Differentiable ℂ f) (t : ℂ) :
    Differentiable ℂ (homeomorph f hf t).symm := differentiable_flow f hf (-t)

def vectorField (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) : P × (ℂ × ℂ) :=
  (0, 0, f (z.1, z.2.1) * z.2.2)

/-- The displayed maps solve the vector-field equation for all complex times.
The coefficient is constant along each trajectory, so no regularity assumption
on it is required for the time derivative. -/
theorem hasDerivAt_flow (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) (t : ℂ) :
    HasDerivAt (fun s : ℂ => flow f s z) (vectorField f (flow f t z)) t := by
  have he := (((hasDerivAt_id t).mul_const (f (z.1, z.2.1))).cexp).mul_const z.2.2
  simpa only [flow, vectorField, id_eq, one_mul, mul_assoc, mul_comm, mul_left_comm] using!
    (hasDerivAt_const t z.1).prodMk ((hasDerivAt_const t z.2.1).prodMk he)

theorem hasDerivAt_flow_zero (f : P × ℂ → ℂ) (z : P × (ℂ × ℂ)) :
    HasDerivAt (fun s : ℂ => flow f s z) (vectorField f z) 0 := by
  simpa only [flow_zero] using hasDerivAt_flow f z 0

end AutomaticContinuity.ParameterOvershears

