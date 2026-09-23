import AutomaticContinuity.FiniteFlowComposition
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

/-!
# Actual finite holomorphic flow compositions

Finite products retain actual inverses, joint holomorphy, and the sum of the
infinitesimal generators at time zero. The inverse generator is derived from
the inverse identities, rather than postulated for an unrelated map.
-/

noncomputable section

namespace AutomaticContinuity.FiniteFlowHolomorphy

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E]

def compose (e : ℕ → E ≃ₜ E) : ℕ → E ≃ₜ E
  | 0 => Homeomorph.refl E
  | n + 1 => (compose e n).trans (e n)

@[simp] theorem compose_zero (e : ℕ → E ≃ₜ E) : compose e 0 = Homeomorph.refl E := rfl

@[simp] theorem compose_succ_apply (e : ℕ → E ≃ₜ E) (n : ℕ) (x : E) :
    compose e (n + 1) x = e n (compose e n x) := rfl

/-- The actual inverse applies the inverse factors in the reversed order. -/
@[simp] theorem compose_succ_symm_apply (e : ℕ → E ≃ₜ E) (n : ℕ) (x : E) :
    (compose e (n + 1)).symm x = (compose e n).symm ((e n).symm x) := rfl

theorem compose_apply_eq_applyFactors (e : ℕ → E ≃ₜ E) (n : ℕ) (x : E) :
    compose e n x = FiniteFlowComposition.applyFactors (fun i => e i) n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [compose_succ_apply, FiniteFlowComposition.applyFactors_succ, ih]

variable [NormedSpace ℂ E]

/-- Chain rule at a parameter value where the outer map is the identity in
the state variable. -/
theorem hasDerivAt_parameter_comp {F : ℂ × E → E} {g : ℂ → E} {x v w : E}
    (hF : DifferentiableAt ℂ F (0, x)) (hF0 : ∀ y, F (0, y) = y)
    (hFt : HasDerivAt (fun t : ℂ => F (t, x)) v 0)
    (hg : HasDerivAt g w 0) (hg0 : g 0 = x) :
    HasDerivAt (fun t : ℂ => F (t, g t)) (v + w) 0 := by
  let A := fderiv ℂ F (0, x)
  have hA : HasFDerivAt F A (0, x) := hF.hasFDerivAt
  have ht : HasDerivAt (fun t : ℂ => (t, x)) ((1 : ℂ), (0 : E)) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
  have hAv : A (1, 0) = v := (hA.comp_hasDerivAt 0 ht).unique hFt
  have hs : HasDerivAt (fun t : ℂ => x + t • w) w 0 := by
    simpa only [zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℂ) x).add ((hasDerivAt_id (0 : ℂ)).smul_const w)
  have hp : HasDerivAt (fun t : ℂ => ((0 : ℂ), x + t • w)) ((0 : ℂ), w) 0 :=
    (hasDerivAt_const 0 (0 : ℂ)).prodMk hs
  have hAw : A (0, w) = w := by
    have hh := hA.comp_hasDerivAt_of_eq 0 hp (by simp)
    change HasDerivAt (fun t : ℂ => F (0, x + t • w)) (A (0, w)) 0 at hh
    have hh' : HasDerivAt (fun t : ℂ => x + t • w) (A (0, w)) 0 := by
      simpa only [Function.comp_apply, hF0] using hh
    exact hh'.unique hs
  have hpair := (hasDerivAt_id 0).prodMk hg
  have hh := hA.comp_hasDerivAt_of_eq 0 hpair (by simp [hg0])
  change HasDerivAt (fun t : ℂ => F (t, g t)) (A (1, w)) 0 at hh
  have hsum : A (1, w) = v + w := by
    rw [show ((1 : ℂ), w) = (1, 0) + (0, w) by simp, map_add, hAv, hAw]
  simpa only [Function.comp_apply, hsum] using hh

omit [NormedSpace ℂ E] in
theorem compose_at_zero (e : ℕ → ℂ → E ≃ₜ E) (n : ℕ)
    (hzero : ∀ i < n, ∀ x, e i 0 x = x) (x : E) :
    compose (fun i => e i 0) n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [compose_succ_apply, hzero n (Nat.lt_succ_self n), ih]
    exact fun i hi => hzero i (Nat.lt_succ_of_lt hi)

omit [NormedSpace ℂ E] in
theorem compose_symm_at_zero (e : ℕ → ℂ → E ≃ₜ E) (n : ℕ)
    (hzero : ∀ i < n, ∀ x, e i 0 x = x) (x : E) :
    (compose (fun i => e i 0) n).symm x = x := by
  apply (compose (fun i => e i 0) n).injective
  rw [Homeomorph.apply_symm_apply, compose_at_zero e n hzero]

theorem differentiable_compose (e : ℕ → ℂ → E ≃ₜ E) (n : ℕ)
    (he : ∀ i < n, Differentiable ℂ (fun z : ℂ × E => e i z.1 z.2)) :
    Differentiable ℂ (fun z : ℂ × E => compose (fun i => e i z.1) n z.2) := by
  induction n with
  | zero => exact differentiable_snd
  | succ n ih =>
    exact (he n (Nat.lt_succ_self n)).comp
      (differentiable_fst.prodMk (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))))

theorem differentiable_compose_symm (e : ℕ → ℂ → E ≃ₜ E) (n : ℕ)
    (he : ∀ i < n, Differentiable ℂ (fun z : ℂ × E => (e i z.1).symm z.2)) :
    Differentiable ℂ (fun z : ℂ × E => (compose (fun i => e i z.1) n).symm z.2) := by
  induction n with
  | zero => exact differentiable_snd
  | succ n ih =>
    exact (ih (fun i hi => he i (Nat.lt_succ_of_lt hi))).comp
      (differentiable_fst.prodMk (he n (Nat.lt_succ_self n)))

theorem hasDerivAt_compose_zero (e : ℕ → ℂ → E ≃ₜ E) (V : ℕ → E → E) (n : ℕ)
    (he : ∀ i < n, Differentiable ℂ (fun z : ℂ × E => e i z.1 z.2))
    (hzero : ∀ i < n, ∀ x, e i 0 x = x)
    (hder : ∀ i < n, ∀ x, HasDerivAt (fun t : ℂ => e i t x) (V i x) 0)
    (x : E) :
    HasDerivAt (fun t : ℂ => compose (fun i => e i t) n x)
      (∑ i ∈ Finset.range n, V i x) 0 := by
  induction n with
  | zero => simpa [compose] using hasDerivAt_const (0 : ℂ) x
  | succ n ih =>
    have hp := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
      (fun i hi => hzero i (Nat.lt_succ_of_lt hi))
      (fun i hi => hder i (Nat.lt_succ_of_lt hi))
    have hz := compose_at_zero e n (fun i hi => hzero i (Nat.lt_succ_of_lt hi)) x
    have hh := hasDerivAt_parameter_comp ((he n (Nat.lt_succ_self n)) (0, x))
      (hzero n (Nat.lt_succ_self n)) (hder n (Nat.lt_succ_self n) x) hp hz
    simpa only [compose_succ_apply, Finset.sum_range_succ, add_comm] using hh

/-- Inverse velocity follows from the actual inverse identities. -/
theorem hasDerivAt_inverse_zero (e : ℂ → E ≃ₜ E) (V : E → E)
    (he : Differentiable ℂ (fun z : ℂ × E => e z.1 z.2))
    (hei : Differentiable ℂ (fun z : ℂ × E => (e z.1).symm z.2))
    (hzero : ∀ x, e 0 x = x)
    (hder : ∀ x, HasDerivAt (fun t : ℂ => e t x) (V x) 0) (x : E) :
    HasDerivAt (fun t : ℂ => (e t).symm x) (-V x) 0 := by
  have hz : (e 0).symm x = x := by
    apply (e 0).injective
    rw [Homeomorph.apply_symm_apply, hzero]
  have hp := (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) x)
  have hgi := (hei (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hp
  change HasDerivAt (fun t : ℂ => (e t).symm x) _ 0 at hgi
  have hg : DifferentiableAt ℂ (fun t : ℂ => (e t).symm x) 0 := hgi.differentiableAt
  have hh := hasDerivAt_parameter_comp (he (0, x)) hzero (hder x) hg.hasDerivAt hz
  have hsum : V x + deriv (fun t : ℂ => (e t).symm x) 0 = 0 := by
    have hc : HasDerivAt (fun _ : ℂ => x)
        (V x + deriv (fun t : ℂ => (e t).symm x) 0) 0 := by
      simpa only [Homeomorph.apply_symm_apply] using hh
    exact hc.unique (hasDerivAt_const 0 x)
  have hv : deriv (fun t : ℂ => (e t).symm x) 0 = -V x := by
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hsum)
  simpa only [hv] using hg.hasDerivAt

/-- The derivative of the actual inverse finite product is minus the sum of
the forward generators. No inverse-generator hypothesis is required. -/
theorem hasDerivAt_compose_symm_zero (e : ℕ → ℂ → E ≃ₜ E) (V : ℕ → E → E) (n : ℕ)
    (he : ∀ i < n, Differentiable ℂ (fun z : ℂ × E => e i z.1 z.2))
    (hei : ∀ i < n, Differentiable ℂ (fun z : ℂ × E => (e i z.1).symm z.2))
    (hzero : ∀ i < n, ∀ x, e i 0 x = x)
    (hder : ∀ i < n, ∀ x, HasDerivAt (fun t : ℂ => e i t x) (V i x) 0)
    (x : E) :
    HasDerivAt (fun t : ℂ => (compose (fun i => e i t) n).symm x)
      (-(∑ i ∈ Finset.range n, V i x)) 0 := by
  exact hasDerivAt_inverse_zero (fun t => compose (fun i => e i t) n)
    (fun x => ∑ i ∈ Finset.range n, V i x)
    (differentiable_compose e n he) (differentiable_compose_symm e n hei)
    (compose_at_zero e n hzero) (hasDerivAt_compose_zero e V n he hzero hder) x

end AutomaticContinuity.FiniteFlowHolomorphy
