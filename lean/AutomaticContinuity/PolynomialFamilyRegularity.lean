import AutomaticContinuity.RadialPolynomialField
import AutomaticContinuity.PolynomialFieldArrays

set_option autoImplicit false

/-! # Coefficientwise regularity of actual polynomial families

Each product coefficient is a fixed finite convolution. Thus coefficientwise
continuity and holomorphy are preserved without assuming a topology on the
whole polynomial algebra, or even a common degree bound for these operations.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFamilyRegularity

open MvPolynomial RadialPolynomialField
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 2) ℂ

theorem rescale_monomial (s : ℂ) (d : Fin 2 →₀ ℕ) (c : ℂ) :
    rescale s (monomial d c) = monomial d (s ^ d.degree * c) := by
  rw [monomial_fin_two, monomial_fin_two]
  simp only [rescale, map_mul, map_pow, bind₁_C_right, bind₁_X_right,
    mul_pow, Finsupp.degree_eq_sum, Fin.sum_univ_two, pow_add]
  ring

theorem coeff_rescale (s : ℂ) (q : Poly) (d : Fin 2 →₀ ℕ) :
    (rescale s q).coeff d = s ^ d.degree * q.coeff d := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial a c =>
      rw [rescale_monomial]
      by_cases h : a = d
      · subst a
        simp only [coeff_monomial, ite_true]
      · simp [coeff_monomial, h]
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

def ContinuousCoefficientsOn {X : Type*} [TopologicalSpace X]
    (q : X → Poly) (U : Set X) : Prop :=
  ∀ d, ContinuousOn (fun x => (q x).coeff d) U

def HolomorphicCoefficientsOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (q : X → Poly) (U : Set X) : Prop :=
  ∀ d, DifferentiableOn ℂ (fun x => (q x).coeff d) U

namespace ContinuousCoefficientsOn

variable {X : Type*} [TopologicalSpace X] {U : Set X} {p q : X → Poly}

theorem const (q : Poly) : ContinuousCoefficientsOn (fun _ : X => q) U :=
  fun _ => continuousOn_const

theorem C {c : X → ℂ} (hc : ContinuousOn c U) :
    ContinuousCoefficientsOn (fun x => MvPolynomial.C (c x)) U := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs <;> first | exact hc | exact continuousOn_const

theorem add (hp : ContinuousCoefficientsOn p U) (hq : ContinuousCoefficientsOn q U) :
    ContinuousCoefficientsOn (fun x => p x + q x) U := by
  intro d
  simpa only [AddMonoidAlgebra.coeff_add, Pi.add_apply] using! (hp d).add (hq d)

theorem sub (hp : ContinuousCoefficientsOn p U) (hq : ContinuousCoefficientsOn q U) :
    ContinuousCoefficientsOn (fun x => p x - q x) U := by
  intro d
  simpa only [coeff_sub, Pi.sub_apply] using! (hp d).sub (hq d)

theorem mul (hp : ContinuousCoefficientsOn p U) (hq : ContinuousCoefficientsOn q U) :
    ContinuousCoefficientsOn (fun x => p x * q x) U := by
  classical
  intro d
  simp only [coeff_mul]
  exact continuousOn_finsetSum _ fun a _ => (hp a.1).mul (hq a.2)

theorem pow (hq : ContinuousCoefficientsOn q U) (m : ℕ) :
    ContinuousCoefficientsOn (fun x => q x ^ m) U := by
  induction m with
  | zero => simpa only [pow_zero] using const (U := U) (1 : Poly)
  | succ m ih => simpa only [pow_succ] using ih.mul hq

theorem rescale {s : X → ℂ} (hq : ContinuousCoefficientsOn q U)
    (hs : ContinuousOn s U) :
    ContinuousCoefficientsOn (fun x => RadialPolynomialField.rescale (s x) (q x)) U := by
  intro d
  simpa only [coeff_rescale, Pi.mul_apply, Pi.pow_apply] using! (hs.pow d.degree).mul (hq d)

theorem iterate (hq : ContinuousCoefficientsOn q U) (m : ℕ) :
    ContinuousCoefficientsOn (fun x => PolynomialCutoff.iterate (q x) m) U := by
  induction m with
  | zero => exact hq
  | succ m ih =>
      exact ((const (3 : Poly)).mul (ih.pow 2)).sub ((const (2 : Poly)).mul (ih.pow 3))

theorem fieldPolynomial {s rate : X → ℂ} (hq : ContinuousCoefficientsOn q U)
    (hs : ContinuousOn s U) (hr : ContinuousOn rate U) (m : ℕ) :
    ContinuousCoefficientsOn (fun x => (fieldPolynomial (q x) (s x) (rate x) m).1) U ∧
    ContinuousCoefficientsOn (fun x => (fieldPolynomial (q x) (s x) (rate x) m).2) U := by
  have hh := (C hr).mul ((hq.rescale hs).iterate m)
  exact ⟨hh.mul (const (MvPolynomial.X 0)), hh.mul (const (MvPolynomial.X 1))⟩

end ContinuousCoefficientsOn

namespace HolomorphicCoefficientsOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {U : Set X} {p q : X → Poly}

theorem const (q : Poly) : HolomorphicCoefficientsOn (fun _ : X => q) U :=
  fun d => differentiableOn_const (q.coeff d)

theorem C {c : X → ℂ} (hc : DifferentiableOn ℂ c U) :
    HolomorphicCoefficientsOn (fun x => MvPolynomial.C (c x)) U := by
  classical
  intro d
  simp only [coeff_C]
  split_ifs <;> first | exact hc | exact differentiableOn_const 0

theorem add (hp : HolomorphicCoefficientsOn p U) (hq : HolomorphicCoefficientsOn q U) :
    HolomorphicCoefficientsOn (fun x => p x + q x) U := by
  intro d
  simpa only [AddMonoidAlgebra.coeff_add, Pi.add_apply] using! (hp d).add (hq d)

theorem sub (hp : HolomorphicCoefficientsOn p U) (hq : HolomorphicCoefficientsOn q U) :
    HolomorphicCoefficientsOn (fun x => p x - q x) U := by
  intro d
  simpa only [coeff_sub, Pi.sub_apply] using! (hp d).sub (hq d)

theorem mul (hp : HolomorphicCoefficientsOn p U) (hq : HolomorphicCoefficientsOn q U) :
    HolomorphicCoefficientsOn (fun x => p x * q x) U := by
  classical
  intro d
  simp only [coeff_mul]
  apply DifferentiableOn.fun_sum
  intro a _
  exact (hp a.1).mul (hq a.2)

theorem pow (hq : HolomorphicCoefficientsOn q U) (m : ℕ) :
    HolomorphicCoefficientsOn (fun x => q x ^ m) U := by
  induction m with
  | zero => simpa only [pow_zero] using const (U := U) (1 : Poly)
  | succ m ih => simpa only [pow_succ] using ih.mul hq

theorem rescale {s : X → ℂ} (hq : HolomorphicCoefficientsOn q U)
    (hs : DifferentiableOn ℂ s U) :
    HolomorphicCoefficientsOn (fun x => RadialPolynomialField.rescale (s x) (q x)) U := by
  intro d
  simpa only [coeff_rescale, Pi.mul_apply, Pi.pow_apply] using! (hs.pow d.degree).mul (hq d)

theorem iterate (hq : HolomorphicCoefficientsOn q U) (m : ℕ) :
    HolomorphicCoefficientsOn (fun x => PolynomialCutoff.iterate (q x) m) U := by
  induction m with
  | zero => exact hq
  | succ m ih =>
      exact ((const (3 : Poly)).mul (ih.pow 2)).sub ((const (2 : Poly)).mul (ih.pow 3))

theorem fieldPolynomial {s rate : X → ℂ} (hq : HolomorphicCoefficientsOn q U)
    (hs : DifferentiableOn ℂ s U) (hr : DifferentiableOn ℂ rate U) (m : ℕ) :
    HolomorphicCoefficientsOn (fun x => (fieldPolynomial (q x) (s x) (rate x) m).1) U ∧
    HolomorphicCoefficientsOn (fun x => (fieldPolynomial (q x) (s x) (rate x) m).2) U := by
  have hh := (C hr).mul ((hq.rescale hs).iterate m)
  exact ⟨hh.mul (const (MvPolynomial.X 0)), hh.mul (const (MvPolynomial.X 1))⟩

end HolomorphicCoefficientsOn

end AutomaticContinuity.PolynomialFamilyRegularity
