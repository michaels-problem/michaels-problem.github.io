import AutomaticContinuity.PolynomialFamilyRegularity

set_option autoImplicit false

/-!
# Centering a polynomial separator along a holomorphic section

Base variables are specialized to parameter-dependent constants and fibre
variables are translated by the section. The result is an actual polynomial
in the two fibre variables. Its degree is bounded by the degree of the fixed
separator, and local coefficient regularity follows from that of the base
coordinates and the section. The fibre-variable labels may be `Bool` or
`Fin 2`, via an explicit coordinate map.
-/

noncomputable section

namespace AutomaticContinuity.CenteredPolynomialFamily

open MvPolynomial PolynomialFamilyRegularity
open scoped BigOperators

variable {σ ι P : Type*}

def centered (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (p : P) : Poly :=
  eval₂Hom C (Sum.elim (fun i => C (b p i)) (fun i => X (j i) + C (h p i))) q

theorem eval_centered (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (p : P) (w : Fin 2 → ℂ) :
    eval w (centered q j b h p) =
      eval (Sum.elim (b p) (fun i => w (j i) + h p i)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [centered]
  | add q r hq hr => simpa [centered] using congrArg₂ (· + ·) hq hr
  | mul_X q i hq =>
    cases i with
    | inl i => simpa [centered] using congrArg (fun z => z * b p i) hq
    | inr i => simpa [centered] using congrArg (fun z => z * (w (j i) + h p i)) hq

/-- Substitution by affine polynomials cannot increase total degree. -/
theorem totalDegree_eval₂Hom_le {κ : Type*} (q : MvPolynomial κ ℂ)
    (v : κ → Poly) (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (eval₂Hom C v q).totalDegree ≤ q.totalDegree := by
  classical
  have heq : eval₂Hom C v q =
      ∑ d ∈ q.support, C (q.coeff d) * d.prod (fun i n => v i ^ n) := by
    conv_lhs => rw [q.as_sum, map_sum]
    simp only [eval₂Hom_monomial]
  rw [heq]
  apply totalDegree_finsetSum_le
  intro d hd
  calc
    (C (q.coeff d) * d.prod (fun i n => v i ^ n)).totalDegree ≤
        (d.prod (fun i n => v i ^ n)).totalDegree := by
      simpa only [totalDegree_C, zero_add] using
        totalDegree_mul (C (q.coeff d)) (d.prod (fun i n => v i ^ n))
    _ ≤ ∑ i ∈ d.support, (v i ^ d i).totalDegree :=
      totalDegree_finsetProd d.support (fun i => v i ^ d i)
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow (v i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _ ≤ q.totalDegree := le_totalDegree hd

theorem totalDegree_centered_le (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) (p : P) :
    (centered q j b h p).totalDegree ≤ q.totalDegree := by
  apply totalDegree_eval₂Hom_le
  intro i
  cases i with
  | inl i => simp
  | inr i => simpa only [Sum.elim_inr, totalDegree_X, totalDegree_C,
      max_eq_left (by omega : 0 ≤ 1)] using!
      totalDegree_add (X (j i) : Poly) (C (h p i))

section Continuous

variable [TopologicalSpace P]

theorem continuousCoefficientsOn_centered (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) {U : Set P}
    (hb : ∀ i, ContinuousOn (fun p => b p i) U)
    (hh : ∀ i, ContinuousOn (fun p => h p i) U) :
    ContinuousCoefficientsOn (centered q j b h) U := by
  change ContinuousCoefficientsOn (fun p => centered q j b h p) U
  induction q using MvPolynomial.induction_on with
  | C c => simpa only [centered, eval₂Hom_C] using ContinuousCoefficientsOn.const (U := U) (C c : Poly)
  | add q r hq hr => simpa only [centered, map_add] using hq.add hr
  | mul_X q i hq =>
    cases i with
    | inl i =>
      simpa only [centered, map_mul, eval₂Hom_X', Sum.elim_inl] using
        hq.mul (ContinuousCoefficientsOn.C (hb i))
    | inr i =>
      simpa only [centered, map_mul, eval₂Hom_X', Sum.elim_inr] using
        hq.mul ((ContinuousCoefficientsOn.const (X (j i))).add (ContinuousCoefficientsOn.C (hh i)))

end Continuous

section Holomorphic

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem holomorphicCoefficientsOn_centered (q : MvPolynomial (σ ⊕ ι) ℂ) (j : ι → Fin 2)
    (b : P → σ → ℂ) (h : P → ι → ℂ) {U : Set P}
    (hb : ∀ i, DifferentiableOn ℂ (fun p => b p i) U)
    (hh : ∀ i, DifferentiableOn ℂ (fun p => h p i) U) :
    HolomorphicCoefficientsOn (centered q j b h) U := by
  change HolomorphicCoefficientsOn (fun p => centered q j b h p) U
  induction q using MvPolynomial.induction_on with
  | C c => simpa only [centered, eval₂Hom_C] using HolomorphicCoefficientsOn.const (U := U) (C c : Poly)
  | add q r hq hr => simpa only [centered, map_add] using hq.add hr
  | mul_X q i hq =>
    cases i with
    | inl i =>
      simpa only [centered, map_mul, eval₂Hom_X', Sum.elim_inl] using
        hq.mul (HolomorphicCoefficientsOn.C (hb i))
    | inr i =>
      simpa only [centered, map_mul, eval₂Hom_X', Sum.elim_inr] using
        hq.mul ((HolomorphicCoefficientsOn.const (X (j i))).add (HolomorphicCoefficientsOn.C (hh i)))

end Holomorphic

end AutomaticContinuity.CenteredPolynomialFamily
