import AutomaticContinuity.HomogeneousFieldCoefficientSelection
import AutomaticContinuity.PolynomialFieldDecomposition

set_option autoImplicit false

/-! # Canonical finite coefficient arrays for polynomial fields

The arrays are actual monomial coefficients, with a single prescribed degree
bound. Reconstruction requires precisely that bound and vanishing at zero.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFieldArrays

open MvPolynomial HomogeneousPowerBasis HomogeneousFieldCoefficientSelection
open scoped BigOperators

abbrev Arrays (N : ℕ) := (m : Fin N) → MonomialCoefficients m.val

def degreeExponent (d : ℕ) (k : Fin (d + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![d - k.val, k.val]

@[simp] theorem degreeExponent_zero (d : ℕ) (k : Fin (d + 1)) :
    degreeExponent d k 0 = d - k.val := by simp [degreeExponent]

@[simp] theorem degreeExponent_one (d : ℕ) (k : Fin (d + 1)) :
    degreeExponent d k 1 = k.val := by simp [degreeExponent]

@[simp] theorem degreeExponent_degree (d : ℕ) (k : Fin (d + 1)) :
    (degreeExponent d k).degree = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degreeExponent_zero, degreeExponent_one]
  omega

theorem degreeExponent_injective (d : ℕ) : Function.Injective (degreeExponent d) := by
  intro i j hij
  apply Fin.ext
  simpa only [degreeExponent_one] using congrArg (fun a : Fin 2 →₀ ℕ => a 1) hij

theorem monomialAt_eq_monomial (d : ℕ) (k : Fin (d + 1)) :
    monomialAt d k = monomial (degreeExponent d k) (1 : ℂ) := by
  rw [monomial_fin_two]
  simp [monomialAt]

theorem sum_coeff_monomialAt (d : ℕ) (P : Poly) :
    (∑ k : Fin (d + 1), P.coeff (degreeExponent d k) • monomialAt d k) =
      homogeneousComponent d P := by
  classical
  ext a
  simp only [coeff_sum, coeff_smul, monomialAt_eq_monomial, coeff_monomial,
    smul_eq_mul, coeff_homogeneousComponent]
  by_cases ha : a.degree = d
  · rw [ite_eq_left ha]
    have hdeg : a 0 + a 1 = d := by
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using ha
    let k : Fin (d + 1) := ⟨a 1, by omega⟩
    have hk : degreeExponent d k = a := by
      ext i
      fin_cases i
      · change d - a 1 = a 0
        omega
      · change a 1 = a 1
        rfl
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hj
      have hne : a ≠ degreeExponent d j := by
        intro h
        exact hj (degreeExponent_injective d (h.symm.trans hk.symm))
      simp [Ne.symm hne]
    · simp
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro k _
    have hne : a ≠ degreeExponent d k := by
      intro h
      exact ha (h ▸ degreeExponent_degree d k)
    simp [Ne.symm hne]

def exponent (m : ℕ) (k : Fin (m + 2)) : Fin 2 →₀ ℕ := degreeExponent (m + 1) k

def extract (N : ℕ) (P Q : Poly) : Arrays N := fun m =>
  (fun k => P.coeff (exponent m.val k), fun k => Q.coeff (exponent m.val k))

def polynomial (N : ℕ) (a : Arrays N) : Poly × Poly :=
  ∑ m : Fin N, ((∑ k, (a m).1 k • monomialAt (m.val + 1) k),
    ∑ k, (a m).2 k • monomialAt (m.val + 1) k)

theorem polynomial_extract (N : ℕ) (P Q : Poly)
    (hP : P.totalDegree ≤ N) (hQ : Q.totalDegree ≤ N)
    (hPzero : eval (0 : Fin 2 → ℂ) P = 0)
    (hQzero : eval (0 : Fin 2 → ℂ) Q = 0) :
    polynomial N (extract N P Q) = (P, Q) := by
  apply Prod.ext
  · simp only [polynomial, Prod.fst_sum, extract, exponent, sum_coeff_monomialAt]
    exact HomogeneousFieldDecomposition.sum_positive_homogeneousComponents N P hP
      (by simpa only [eval_zero, constantCoeff_eq] using hPzero)
  · simp only [polynomial, Prod.snd_sum, extract, exponent, sum_coeff_monomialAt]
    exact HomogeneousFieldDecomposition.sum_positive_homogeneousComponents N Q hQ
      (by simpa only [eval_zero, constantCoeff_eq] using hQzero)

theorem continuous_extract {X : Type*} [TopologicalSpace X] (N : ℕ)
    {P Q : X → Poly} (hP : ∀ a, Continuous (fun x => (P x).coeff a))
    (hQ : ∀ a, Continuous (fun x => (Q x).coeff a)) :
    Continuous (fun x => extract N (P x) (Q x)) := by
  apply continuous_pi
  intro m
  exact (continuous_pi fun k => hP _).prodMk (continuous_pi fun k => hQ _)

theorem continuousOn_extract {X : Type*} [TopologicalSpace X] (N : ℕ)
    {U : Set X} {P Q : X → Poly}
    (hP : ∀ a, ContinuousOn (fun x => (P x).coeff a) U)
    (hQ : ∀ a, ContinuousOn (fun x => (Q x).coeff a) U) :
    ContinuousOn (fun x => extract N (P x) (Q x)) U := by
  apply continuousOn_pi.mpr
  intro m
  exact (continuousOn_pi.mpr fun k => hP _).prodMk
    (continuousOn_pi.mpr fun k => hQ _)

theorem differentiableOn_extract {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (N : ℕ) {U : Set X} {P Q : X → Poly}
    (hP : ∀ a, DifferentiableOn ℂ (fun x => (P x).coeff a) U)
    (hQ : ∀ a, DifferentiableOn ℂ (fun x => (Q x).coeff a) U) :
    DifferentiableOn ℂ (fun x => extract N (P x) (Q x)) U := by
  apply differentiableOn_pi.mpr
  intro m
  exact (differentiableOn_pi.mpr fun k => hP _).prodMk
    (differentiableOn_pi.mpr fun k => hQ _)

end AutomaticContinuity.PolynomialFieldArrays
