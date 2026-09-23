import AutomaticContinuity.HomogeneousCoefficientBasis
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

/-! # Fixed linear-form powers span the actual homogeneous polynomials -/

noncomputable section

namespace AutomaticContinuity.HomogeneousPowerBasis

open MvPolynomial
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 2) ℂ

def linearForm (s : ℂ) : Poly := X 0 + C s * X 1

def monomialAt (m : ℕ) (k : Fin (m + 1)) : Poly :=
  X 0 ^ (m - k.val) * X 1 ^ k.val

theorem linearForm_pow (s : ℂ) (m : ℕ) :
    linearForm s ^ m = ∑ k : Fin (m + 1),
      ((m.choose k.val : ℂ) * s ^ k.val) • monomialAt m k := by
  rw [linearForm, add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [monomialAt, smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow]
  ring

theorem exists_expansion_of_array (m : ℕ) (a : Fin (m + 1) → ℂ) :
    ∃ b : Fin (m + 1) → ℂ,
      ∑ k, a k • monomialAt m k = ∑ j, b j • linearForm (j.val : ℂ) ^ m := by
  obtain ⟨b, hb, _⟩ := HomogeneousCoefficientBasis.existsUnique_coefficients m a
  refine ⟨b, ?_⟩
  symm
  simp_rw [linearForm_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul]
  congr 1
  rw [hb k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem monomialAt_mem_span (m : ℕ) (k : Fin (m + 1)) :
    monomialAt m k ∈ Submodule.span ℂ
      (Set.range (fun j : Fin (m + 1) => linearForm (j.val : ℂ) ^ m)) := by
  classical
  obtain ⟨b, hb⟩ := exists_expansion_of_array m (Pi.single k 1)
  have heq : monomialAt m k = ∑ j, b j • linearForm (j.val : ℂ) ^ m := by
    simpa using hb
  rw [heq]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, rfl⟩)

theorem homogeneous_mem_span {m : ℕ} {p : Poly} (hp : p.IsHomogeneous m) :
    p ∈ Submodule.span ℂ
      (Set.range (fun j : Fin (m + 1) => linearForm (j.val : ℂ) ^ m)) := by
  change p ∈ homogeneousSubmodule (Fin 2) ℂ m at hp
  rw [homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hp
  apply (Submodule.span_le.mpr ?_) hp
  rintro _ ⟨d, hd, rfl⟩
  change d.degree = m at hd
  have hdeg : d 0 + d 1 = m := by
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hd
  let k : Fin (m + 1) := ⟨d 1, by omega⟩
  have hx : m - k.val = d 0 := by dsimp [k]; omega
  have heq : (monomial d (1 : ℂ) : Poly) = monomialAt m k := by
    rw [monomial_fin_two]
    simp only [map_one, one_mul, monomialAt, hx]
    rfl
  change (monomial d 1 : Poly) ∈ _
  rw [heq]
  exact monomialAt_mem_span m k

/-- An actual homogeneous polynomial is a finite linear combination of
fixed powers. The slopes depend only on the degree. -/
theorem exists_expansion {m : ℕ} {p : Poly} (hp : p.IsHomogeneous m) :
    ∃ b : Fin (m + 1) → ℂ, p = ∑ j, b j • linearForm (j.val : ℂ) ^ m := by
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (homogeneous_mem_span hp)
  exact ⟨b, hb.symm⟩

theorem linearForm_homogeneous (s : ℂ) : (linearForm s).IsHomogeneous 1 :=
  (isHomogeneous_X ℂ 0).add ((isHomogeneous_X ℂ 1).C_mul s)

theorem linearForm_pow_homogeneous (s : ℂ) (m : ℕ) :
    (linearForm s ^ m).IsHomogeneous m := by
  simpa only [one_mul] using (linearForm_homogeneous s).pow m

end AutomaticContinuity.HomogeneousPowerBasis
