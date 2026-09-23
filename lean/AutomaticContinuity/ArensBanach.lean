import AutomaticContinuity.Bezout
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false

/-!
# Finite equations in complex Banach algebras

The maximal-ideal construction uses the standard resolvent/Liouville proof of
Gelfand–Mazur. The short argument is adapted from the inspected pinned Mathlib
`GelfandFormula.lean` so this project need not import its unrelated polynomial
spectral-mapping dependencies or the C⋆-algebra portions of `GelfandDuality.lean`.
-/

noncomputable section

namespace AutomaticContinuity.Arens

open scoped BigOperators
open scoped Topology

universe u v

variable {ι : Type u} [Fintype ι]
variable {A : Type v} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The resolvent cannot be entire and decay to zero at infinity. This is the
standard Liouville proof of nonemptiness of the Banach-algebra spectrum. -/
theorem spectrum_nonempty [Nontrivial A] (a : A) : (spectrum ℂ a).Nonempty := by
  by_contra! h
  have hres : resolventSet ℂ a = Set.univ := by
    rwa [spectrum, Set.compl_empty_iff] at h
  have hdiff : Differentiable ℂ (resolvent a : ℂ → A) := by
    intro z
    have hz : z ∈ resolventSet ℂ a := hres.symm ▸ Set.mem_univ z
    have hleft := hasFDerivAt_ringInverse (𝕜 := ℂ) hz.unit
    have hright : HasDerivAt (fun w : ℂ => algebraMap ℂ A w - a) 1 z := by
      simpa using! (Algebra.linearMap ℂ A).hasDerivAt.sub_const a
    exact (hleft.comp_hasDerivAt z hright).differentiableAt
  have hzero := hdiff.apply_eq_of_tendsto_cocompact 0 (by
    simpa [Metric.cobounded_eq_cocompact] using spectrum.resolvent_tendsto_cobounded a (𝕜 := ℂ))
  exact not_isUnit_zero (hzero ▸ (spectrum.isUnit_resolvent.mp (hres.symm ▸ Set.mem_univ 0)))

/-- Gelfand–Mazur for the complete normed division algebra underlying a maximal
quotient. Only submultiplicativity of the norm is required. -/
def banachDivisionAlgEquiv [Nontrivial A]
    (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) : ℂ ≃ₐ[ℂ] A :=
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (spectrum_nonempty a).some
    left_inv := fun z => by
      simpa only [spectrum.scalar_eq] using!
        (spectrum_nonempty (algebraMap ℂ A z)).some_mem
    right_inv := fun a => by
      have hm := (spectrum_nonempty a).some_mem
      rwa [spectrum.mem_iff, hA, Classical.not_not, sub_eq_zero] at hm }

/-- A maximal Banach ideal is the kernel of a continuous complex character. -/
theorem character_of_maximal (M : Ideal A) [Ideal.IsMaximal M] :
    ∃ η : A →ₐ[ℂ] ℂ, Continuous η ∧ ∀ a ∈ M, η a = 0 := by
  let e : ℂ ≃ₐ[ℂ] A ⧸ M := banachDivisionAlgEquiv
    (letI := Ideal.Quotient.field M; isUnit_iff_ne_zero (G₀ := A ⧸ M))
  let η : A →ₐ[ℂ] ℂ := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M)
  refine ⟨η, map_continuous η, ?_⟩
  intro a ha
  have hzero : Ideal.Quotient.mk M a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  change e.symm (Ideal.Quotient.mk M a) = 0
  rw [hzero, map_zero]

/-- The elementary Banach-algebra dichotomy behind finite interpolation. -/
theorem solution_or_character (a : ι → A) :
    Nonempty (Bezout.Solution a) ∨
      ∃ η : A →ₐ[ℂ] ℂ, Continuous η ∧ ∀ i, η (a i) = 0 := by
  classical
  let I : Ideal A := Ideal.span (Set.range a)
  by_cases hI : I = ⊤
  · left
    have h1 : (1 : A) ∈ Ideal.span (Set.range a) := by
      change (1 : A) ∈ I
      rw [hI]
      trivial
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
    exact ⟨⟨b, by simpa only [Bezout.pairing, mul_comm] using hb⟩⟩
  · right
    obtain ⟨M, hM, hIM⟩ := I.exists_le_maximal hI
    let : Ideal.IsMaximal M := hM
    obtain ⟨η, hη, hzero⟩ := character_of_maximal M
    exact ⟨η, hη, fun i => hzero _ (hIM (Ideal.subset_span (Set.mem_range_self i)))⟩

end AutomaticContinuity.Arens
