import AutomaticContinuity.FlagCompactBasin
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# The actual neighbourhood family has invertible vertical derivative

The derivative is taken in the fibre variable. Invertibility is derived from
the actual left inverse identity and finite dimensionality; it is not an
additional geometric hypothesis.
-/

noncomputable section

namespace AutomaticContinuity.FlagDominatingFamily

open Set

section InverseDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A differentiable left inverse makes the derivative of a finite-dimensional
endomorphism invertible. -/
theorem bijective_fderiv_of_leftInverse (f g : E → E) (x : E)
    (hf : DifferentiableAt ℂ f (g x)) (hg : DifferentiableAt ℂ g x)
    (hleft : ∀ y, f (g y) = y) : Function.Bijective (fderiv ℂ g x) := by
  have hcomp := hf.hasFDerivAt.comp x hg.hasFDerivAt
  change HasFDerivAt (fun y => f (g y))
    ((fderiv ℂ f (g x)).comp (fderiv ℂ g x)) x at hcomp
  have hid : HasFDerivAt (fun y : E => y)
      ((fderiv ℂ f (g x)).comp (fderiv ℂ g x)) x := by
    simpa only [hleft] using hcomp
  have hmatrix := hid.unique (hasFDerivAt_id x)
  have hlin : Function.LeftInverse (fderiv ℂ f (g x)) (fderiv ℂ g x) := by
    intro v
    have he := congrArg (fun A : E →L[ℂ] E => A v) hmatrix
    exact he
  refine ⟨hlin.injective, ?_⟩
  exact (LinearMap.injective_iff_surjective (f := (fderiv ℂ g x).toLinearMap)).mp hlin.injective

theorem exists_equiv_fderiv_of_leftInverse (f g : E → E) (x : E)
    (hf : DifferentiableAt ℂ f (g x)) (hg : DifferentiableAt ℂ g x)
    (hleft : ∀ y, f (g y) = y) :
    ∃ A : E ≃L[ℂ] E, (A : E →L[ℂ] E) = fderiv ℂ g x := by
  let A := (LinearEquiv.ofBijective (fderiv ℂ g x).toLinearMap
    (bijective_fderiv_of_leftInverse f g x hf hg hleft)).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  ext v
  rfl

end InverseDerivative

section Vertical

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem vertical_differentiableAt (g : P × E → E) {B : Set P}
    (hB : IsOpen B) (hg : DifferentiableOn ℂ g (B ×ˢ univ)) {p : P} (hp : p ∈ B) :
    DifferentiableAt ℂ (fun w => g (p, w)) 0 := by
  have hgj := hg.differentiableAt ((hB.prod isOpen_univ).mem_nhds
    (show (p, (0 : E)) ∈ B ×ˢ univ from ⟨hp, mem_univ _⟩))
  exact hgj.comp 0 ((differentiable_const p).prodMk differentiable_id).differentiableAt

/-- Joint holomorphy on the open base and an actual left inverse imply
bijectivity of the vertical derivative at fibre zero. -/
theorem vertical_derivative_bijective (f g : P × E → E) {B : Set P}
    (hB : IsOpen B) (hg : DifferentiableOn ℂ g (B ×ˢ univ)) {p : P} (hp : p ∈ B)
    (hf : DifferentiableAt ℂ f (p, g (p, 0)))
    (hleft : ∀ w, f (p, g (p, w)) = w) :
    Function.Bijective (fderiv ℂ (fun w => g (p, w)) 0) := by
  have hfv : DifferentiableAt ℂ (fun w => f (p, w)) (g (p, 0)) :=
    hf.comp (g (p, 0)) ((differentiable_const p).prodMk differentiable_id).differentiableAt
  exact bijective_fderiv_of_leftInverse (fun w => f (p, w)) (fun w => g (p, w)) 0
    hfv (vertical_differentiableAt g hB hg hp) hleft

theorem vertical_derivative_equiv (f g : P × E → E) {B : Set P}
    (hB : IsOpen B) (hg : DifferentiableOn ℂ g (B ×ˢ univ)) {p : P} (hp : p ∈ B)
    (hf : DifferentiableAt ℂ f (p, g (p, 0)))
    (hleft : ∀ w, f (p, g (p, w)) = w) :
    ∃ A : E ≃L[ℂ] E, HasFDerivAt (fun w => g (p, w)) (A : E →L[ℂ] E) 0 := by
  have hfv : DifferentiableAt ℂ (fun w => f (p, w)) (g (p, 0)) :=
    hf.comp (g (p, 0)) ((differentiable_const p).prodMk differentiable_id).differentiableAt
  have hgv := vertical_differentiableAt g hB hg hp
  obtain ⟨A, hA⟩ := exists_equiv_fderiv_of_leftInverse
    (fun w => f (p, w)) (fun w => g (p, w)) 0 hfv hgv hleft
  exact ⟨A, hA.symm ▸ hgv.hasFDerivAt⟩

end Vertical

abbrev Pair := ℂ × ℂ

/-- The proved entire-fibre neighbourhood family is dominating at its zero
section, with an actual continuous linear equivalence as each derivative. -/
theorem exists_neighbourhood_dominating_family {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ U, (z, h z) ∈ FlagTotalSpace.totalSet n) :
    ∃ (B : Set (FinitePoint n)) (f g : FinitePoint n × Pair → Pair),
      IsOpen B ∧ polydisc n R ⊆ B ∧ B ⊆ U ∧
      DifferentiableOn ℂ g (B ×ˢ univ) ∧
      ∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0 ∧
        DifferentiableAt ℂ f (p, h p) ∧
        (∀ w : Pair, f (p, g (p, w)) = w) ∧
        Function.Injective (fun w : Pair => g (p, w)) ∧
        (∀ w : Pair, (p, g (p, w)) ∈ FlagTotalSpace.totalSet n) ∧
        Function.Bijective (fderiv ℂ (fun w => g (p, w)) 0) ∧
        ∃ A : Pair ≃L[ℂ] Pair,
          HasFDerivAt (fun w => g (p, w)) (A : Pair →L[ℂ] Pair) 0 := by
  obtain ⟨B, f, g, hB, hKB, hBU, hg, hprop⟩ :=
    FlagCompactBasin.exists_neighbourhood_family hR h hU hKU hh hadm
  refine ⟨B, f, g, hB, hKB, hBU, hg, ?_⟩
  intro p hp
  obtain ⟨hzero, hfzero, hf, hleft, hinj, havoid⟩ := hprop p hp
  have hf' : DifferentiableAt ℂ f (p, g (p, 0)) := hzero.symm ▸ hf
  exact ⟨hzero, hfzero, hf, hleft, hinj, havoid,
    vertical_derivative_bijective f g hB hg hp hf' hleft,
    vertical_derivative_equiv f g hB hg hp hf' hleft⟩

end AutomaticContinuity.FlagDominatingFamily
