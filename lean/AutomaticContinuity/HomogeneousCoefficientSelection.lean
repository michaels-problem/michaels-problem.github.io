import AutomaticContinuity.HomogeneousPowerBasis
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false

/-!
# Fixed complex-linear homogeneous coefficient selection

The chosen section is a linear map once and for all at each degree. Its
coefficients are not selected independently at each parameter value. On the
ordinary finite arrays this gives an actual continuous complex-linear map,
so continuous and holomorphic parameter dependence are preserved.
-/

noncomputable section

namespace AutomaticContinuity.HomogeneousCoefficientSelection

open MvPolynomial HomogeneousPowerBasis
open scoped BigOperators

abbrev HomogeneousPoly (m : ℕ) : Type := homogeneousSubmodule (Fin 2) ℂ m

/-- Synthesis in the fixed linear-form powers, with slopes `0,...,m`. -/
def synthesis (m : ℕ) : (Fin (m + 1) → ℂ) →ₗ[ℂ] HomogeneousPoly m where
  toFun b := ⟨∑ j, b j • linearForm (j.val : ℂ) ^ m,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (linearForm_pow_homogeneous (j.val : ℂ) m)⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' c a := by
    apply Subtype.ext
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, Submodule.coe_smul,
      RingHom.id_apply, smul_eq_mul]

@[simp] theorem synthesis_val (m : ℕ) (b : Fin (m + 1) → ℂ) :
    (synthesis m b).val = ∑ j, b j • linearForm (j.val : ℂ) ^ m := rfl

theorem synthesis_surjective (m : ℕ) : Function.Surjective (synthesis m) := by
  intro p
  obtain ⟨b, hb⟩ := exists_expansion p.property
  exact ⟨b, Subtype.ext hb.symm⟩

theorem exists_linear_selector (m : ℕ) :
    ∃ s : HomogeneousPoly m →ₗ[ℂ] (Fin (m + 1) → ℂ),
      (synthesis m).comp s = LinearMap.id :=
  (synthesis m).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (synthesis_surjective m))

/-- One fixed linear selector for the entire homogeneous space. -/
def selector (m : ℕ) : HomogeneousPoly m →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
  Classical.choose (exists_linear_selector m)

theorem synthesis_comp_selector (m : ℕ) :
    (synthesis m).comp (selector m) = LinearMap.id :=
  Classical.choose_spec (exists_linear_selector m)

@[simp] theorem synthesis_selector (m : ℕ) (p : HomogeneousPoly m) :
    synthesis m (selector m p) = p :=
  LinearMap.congr_fun (synthesis_comp_selector m) p

/-- The selected coefficients reconstruct the actual polynomial. -/
theorem expansion (m : ℕ) (p : HomogeneousPoly m) :
    p.val = ∑ j, selector m p j • linearForm (j.val : ℂ) ^ m := by
  exact (congrArg Subtype.val (synthesis_selector m p)).symm

theorem selector_injective (m : ℕ) : Function.Injective (selector m) := by
  intro p q hpq
  simpa only [synthesis_selector] using congrArg (synthesis m) hpq

theorem monomialAt_homogeneous (m : ℕ) (k : Fin (m + 1)) :
    (monomialAt m k).IsHomogeneous m := by
  have hk : k.val ≤ m := Nat.le_of_lt_succ k.isLt
  have hh := ((isHomogeneous_X ℂ (0 : Fin 2)).pow (m - k.val)).mul
    ((isHomogeneous_X ℂ (1 : Fin 2)).pow k.val)
  simpa only [monomialAt, one_mul, Nat.sub_add_cancel hk] using hh

/-- Ordinary monomial coefficient arrays synthesise homogeneous polynomials. -/
def monomialSynthesis (m : ℕ) : (Fin (m + 1) → ℂ) →ₗ[ℂ] HomogeneousPoly m where
  toFun a := ⟨∑ k, a k • monomialAt m k,
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (monomialAt_homogeneous m k)⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' c a := by
    apply Subtype.ext
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, Submodule.coe_smul,
      RingHom.id_apply, smul_eq_mul]

/-- The coefficient change on finite arrays is genuinely continuous linear. -/
def coefficients (m : ℕ) : (Fin (m + 1) → ℂ) →L[ℂ] (Fin (m + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap ((selector m).comp (monomialSynthesis m))

theorem expansion_of_array (m : ℕ) (a : Fin (m + 1) → ℂ) :
    ∑ k, a k • monomialAt m k =
      ∑ j, coefficients m a j • linearForm (j.val : ℂ) ^ m :=
  expansion m (monomialSynthesis m a)

theorem norm_coefficients_le (m : ℕ) (a : Fin (m + 1) → ℂ) :
    ‖coefficients m a‖ ≤ ‖coefficients m‖ * ‖a‖ :=
  (coefficients m).le_opNorm a

theorem continuous_coefficients {P : Type*} [TopologicalSpace P] (m : ℕ)
    {a : P → Fin (m + 1) → ℂ} (ha : Continuous a) :
    Continuous (fun p => coefficients m (a p)) := (coefficients m).continuous.comp ha

theorem differentiableOn_coefficients {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] (m : ℕ)
    {U : Set P} {a : P → Fin (m + 1) → ℂ} (ha : DifferentiableOn ℂ a U) :
    DifferentiableOn ℂ (fun p => coefficients m (a p)) U :=
  (coefficients m).differentiable.comp_differentiableOn ha

end AutomaticContinuity.HomogeneousCoefficientSelection
