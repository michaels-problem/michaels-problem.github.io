import AutomaticContinuity.HomogeneousCoefficientSelection
import AutomaticContinuity.HomogeneousFieldDecomposition

set_option autoImplicit false

/-!
# Parameter-compatible coefficients for complete homogeneous fields

A fixed complex-linear right inverse of actual field synthesis chooses all
shear and overshear coefficients simultaneously. On ordinary finite monomial
arrays the selector is continuous linear, with a fixed norm bound, and thus
preserves local holomorphic parameter dependence and exact zero coefficients.
-/

noncomputable section

namespace AutomaticContinuity.HomogeneousFieldCoefficientSelection

open HomogeneousPowerBasis HomogeneousFieldDecomposition
open HomogeneousCoefficientSelection
open scoped BigOperators

abbrev HomogeneousField (m : ℕ) := HomogeneousPoly (m + 1) × HomogeneousPoly (m + 1)
abbrev CompleteCoefficients (m : ℕ) := (Fin (m + 1) → ℂ) × (Fin (m + 3) → ℂ)
abbrev MonomialCoefficients (m : ℕ) := (Fin (m + 2) → ℂ) × (Fin (m + 2) → ℂ)

def forget (m : ℕ) : HomogeneousField m →ₗ[ℂ] Field where
  toFun F := (F.1.val, F.2.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem forget_injective (m : ℕ) : Function.Injective (forget m) := by
  intro F G h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

def overshearVector (m : ℕ) (s : ℂ) : HomogeneousField m :=
  (⟨(overshear s m).1, (overshear_homogeneous s m).1⟩,
   ⟨(overshear s m).2, (overshear_homogeneous s m).2⟩)

def shearVector (m : ℕ) (s : ℂ) : HomogeneousField m :=
  (⟨(shear s (m + 1)).1, (shear_homogeneous s (m + 1)).1⟩,
   ⟨(shear s (m + 1)).2, (shear_homogeneous s (m + 1)).2⟩)

@[simp] theorem forget_overshearVector (m : ℕ) (s : ℂ) :
    forget m (overshearVector m s) = overshear s m := rfl

@[simp] theorem forget_shearVector (m : ℕ) (s : ℂ) :
    forget m (shearVector m s) = shear s (m + 1) := rfl

def synthesis (m : ℕ) : CompleteCoefficients m →ₗ[ℂ] HomogeneousField m where
  toFun a := (∑ j, a.1 j • overshearVector m (j.val : ℂ)) +
    ∑ j, a.2 j • shearVector m (j.val : ℂ)
  map_add' a b := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_add,
      Finset.smul_sum, smul_smul, RingHom.id_apply, smul_eq_mul]

theorem forget_synthesis (m : ℕ) (a : CompleteCoefficients m) :
    forget m (synthesis m a) =
      (∑ j, a.1 j • overshear (j.val : ℂ) m) +
        ∑ j, a.2 j • shear (j.val : ℂ) (m + 1) := by
  change forget m ((∑ j, a.1 j • overshearVector m (j.val : ℂ)) +
    ∑ j, a.2 j • shearVector m (j.val : ℂ)) = _
  simp only [map_add, map_sum, map_smul, forget_overshearVector, forget_shearVector]

theorem synthesis_surjective (m : ℕ) : Function.Surjective (synthesis m) := by
  intro F
  obtain ⟨c, b, hcb⟩ := exists_decomposition m F.1.val F.2.val F.1.property F.2.property
  refine ⟨(c, b), forget_injective m ?_⟩
  rw [forget_synthesis]
  exact hcb.symm

theorem exists_linear_selector (m : ℕ) :
    ∃ s : HomogeneousField m →ₗ[ℂ] CompleteCoefficients m,
      (synthesis m).comp s = LinearMap.id :=
  (synthesis m).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (synthesis_surjective m))

def selector (m : ℕ) : HomogeneousField m →ₗ[ℂ] CompleteCoefficients m :=
  Classical.choose (exists_linear_selector m)

theorem synthesis_comp_selector (m : ℕ) :
    (synthesis m).comp (selector m) = LinearMap.id :=
  Classical.choose_spec (exists_linear_selector m)

@[simp] theorem synthesis_selector (m : ℕ) (F : HomogeneousField m) :
    synthesis m (selector m F) = F :=
  LinearMap.congr_fun (synthesis_comp_selector m) F

theorem decomposition (m : ℕ) (F : HomogeneousField m) :
    forget m F =
      (∑ j, (selector m F).1 j • overshear (j.val : ℂ) m) +
        ∑ j, (selector m F).2 j • shear (j.val : ℂ) (m + 1) := by
  rw [← forget_synthesis, synthesis_selector]

def monomialSynthesis (m : ℕ) : MonomialCoefficients m →ₗ[ℂ] HomogeneousField m :=
  (HomogeneousCoefficientSelection.monomialSynthesis (m + 1)).prodMap
    (HomogeneousCoefficientSelection.monomialSynthesis (m + 1))

/-- One continuous complex-linear coefficient change for each homogeneous degree. -/
def coefficients (m : ℕ) : MonomialCoefficients m →L[ℂ] CompleteCoefficients m :=
  LinearMap.toContinuousLinearMap ((selector m).comp (monomialSynthesis m))

theorem decomposition_of_array (m : ℕ) (a : MonomialCoefficients m) :
    ((∑ k, a.1 k • monomialAt (m + 1) k),
      ∑ k, a.2 k • monomialAt (m + 1) k) =
      (∑ j, (coefficients m a).1 j • overshear (j.val : ℂ) m) +
        ∑ j, (coefficients m a).2 j • shear (j.val : ℂ) (m + 1) :=
  decomposition m (monomialSynthesis m a)

theorem norm_coefficients_le (m : ℕ) (a : MonomialCoefficients m) :
    ‖coefficients m a‖ ≤ ‖coefficients m‖ * ‖a‖ :=
  (coefficients m).le_opNorm a

theorem continuous_coefficients {P : Type*} [TopologicalSpace P] (m : ℕ)
    {a : P → MonomialCoefficients m} (ha : Continuous a) :
    Continuous (fun p => coefficients m (a p)) := (coefficients m).continuous.comp ha

theorem differentiableOn_coefficients {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P] (m : ℕ)
    {U : Set P} {a : P → MonomialCoefficients m} (ha : DifferentiableOn ℂ a U) :
    DifferentiableOn ℂ (fun p => coefficients m (a p)) U :=
  (coefficients m).differentiable.comp_differentiableOn ha

end AutomaticContinuity.HomogeneousFieldCoefficientSelection
