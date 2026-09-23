import AutomaticContinuity.Statement
import Mathlib.Algebra.Algebra.Unitization

/-! # Elementary character and boundedness facts

These lemmas explain the definitions and prepare the unitisation step. None
uses, assumes, or proves Theorem A.
-/

namespace AutomaticContinuity

universe u

namespace Character

variable {A : Type u} [NonUnitalCommRing A] [Module ℂ A]

theorem exists_apply_ne_zero (χ : Character A) : ∃ a : A, χ.val a ≠ 0 := by
  by_contra h
  apply χ.property
  ext a
  simpa using (not_exists_not.mp h a)

end Character

section Unital

variable {A : Type u} [CommRing A] [Algebra ℂ A]

/-- The nonzero hypothesis forces a character on a unital algebra to preserve one. -/
theorem Character.map_one (χ : Character A) : χ.val 1 = 1 := by
  obtain ⟨a, ha⟩ := χ.exists_apply_ne_zero
  have h : χ.val 1 * χ.val a = 1 * χ.val a := by
    rw [← map_mul, one_mul, one_mul]
  exact mul_right_cancel₀ ha h

/-- Regard an algebraic character on a unital algebra as a unital homomorphism. -/
def Character.toAlgHom (χ : Character A) : A →ₐ[ℂ] ℂ where
  toFun := χ.val
  map_one' := χ.map_one
  map_mul' := map_mul χ.val
  map_zero' := map_zero χ.val
  map_add' := map_add χ.val
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, χ.map_one]
    simp

@[simp] theorem Character.toAlgHom_apply (χ : Character A) (a : A) :
    χ.toAlgHom a = χ.val a := rfl

/-- Unital algebra homomorphisms to ℂ are automatically nonzero. -/
def Character.ofAlgHom (χ : A →ₐ[ℂ] ℂ) : Character A :=
  ⟨χ.toNonUnitalAlgHom, by
    intro h
    have h1 := DFunLike.congr_fun h (1 : A)
    change χ 1 = 0 at h1
    simp at h1⟩

@[simp] theorem Character.ofAlgHom_apply (χ : A →ₐ[ℂ] ℂ) (a : A) :
    (Character.ofAlgHom χ).val a = χ a := rfl

end Unital

section Unitisation

variable {A : Type u} [NonUnitalCommRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Algebraic extension to the standard Mathlib unitisation, ordered as ℂ × A. -/
def Character.unitize (χ : Character A) : Character (Unitization ℂ A) :=
  Character.ofAlgHom (Unitization.lift χ.val)

@[simp] theorem Character.unitize_apply (χ : Character A) (a : Unitization ℂ A) :
    χ.unitize.val a = a.fst + χ.val a.snd := rfl

@[simp] theorem Character.unitize_inr (χ : Character A) (a : A) :
    χ.unitize.val (Unitization.inr a) = χ.val a := by
  simp [Character.unitize_apply]

end Unitisation

section Boundedness

variable {A : Type u} [NonUnitalCommRing A] [Module ℂ A] [TopologicalSpace A]

/-- The numeric definition is equivalent to boundedness of every image in ℂ. -/
theorem boundedOnBoundedSets_iff_image (χ : A → ℂ) :
    BoundedOnBoundedSets A χ ↔
      ∀ B : Set A, Bornology.IsVonNBounded ℂ B →
        Bornology.IsVonNBounded ℂ (χ '' B) := by
  constructor
  · intro h B hB
    obtain ⟨C, _, hC⟩ := h B hB
    exact (NormedSpace.image_isVonNBounded_iff ℂ).2 ⟨C, hC⟩
  · intro h B hB
    obtain ⟨C, hC⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).1 (h B hB)
    exact ⟨max C 0, le_max_right _ _, fun a ha => (hC a ha).trans (le_max_left _ _)⟩

/-- A defining seminorm family detects bounded subsets exactly. -/
theorem bounded_iff_defining_seminorms
    {P : Set (Seminorm ℂ A)}
    (hP : WithSeminorms (fun p : P => p.val)) (B : Set A) :
    Bornology.IsVonNBounded ℂ B ↔
      ∀ p : P, ∃ C > (0 : ℝ), ∀ a ∈ B, p.val a < C :=
  hP.isVonNBounded_iff_seminorm_bounded

end Boundedness

end AutomaticContinuity
