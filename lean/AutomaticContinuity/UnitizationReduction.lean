import AutomaticContinuity.Characters
import AutomaticContinuity.UnitizationTopology

/-!
# Reduction from nonunital algebras to unital algebras

This is a conditional reduction, not a proof of the remaining unital theorem.
The general product construction is used; no normability assumption is added.
-/

namespace AutomaticContinuity

universe u

/-- The unital case of the boundedness target. This defines the proposition that
remains to be proved, without asserting it as an axiom or theorem. -/
def UnitalBoundednessStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A]
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A],
    IsLocallyMultiplicativelyConvex A →
    ∀ χ : Character A, BoundedOnBoundedSets A (fun a => χ.val a)

open scoped UnitizationTopology

/-- Once the unital case is known, passage to the unitization proves Theorem A
for every algebra in its stated scope. -/
theorem theoremA_of_unitalBoundedness :
    UnitalBoundednessStatement.{u} → TheoremAStatement.{u} := by
  intro h A _ _ _ _ _ _ _ _ hA χ B hB
  have hU := h (Unitization ℂ A) (UnitizationTopology.isLocallyMultiplicativelyConvex hA)
    χ.unitize
  obtain ⟨C, hC, hbound⟩ := hU ((Unitization.inr : A → Unitization ℂ A) '' B)
    (UnitizationTopology.isVonNBounded_image_inr hB)
  refine ⟨C, hC, ?_⟩
  intro a ha
  simpa using hbound (Unitization.inr a) ⟨a, ha, rfl⟩

end AutomaticContinuity
