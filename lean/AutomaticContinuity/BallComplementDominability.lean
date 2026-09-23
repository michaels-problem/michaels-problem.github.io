import AutomaticContinuity.ConcreteBallAvoidance
import AutomaticContinuity.SmallScaleHenonGeometry
import AutomaticContinuity.EuclideanPairRotations

set_option autoImplicit false

/-!
# Entire injective maps into a ball complement through every exterior point

The explicit two-attractor polynomial automorphism, its proved basin
linearization, and a complex linear Euclidean rotation supply these maps.
This is a pointwise flexibility theorem, not an Oka approximation theorem or
a family over an arbitrary compact parameter set.
-/

noncomputable section

namespace AutomaticContinuity.BallComplementDominability

open SmallScaleHenonTrapping

/-- Every point exterior to a positive-radius closed Euclidean ball lies on
an injective entire image of `ℂ²` disjoint from that ball, with the point at
the image of zero. -/
theorem exists_entire_injection {r : ℝ} (hr : 0 < r) (p : ℂ × ℂ)
    (hp : r < euclideanPairNorm p) :
    ∃ f : (ℂ × ℂ) → ℂ × ℂ, Differentiable ℂ f ∧ Function.Injective f ∧
      f 0 = p ∧ ∀ z, r < euclideanPairNorm (f z) := by
  obtain ⟨β, a, hβ, hβq, hra, heq, _, _⟩ := exists_exteriorPoint_of_norm hr hp
  obtain ⟨f, hf, hinj, hf0, hout⟩ := ConcreteBallAvoidance.exists_entire_injection hβ hβq hr hra
  have hpos : 0 < euclideanPairNorm (exteriorPoint β a) := heq.symm ▸ (hr.trans hp)
  obtain ⟨e, he, henorm⟩ := EuclideanPairRotations.exists_rotation (exteriorPoint β a) p hpos heq
  refine ⟨fun z => e (f z), e.differentiable.comp hf, e.injective.comp hinj, ?_, ?_⟩
  · change e (f 0) = p
    rw [hf0, he]
  · intro z
    rw [henorm]
    exact hout z

end AutomaticContinuity.BallComplementDominability
