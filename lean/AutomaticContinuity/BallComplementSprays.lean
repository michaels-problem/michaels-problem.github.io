import AutomaticContinuity.LocalEntireSpray
import AutomaticContinuity.BallComplementEmbeddings

/-!
# Entire-parameter sprays near every exterior point of a Euclidean ball

The checked normalized Hénon-basin embedding into the complement of a slightly
larger ball supplies an actual spray, jointly holomorphic in the base and entire
parameter. This result is local in the base. It asserts no approximation or
global gluing of sprays over arbitrary compact sections.
-/

noncomputable section

namespace AutomaticContinuity.BallComplementSprays

open LocalEntireSpray

/-- Near each exterior point there is an actual normalized local spray with
injective entire fibers, all of whose values avoid the given closed ball.
The parameter derivative is exactly the identity for every base point. -/
theorem exists_normalized_local_spray {r : ℝ} (hr : 0 < r) (p : Pair)
    (hp : r < euclideanPairNorm p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S : Pair × Pair → Pair,
      Differentiable ℂ S ∧
      (∀ y : Pair, S (y, 0) = y) ∧
      (∀ y : Pair, Function.Injective (fun t => S (y, t))) ∧
      (∀ y : Pair, HasFDerivAt (fun t => S (y, t)) (ContinuousLinearMap.id ℂ Pair) 0) ∧
      (∀ y : Pair, euclideanPairNorm (y - p) < δ →
        ∀ t : Pair, r < euclideanPairNorm (S (y, t))) ∧
      (∀ y : Pair, ∃ e : OpenPartialHomeomorph Pair Pair,
        (e : Pair → Pair) = (fun t => S (y, t)) ∧
        (0 : Pair) ∈ e.source ∧ y ∈ e.target ∧ DifferentiableOn ℂ e.symm e.target) := by
  let R := (r + euclideanPairNorm p) / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hR : 0 < R := hr.trans hrR
  have hRp : R < euclideanPairNorm p := by dsimp [R]; linarith
  obtain ⟨φ, hφ, hφinj, hφ0, hφder, hφR⟩ :=
    BallComplementEmbeddings.exists_normalized_entire_embedding hR p hRp
  refine ⟨R - r, sub_pos.mpr hrR, spray φ p,
    differentiable_spray hφ p, spray_zero hφ0, injective_fiber hφinj,
    hasFDerivAt_fiber hφder, ?_, ?_⟩
  · intro y hy t
    exact spray_avoids hφR hy t
  · intro y
    exact exists_fiber_biholomorphic_chart hφ hφ0 (ContinuousLinearEquiv.refl ℂ Pair)
      (by simpa only [ContinuousLinearEquiv.coe_refl] using hφder) y

end AutomaticContinuity.BallComplementSprays
