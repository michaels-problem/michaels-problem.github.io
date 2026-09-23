import AutomaticContinuity.PolynomialConvexNeighbourhood
import AutomaticContinuity.TranslatedPolynomialConvexity

set_option autoImplicit false

/-!
# Adjoining a small polydisc to the forbidden compact graph

The new polydisc has positive radius, contains the chosen exterior point in
its interior, is disjoint from the compact graph, and their union is compact
and polynomially convex in all ordinary complex coordinates.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialConvexNeighbourhood

open Set Metric

/-- Every exterior point of a compact polynomially convex set admits a small
closed coordinate polydisc whose union with that set is polynomially convex. -/
theorem exists_closedBall {σ : Type*} [Fintype σ]
    (K : Set (σ → ℂ)) (hKcompact : IsCompact K)
    (hK : IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K)
    (x : σ → ℂ) (hx : x ∉ K) :
    ∃ δ > 0, Disjoint K (closedBall x δ) ∧
      IsCompact (K ∪ closedBall x δ) ∧
      IsPolynomiallyConvexOf (fun z : σ → ℂ => z) (K ∪ closedBall x δ) := by
  obtain ⟨V, hV, hxV, hdisjoint, hunion⟩ :=
    exists_neighbourhood (fun z : σ → ℂ => z) continuous_id K hKcompact hK x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsub : closedBall x (ε / 2) ⊆ V :=
    (closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball
  refine ⟨ε / 2, hhalf, hdisjoint.mono_right hsub,
    hKcompact.union (isCompact_closedBall x (ε / 2)), ?_⟩
  exact hunion _ hsub (isCompact_closedBall x (ε / 2))
    (isPolynomiallyConvex_closedBall x hhalf.le)

/-- Concrete application in all `n+2` complex coordinates of the product
presentation of the forbidden flag graph. -/
theorem exists_closedBall_compactForbiddenGraph (n : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (x : FlagPolynomialSeparation.Point n)
    (hx : x ∉ FlagTotalSpace.compactForbiddenGraph n R) :
    ∃ δ > 0,
      Disjoint (FlagPolynomialSeparation.coordinates '' FlagTotalSpace.compactForbiddenGraph n R)
        (closedBall (FlagPolynomialSeparation.coordinates x) δ) ∧
      IsCompact ((FlagPolynomialSeparation.coordinates '' FlagTotalSpace.compactForbiddenGraph n R) ∪
        closedBall (FlagPolynomialSeparation.coordinates x) δ) ∧
      IsPolynomiallyConvexOf (fun z : FlagPolynomialSeparation.Variables n → ℂ => z)
        ((FlagPolynomialSeparation.coordinates '' FlagTotalSpace.compactForbiddenGraph n R) ∪
          closedBall (FlagPolynomialSeparation.coordinates x) δ) := by
  apply exists_closedBall _
    (FlagPolynomialSeparation.isCompact_coordinates_compactForbiddenGraph n hR)
    (FlagPolynomialSeparation.isPolynomiallyConvex_coordinates_compactForbiddenGraph n hR)
  rintro ⟨y, hy, heq⟩
  have hyx : y = x := (FlagPolynomialSeparation.coordinatesLinearEquiv n).injective heq
  exact hx (hyx ▸ hy)

end AutomaticContinuity.PolynomialConvexNeighbourhood
