import AutomaticContinuity.PolynomialConvexUnion

set_option autoImplicit false

/-!
# Adjoining a compact set in an exterior neighbourhood

Every exterior point of a compact polynomially convex set has a fixed open
neighbourhood in which any compact polynomially convex set can be adjoined
without changing polynomial convexity. This is the local union property needed
when placing a small neighbourhood of a section value outside a forbidden set.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialConvexNeighbourhood

open Set MvPolynomial

universe u v
variable {X : Type u} {σ : Type v}

theorem exists_neighbourhood [TopologicalSpace X]
    (e : X → σ → ℂ) (he : Continuous e) (K : Set X)
    (hKcompact : IsCompact K) (hK : IsPolynomiallyConvexOf e K)
    (x : X) (hx : x ∉ K) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint K V ∧
      ∀ L : Set X, L ⊆ V → IsCompact L → IsPolynomiallyConvexOf e L →
        IsPolynomiallyConvexOf e (K ∪ L) := by
  obtain ⟨V, hV, hxV, hdisjoint, hcut⟩ :=
    PolynomialExteriorCutoff.exists_neighbourhood_cutoffs e he K x (by rwa [hK])
  obtain ⟨q, _, hqK, hqV⟩ := hcut (1 / 8) (by norm_num)
  refine ⟨V, hV, hxV, hdisjoint, ?_⟩
  intro L hLV hLcompact hL
  exact PolynomialConvexUnion.isPolynomiallyConvexOf_union e he hKcompact hLcompact
    hK hL q (fun y hy => (hqK y hy).le) (fun y hy => (hqV y (hLV hy)).le)

/-- The local adjoining property for the actual compact forbidden flag graph. -/
theorem exists_neighbourhood_compactForbiddenGraph (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (x : FlagPolynomialSeparation.Point n)
    (hx : x ∉ FlagTotalSpace.compactForbiddenGraph n R) :
    ∃ V : Set (FlagPolynomialSeparation.Point n), IsOpen V ∧ x ∈ V ∧
      Disjoint (FlagTotalSpace.compactForbiddenGraph n R) V ∧
      ∀ L : Set (FlagPolynomialSeparation.Point n), L ⊆ V → IsCompact L →
        IsPolynomiallyConvexOf FlagPolynomialSeparation.coordinates L →
        IsPolynomiallyConvexOf FlagPolynomialSeparation.coordinates
          (FlagTotalSpace.compactForbiddenGraph n R ∪ L) :=
  exists_neighbourhood FlagPolynomialSeparation.coordinates
    (FlagPolynomialSeparation.continuous_coordinates n)
    (FlagTotalSpace.compactForbiddenGraph n R)
    (FlagTotalSpace.isCompact_compactForbiddenGraph n hR)
    (FlagPolynomialSeparation.isPolynomiallyConvex_compactForbiddenGraph n hR) x hx

end AutomaticContinuity.PolynomialConvexNeighbourhood
