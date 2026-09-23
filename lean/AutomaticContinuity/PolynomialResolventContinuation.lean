import AutomaticContinuity.PolynomialProjectionSpectrum

set_option autoImplicit false

/-!
# Coordinate resolvents by escape to infinity

An unbounded connected subset of the complement of a coordinate range
cannot belong to a bounded complementary component of the ambient spectrum.
This yields an actual inverse in the closed polynomial algebra, without
assuming polynomial convexity or connectedness of the entire complement.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set
open scoped Topology

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

theorem coordinateDenominator_isUnit_of_unbounded_connected
    (j : σ) (ζ : ℂ) (T : Set ℂ) (hT : IsPreconnected T) (hζ : ζ ∈ T)
    (havoid : T ⊆ (coordinateRange K j)ᶜ)
    (hunbounded : ¬ Bornology.IsBounded T) :
    IsUnit (coordinateDenominator K j ζ) := by
  let : IsClosed (algebra K : Set C(K, ℂ)) :=
    Subalgebra.isClosed_topologicalClosure (restriction K).range
  change IsUnit (algebraMap ℂ (P K) ζ - polynomial K (MvPolynomial.X j))
  rw [← spectrum.notMem_iff]
  intro hs
  have hval : spectrum ℂ (polynomial K (MvPolynomial.X j)).val = coordinateRange K j := by
    rw [ContinuousMap.spectrum_eq_range]
    congr 1
    funext x
    simp [polynomial_apply]
  have hb := Subalgebra.spectrum_isBounded_connectedComponentIn (algebra K)
    (polynomial K (MvPolynomial.X j)) hs
  rw [hval] at hb
  exact hunbounded (hb.subset (hT.subset_connectedComponentIn hζ havoid))

theorem coordinateDenominator_isUnit_of_escape
    (j : σ) (hescape : ∀ ζ ∉ coordinateRange K j,
      ∃ T : Set ℂ, IsPreconnected T ∧ ζ ∈ T ∧
        T ⊆ (coordinateRange K j)ᶜ ∧ ¬ Bornology.IsBounded T)
    (ζ : ℂ) (hζ : ζ ∉ coordinateRange K j) :
    IsUnit (coordinateDenominator K j ζ) := by
  obtain ⟨T, hT, hmem, havoid, hunbounded⟩ := hescape ζ hζ
  exact coordinateDenominator_isUnit_of_unbounded_connected K j ζ T hT hmem havoid hunbounded

theorem isPolynomiallyConvex_of_coordinate_escape
    (hprod : ∀ z : σ → ℂ, (∀ j, z j ∈ coordinateRange K j) → z ∈ K)
    (hescape : ∀ j ζ, ζ ∉ coordinateRange K j →
      ∃ T : Set ℂ, IsPreconnected T ∧ ζ ∈ T ∧
        T ⊆ (coordinateRange K j)ᶜ ∧ ¬ Bornology.IsBounded T) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K := by
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  have hex : ∃ j, z j ∉ coordinateRange K j := by
    by_contra! h
    exact hz (hprod z h)
  obtain ⟨j, hj⟩ := hex
  have hunit := coordinateDenominator_isUnit_of_escape K j (hescape j) (z j) hj
  obtain ⟨q, hq, hqz⟩ := exists_coordinate_separator_of_isUnit K j (z j) hunit
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨q, 1 / 2, ?_, ?_⟩
  · intro x hx
    exact (hq ⟨x, hx⟩).le
  · rw [hqz z rfl, norm_one]
    norm_num

end AutomaticContinuity.PolynomialFunctionAlgebra
