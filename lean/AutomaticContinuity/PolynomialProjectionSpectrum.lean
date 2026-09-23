import AutomaticContinuity.PolynomialFunctionResolvent
import AutomaticContinuity.PolynomialBezoutCutoff
import Mathlib.Topology.ContinuousMap.Units

set_option autoImplicit false

/-!
# Coordinate resolvents from connected planar complements

The spectrum in a closed subalgebra can only fill bounded complementary
components of the ambient spectrum. Consequently a coordinate projection
with connected complement has no additional spectrum in the closed
polynomial function algebra. This constructs the actual resolvent without
assuming polynomial convexity of the full compact set.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set
open scoped Topology

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

def coordinateRange (j : σ) : Set ℂ := Set.range (fun x : K => x.val j)

theorem coordinate_spectrum_eq_range (j : σ)
    (hc : IsPreconnected (coordinateRange K j)ᶜ) :
    spectrum ℂ (polynomial K (MvPolynomial.X j)) = coordinateRange K j := by
  let : IsClosed (algebra K : Set C(K, ℂ)) :=
    Subalgebra.isClosed_topologicalClosure (restriction K).range
  have hval : spectrum ℂ (polynomial K (MvPolynomial.X j)).val = coordinateRange K j := by
    rw [ContinuousMap.spectrum_eq_range]
    congr 1
    funext x
    simp [polynomial_apply]
  rw [Subalgebra.spectrum_eq_of_isPreconnected_compl (algebra K)
    (polynomial K (MvPolynomial.X j)) (hval.symm ▸ hc), hval]

theorem coordinateDenominator_isUnit_of_connected_compl (j : σ)
    (hc : IsPreconnected (coordinateRange K j)ᶜ) (ζ : ℂ)
    (hζ : ∀ x : K, ζ ≠ x.val j) :
    IsUnit (coordinateDenominator K j ζ) := by
  change IsUnit (algebraMap ℂ (P K) ζ - polynomial K (MvPolynomial.X j))
  rw [← spectrum.notMem_iff, coordinate_spectrum_eq_range K j hc]
  rintro ⟨x, hx⟩
  exact hζ x hx.symm

/-- One invertible coordinate denominator gives a polynomial separating the
entire compact from any point with that excluded coordinate. -/
theorem exists_coordinate_separator_of_isUnit (j : σ) (ζ : ℂ)
    (hunit : IsUnit (coordinateDenominator K j ζ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      (∀ x : K, ‖MvPolynomial.eval x.val q‖ < ε) ∧
      ∀ z : σ → ℂ, z j = ζ → MvPolynomial.eval z q = 1 := by
  let a : Fin 1 → P K := fun _ => coordinateDenominator K j ζ
  have hnz : ∀ η : P K →ₐ[ℂ] ℂ, ∃ i : Fin 1, η (a i) ≠ 0 := by
    intro η
    exact ⟨0, (η.isUnit_map hunit).ne_zero⟩
  obtain ⟨p, hp⟩ := PolynomialBezoutCutoff.exists_small_residual a
    (polynomial K) (denseRange_polynomial K) hnz hε
  let q : MvPolynomial σ ℂ := 1 - (MvPolynomial.C ζ - MvPolynomial.X j) * p 0
  have hp' : ‖1 - coordinateDenominator K j ζ * polynomial K (p 0)‖ < ε := by
    simpa only [Fin.sum_univ_one, a] using hp
  have heq : polynomial K q = 1 - coordinateDenominator K j ζ * polynomial K (p 0) := by
    dsimp only [q]
    rw [map_sub, map_one, map_mul]
    congr 2
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    simp only [Subalgebra.coe_sub, ContinuousMap.sub_apply, polynomial_apply,
      coordinateDenominator_apply, map_sub,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hnorm : ‖polynomial K q‖ < ε := by
    rw [heq]
    exact hp'
  refine ⟨q, ?_, ?_⟩
  · intro x
    have hb := (ContinuousMap.norm_coe_le_norm (polynomial K q).val x).trans_lt hnorm
    simpa only [polynomial_apply] using hb
  · intro z hz
    simp [q, hz]

/-- A product-shaped compact whose coordinate complements are connected is
polynomially convex. No contour approximation result is an assumption. -/
theorem isPolynomiallyConvex_of_coordinate_ranges
    (hprod : ∀ z : σ → ℂ, (∀ j, z j ∈ coordinateRange K j) → z ∈ K)
    (hc : ∀ j, IsPreconnected (coordinateRange K j)ᶜ) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) K := by
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  have hex : ∃ j, z j ∉ coordinateRange K j := by
    by_contra! h
    exact hz (hprod z h)
  obtain ⟨j, hj⟩ := hex
  have hunit := coordinateDenominator_isUnit_of_connected_compl K j (hc j) (z j)
    (fun x h => hj ⟨x, h.symm⟩)
  obtain ⟨q, hq, hqz⟩ := exists_coordinate_separator_of_isUnit K j (z j) hunit
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨q, 1 / 2, ?_, ?_⟩
  · intro x hx
    exact (hq ⟨x, hx⟩).le
  · rw [hqz z rfl, norm_one]
    norm_num

end AutomaticContinuity.PolynomialFunctionAlgebra
