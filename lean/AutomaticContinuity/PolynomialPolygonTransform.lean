import AutomaticContinuity.PolynomialFunctionResolvent
import AutomaticContinuity.PolygonCauchyIntegral

set_option autoImplicit false

/-! # Polygon Cauchy transforms in the closed polynomial algebra

These are actual integrals of actual inverses in `P(K)`. Uniform polynomial
approximation follows from the definition of this closed algebra, without
an assumed Runge theorem or an assumed approximation operator.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set MeasureTheory
open PolygonCauchy

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

def polygonTransform (j : σ) {n : ℕ} (v : Fin (n+1) → ℂ) (f : ℂ → ℂ) : P K :=
  polygonIntegral v (fun ζ => f ζ • coordinateResolvent K j ζ)

theorem polygonTransform_apply
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) {n : ℕ} (v : Fin (n+1) → ℂ) (f : ℂ → ℂ)
    (hf : ∀ i, ContinuousOn (fun t => f (edge (v i) (v (i+1)) t)) (Icc 0 1))
    (havoid : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : K,
      edge (v i) (v (i+1)) t ≠ x.val j) (x : K) :
    (polygonTransform K j v f).val x =
      polygonIntegral v (fun ζ => (ζ - x.val j)⁻¹ * f ζ) := by
  change evaluationCLM K x (polygonTransform K j v f) = _
  unfold polygonTransform polygonIntegral
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold segmentIntegral
  rw [map_smul]
  congr 1
  have hc : ContinuousOn
      (fun t => f (edge (v i) (v (i+1)) t) •
        coordinateResolvent K j (edge (v i) (v (i+1)) t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (hf i).smul (continuousOn_coordinateResolvent_comp K hK j _
      (continuous_edge _ _).continuousOn (havoid i))
  rw [← (evaluationCLM K x).intervalIntegral_comp_comm hc.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  simp only [map_smul, evaluationCLM_apply, smul_eq_mul,
    coordinateResolvent_apply K hK j _ (havoid i t ht') x]
  exact mul_comm _ _

theorem exists_polynomial_approx_polygonTransform
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) {n : ℕ} (v : Fin (n+1) → ℂ) (f : ℂ → ℂ)
    (hf : ∀ i, ContinuousOn (fun t => f (edge (v i) (v (i+1)) t)) (Icc 0 1))
    (havoid : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : K,
      edge (v i) (v (i+1)) t ≠ x.val j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℂ, ∀ x : K,
      ‖MvPolynomial.eval x.val p -
        polygonIntegral v (fun ζ => (ζ-x.val j)⁻¹ * f ζ)‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_approx K (polygonTransform K j v f) hε
  refine ⟨p, fun x => ?_⟩
  have hx := (ContinuousMap.norm_coe_le_norm
    (polynomial K p - polygonTransform K j v f).val x).trans_lt hp
  simpa only [Subalgebra.coe_sub, ContinuousMap.sub_apply, polynomial_apply,
    polygonTransform_apply K hK j v f hf havoid x] using hx

end AutomaticContinuity.PolynomialFunctionAlgebra
