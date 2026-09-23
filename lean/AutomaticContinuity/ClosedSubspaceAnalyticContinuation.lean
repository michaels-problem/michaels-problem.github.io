import AutomaticContinuity.PolynomialFunctionAlgebra
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

/-! # Analytic continuation of membership in a closed complex subspace

Apply the identity theorem to the actual normed quotient map. In particular,
membership in the closed polynomial algebra propagates from a neighbourhood
of one parameter to every point of a connected parameter set.
-/

noncomputable section

namespace AutomaticContinuity

open Set Filter
open scoped Topology

theorem mem_closedSubmodule_of_analytic_continuation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    {F : ℂ → E} {O A : Set ℂ} (hO : IsOpen O)
    (hF : DifferentiableOn ℂ F O) (hA : IsPreconnected A) (hAO : A ⊆ O)
    {t₀ : ℂ} (ht₀ : t₀ ∈ A) (hseed : ∀ᶠ t in 𝓝 t₀, F t ∈ S) :
    ∀ t ∈ A, F t ∈ S := by
  let : IsClosed (S : Set E) := hS
  let q : E →L[ℂ] E ⧸ S := S.mkQL
  have hqF : AnalyticOnNhd ℂ (fun t => q (F t)) A := by
    intro t ht
    exact (q.analyticAt (F t)).comp (hF.analyticAt (hO.mem_nhds (hAO ht)))
  have hzero : (fun t => q (F t)) =ᶠ[𝓝 t₀] 0 := by
    filter_upwards [hseed] with t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr ht
  have h := hqF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hA ht₀ hzero
  intro t ht
  exact (Submodule.Quotient.mk_eq_zero S).mp (h ht)

namespace PolynomialFunctionAlgebra

theorem mem_algebra_of_analytic_continuation
    {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]
    {F : ℂ → C(K, ℂ)} {O A : Set ℂ} (hO : IsOpen O)
    (hF : DifferentiableOn ℂ F O) (hA : IsPreconnected A) (hAO : A ⊆ O)
    {t₀ : ℂ} (ht₀ : t₀ ∈ A) (hseed : ∀ᶠ t in 𝓝 t₀, F t ∈ algebra K) :
    ∀ t ∈ A, F t ∈ algebra K :=
  mem_closedSubmodule_of_analytic_continuation (algebra K).toSubmodule
    (Subalgebra.isClosed_topologicalClosure (restriction K).range)
    hO hF hA hAO ht₀ hseed

end PolynomialFunctionAlgebra

end AutomaticContinuity
