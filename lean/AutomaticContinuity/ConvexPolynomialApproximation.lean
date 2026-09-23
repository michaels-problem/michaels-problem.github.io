import AutomaticContinuity.RadialCompactFamily
import AutomaticContinuity.RadialPolynomialSeed
import AutomaticContinuity.ClosedSubspaceAnalyticContinuation

set_option autoImplicit false

/-! # Polynomial approximation on compact convex sets

This proves the required scalar Runge theorem by a radial family in the
actual Banach space `C(K,ℂ)`. The local polydisc expansion gives a polynomial
seed near parameter zero; the identity theorem in the quotient by the closed
polynomial algebra propagates membership to parameter one.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set Filter
open scoped Topology

theorem exists_polynomial_approx_on_convex {n : ℕ}
    {K U : Set (FinitePoint n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) (f : FinitePoint n → ℂ)
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖MvPolynomial.eval z p - f z‖ < ε := by
  classical
  rcases K.eq_empty_or_nonempty with hEmpty | ⟨c, hc⟩
  · exact ⟨0, fun z hz => False.elim (by simp [hEmpty] at hz)⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨O, F, hO, hinterval, _, hF, hFeq⟩ :=
    RadialCompactFamily.exists_holomorphic_radial_family hK hconv hU hKU hc f hf
  have h0 : (0 : ℂ) ∈ O := by simpa using hinterval 0 (by simp)
  have h1 : (1 : ℂ) ∈ O := by simpa using hinterval 1 (by simp)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x : K, F t x = f (c+t•(x.val-c)) := by
    filter_upwards [hO.mem_nhds h0] with t ht
    exact hFeq t ht
  have hseed := eventually_mem_algebra_radial K hK c f hU (hKU hc) hf F hnear
  let A : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1
  have hA : IsPreconnected A := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hAO : A ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact hinterval t ht
  have h0A : (0 : ℂ) ∈ A := ⟨0, by simp, by simp⟩
  have h1A : (1 : ℂ) ∈ A := ⟨1, by simp, by simp⟩
  have hmem : F 1 ∈ algebra K :=
    mem_algebra_of_analytic_continuation K hO hF hA hAO h0A hseed 1 h1A
  obtain ⟨p, hp⟩ := exists_polynomial_approx K ⟨F 1, hmem⟩ hε
  refine ⟨p, fun z hz => ?_⟩
  have hb := (ContinuousMap.norm_coe_le_norm
    (polynomial K p - (⟨F 1,hmem⟩ : P K)).val ⟨z,hz⟩).trans_lt hp
  have heval : F 1 ⟨z,hz⟩ = f z := by
    simpa using hFeq 1 h1 ⟨z,hz⟩
  simpa only [Subalgebra.coe_sub, ContinuousMap.sub_apply, polynomial_apply, heval] using hb

end AutomaticContinuity.PolynomialFunctionAlgebra
