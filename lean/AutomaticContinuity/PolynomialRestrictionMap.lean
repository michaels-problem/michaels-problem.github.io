import AutomaticContinuity.PolynomialFunctionAlgebra

set_option autoImplicit false

/-!
# Restriction between the actual polynomial function algebras

Restriction is precomposition with the inclusion of compact coordinate sets.
Uniform polynomial approximability implies membership in the closed
polynomial algebra, including when the compact set is empty.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set

variable {σ : Type*}

theorem mem_algebra_of_approx (K : Set (σ → ℂ)) [CompactSpace K]
    (f : C(K, ℂ))
    (h : ∀ ε > 0, ∃ p : MvPolynomial σ ℂ,
      ∀ x : K, ‖MvPolynomial.eval x.val p - f x‖ < ε) : f ∈ algebra K := by
  change f ∈ closure (Set.range (restriction K))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p, hp⟩ := h (ε / 2) (half_pos hε)
  refine ⟨restriction K p, ⟨p, rfl⟩, ?_⟩
  have hnorm : ‖restriction K p - f‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
    intro x
    simpa only [ContinuousMap.sub_apply, restriction_apply] using (hp x).le
  rw [dist_eq_norm, norm_sub_rev]
  exact hnorm.trans_lt (half_lt_self hε)

def restrictContinuous (K L : Set (σ → ℂ)) (hKL : K ⊆ L) :
    C(L, ℂ) →ₐ[ℂ] C(K, ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ
    ⟨fun x : K => ⟨x.val, hKL x.property⟩,
      continuous_subtype_val.subtype_mk (fun x => hKL x.property)⟩

@[simp] theorem restrictContinuous_apply (K L : Set (σ → ℂ)) (hKL : K ⊆ L)
    (f : C(L, ℂ)) (x : K) :
    restrictContinuous K L hKL f x = f ⟨x.val, hKL x.property⟩ := rfl

theorem restrictContinuous_mem (K L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace L]
    (hKL : K ⊆ L) (f : P L) : restrictContinuous K L hKL f.val ∈ algebra K := by
  apply mem_algebra_of_approx K
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_approx L f hε
  refine ⟨p, fun x => ?_⟩
  have hn := ContinuousMap.norm_coe_le_norm (polynomial L p - f).val
    ⟨x.val, hKL x.property⟩
  have hpoint : ‖(polynomial L p).val ⟨x.val, hKL x.property⟩ -
      f.val ⟨x.val, hKL x.property⟩‖ < ε := lt_of_le_of_lt hn hp
  simpa only [polynomial_apply, restrictContinuous_apply] using hpoint

/-- The actual restriction homomorphism on closed polynomial subalgebras. -/
def restrict (K L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace L] (hKL : K ⊆ L) :
    P L →ₐ[ℂ] P K :=
  ((restrictContinuous K L hKL).comp (algebra L).val).codRestrict (algebra K)
    (restrictContinuous_mem K L hKL)

@[simp] theorem restrict_apply (K L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace L]
    (hKL : K ⊆ L) (f : P L) (x : K) :
    (restrict K L hKL f).val x = f.val ⟨x.val, hKL x.property⟩ := rfl

@[simp] theorem restrict_polynomial (K L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace L]
    (hKL : K ⊆ L) (p : MvPolynomial σ ℂ) :
    restrict K L hKL (polynomial L p) = polynomial K p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  simp only [restrict_apply, polynomial_apply]

theorem norm_restrict_le (K L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace L]
    (hKL : K ⊆ L) (f : P L) : ‖restrict K L hKL f‖ ≤ ‖f‖ := by
  change ‖(restrict K L hKL f).val‖ ≤ ‖f.val‖
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  exact f.val.norm_coe_le_norm ⟨x.val, hKL x.property⟩

end AutomaticContinuity.PolynomialFunctionAlgebra
