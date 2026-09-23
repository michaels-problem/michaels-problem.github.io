import AutomaticContinuity.PolynomialBezoutCutoff
import AutomaticContinuity.PolynomialConvexUnion
import AutomaticContinuity.PolynomialRestrictionMap

set_option autoImplicit false

/-!
# Polynomial cutoffs from uniformly approximable functions

A finite family of actual functions in the closed polynomial algebra, with no
common zero on a polynomially convex compact and vanishing on a second set,
produces a genuine polynomial cutoff. The proof uses a Banach-algebra Bézout
identity and density twice. It assumes no approximation theorem for arbitrary
holomorphic functions.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionCutoff

open Set PolynomialFunctionAlgebra
open scoped BigOperators

universe u v
variable {σ : Type u} {ι : Type v} [Fintype ι]

/-- The function-algebra form of the cutoff construction. Compatibility means
the two listed functions are restrictions of the same actual function. -/
theorem exists_polynomial_cutoff_of_compatible
    (K S L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace S]
    (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (aK : ι → P K) (aS : ι → P S)
    (hcompat : ∀ i (x : K), (aK i).val x = (aS i).val ⟨x.val, hKS x.property⟩)
    (hzeroK : ∀ x : K, ∃ i, (aK i).val x ≠ 0)
    (hzeroL : ∀ i (x : L), (aS i).val ⟨x.val, hLS x.property⟩ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      (∀ x ∈ K, ‖MvPolynomial.eval x q‖ < ε) ∧
      ∀ x ∈ L, ‖MvPolynomial.eval x q - 1‖ < ε := by
  classical
  have hnz : ∀ η : P K →ₐ[ℂ] ℂ, ∃ i, η (aK i) ≠ 0 := by
    intro η
    obtain ⟨x, hx⟩ := character_eq_evaluation K hK η
    obtain ⟨i, hi⟩ := hzeroK x
    exact ⟨i, by simpa only [hx] using hi⟩
  obtain ⟨b, hb⟩ := PolynomialBezoutCutoff.exists_small_residual aK
    (polynomial K) (denseRange_polynomial K) hnz (half_pos hε)
  let rK : P K := 1 - ∑ i, aK i * polynomial K (b i)
  let rS : P S := 1 - ∑ i, aS i * polynomial S (b i)
  have hrK : ‖rK‖ < ε / 2 := hb
  have hrcompat : ∀ x : K, rK.val x = rS.val ⟨x.val, hKS x.property⟩ := by
    intro x
    simp [rK, rS, hcompat, polynomial_apply]
  have hrL : ∀ x : L, rS.val ⟨x.val, hLS x.property⟩ = 1 := by
    intro x
    simp [rS, hzeroL, polynomial_apply]
  obtain ⟨q, hq⟩ := exists_polynomial_approx S rS (half_pos hε)
  have hqpoint : ∀ x : S, ‖MvPolynomial.eval x.val q - rS.val x‖ < ε / 2 := by
    intro x
    have hbnd := ContinuousMap.norm_coe_le_norm (polynomial S q - rS).val x
    have hbnd' : ‖MvPolynomial.eval x.val q - rS.val x‖ ≤
        ‖polynomial S q - rS‖ := by
      change ‖MvPolynomial.eval x.val q - rS.val x‖ ≤
        ‖(polynomial S q - rS).val‖
      simpa only [Subalgebra.coe_sub, ContinuousMap.sub_apply, polynomial_apply] using hbnd
    exact hbnd'.trans_lt hq
  refine ⟨q, ?_, ?_⟩
  · intro x hx
    have hsmall := (ContinuousMap.norm_coe_le_norm rK.val (⟨x, hx⟩ : K)).trans_lt hrK
    have hdiff := hqpoint (⟨x, hKS hx⟩ : S)
    rw [← hrcompat (⟨x, hx⟩ : K)] at hdiff
    have ht := norm_add_le (MvPolynomial.eval x q - rK.val ⟨x, hx⟩) (rK.val ⟨x, hx⟩)
    rw [sub_add_cancel] at ht
    linarith
  · intro x hx
    have hh := hqpoint (⟨x, hLS hx⟩ : S)
    rw [hrL (⟨x, hx⟩ : L)] at hh
    linarith

/-- A cutoff from a single family in the polynomial algebra on the ambient
compact set. -/
theorem exists_polynomial_cutoff
    (K S L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace S]
    (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (a : ι → P S)
    (hzeroK : ∀ x : K, ∃ i, (a i).val ⟨x.val, hKS x.property⟩ ≠ 0)
    (hzeroL : ∀ i (x : L), (a i).val ⟨x.val, hLS x.property⟩ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      (∀ x ∈ K, ‖MvPolynomial.eval x q‖ < ε) ∧
      ∀ x ∈ L, ‖MvPolynomial.eval x q - 1‖ < ε := by
  exact exists_polynomial_cutoff_of_compatible K S L hKS hLS hK
    (fun i => restrict K S hKS (a i)) a
    (fun _ _ => rfl) hzeroK hzeroL hε

/-- Uniform approximability of the given finite functions is the entire
approximation premise; no holomorphic approximation principle is implicit. -/
theorem exists_polynomial_cutoff_of_approx
    (K S L : Set (σ → ℂ)) [CompactSpace K] [CompactSpace S]
    (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (a : ι → C(S, ℂ))
    (happrox : ∀ i ε, 0 < ε → ∃ p : MvPolynomial σ ℂ,
      ∀ x : S, ‖MvPolynomial.eval x.val p - a i x‖ < ε)
    (hzeroK : ∀ x : K, ∃ i, a i ⟨x.val, hKS x.property⟩ ≠ 0)
    (hzeroL : ∀ i (x : L), a i ⟨x.val, hLS x.property⟩ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      (∀ x ∈ K, ‖MvPolynomial.eval x q‖ < ε) ∧
      ∀ x ∈ L, ‖MvPolynomial.eval x q - 1‖ < ε := by
  exact exists_polynomial_cutoff K S L hKS hLS hK
    (fun i => ⟨a i, mem_algebra_of_approx S (a i) (happrox i)⟩)
    hzeroK hzeroL hε

end AutomaticContinuity.PolynomialFunctionCutoff
