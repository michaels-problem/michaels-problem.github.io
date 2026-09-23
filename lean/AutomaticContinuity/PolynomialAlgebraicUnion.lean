import AutomaticContinuity.PolynomialBezoutCutoff
import AutomaticContinuity.PolynomialConvexUnion

set_option autoImplicit false

/-!
# Polynomially convex unions separated by a finite polynomial zero set

The polynomial Bézout cutoff is small on K and exactly one on the entire
common zero set. It therefore supplies the cutoff required by the previously
proved compact-union theorem. The common zero set need not be compact.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialAlgebraicUnion

open Set MvPolynomial

theorem isPolynomiallyConvex_union {σ ι : Type*} [Fintype ι]
    {K L : Set (σ → ℂ)} (hKc : IsCompact K) (hLc : IsCompact L)
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (hL : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) L)
    (q : ι → MvPolynomial σ ℂ)
    (hKq : ∀ z ∈ K, ∃ i, eval z (q i) ≠ 0)
    (hLq : ∀ z ∈ L, ∀ i, eval z (q i) = 0) :
    IsPolynomiallyConvexOf (fun x : σ → ℂ => x) (K ∪ L) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  obtain ⟨r, hrK, hrZ⟩ := PolynomialBezoutCutoff.exists_polynomial_cutoff K hK q hKq
    (by norm_num : (0 : ℝ) < 1 / 8)
  apply PolynomialConvexUnion.isPolynomiallyConvexOf_union (fun x : σ → ℂ => x)
    continuous_id hKc hLc hK hL r (fun z hz => (hrK z hz).le)
  intro z hz
  rw [hrZ z (hLq z hz), sub_self, norm_zero]
  norm_num

end AutomaticContinuity.PolynomialAlgebraicUnion
