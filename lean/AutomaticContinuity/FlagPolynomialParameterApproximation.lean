import AutomaticContinuity.FlagApproximationTransfer
import AutomaticContinuity.LocalFlagInterpolation

set_option autoImplicit false

/-! # Scalar two-piece polynomial approximation supplies the parameter input -/

noncomputable section

namespace AutomaticContinuity.FlagApproximationTransfer

open Set

theorem parameterApproximation_of_scalar_polynomials {n : ℕ}
    (K C : Set (FinitePoint n)) (φ θ : FinitePoint n → Pair)
    (hscalar : ∀ b : Bool, ∀ ε : ℝ, 0 < ε →
      ∃ p : MvPolynomial (Fin n) ℂ,
        (∀ z ∈ K, ‖MvPolynomial.eval z p - (if b then (φ z).2 else (φ z).1)‖ < ε) ∧
        (∀ z ∈ C, ‖MvPolynomial.eval z p - (if b then (θ z).2 else (θ z).1)‖ < ε)) :
    ParameterApproximation K C φ θ := by
  intro δ hδ
  obtain ⟨p, hpK, hpC⟩ := hscalar false (δ / 2) (half_pos hδ)
  obtain ⟨q, hqK, hqC⟩ := hscalar true (δ / 2) (half_pos hδ)
  refine ⟨fun z => (MvPolynomial.eval z p, MvPolynomial.eval z q),
    (differentiable_polynomial_eval p).prodMk (differentiable_polynomial_eval q), ?_, ?_⟩
  · intro z hz
    apply (euclideanPairNorm_le_sum _).trans
    change ‖MvPolynomial.eval z p - (φ z).1‖ + ‖MvPolynomial.eval z q - (φ z).2‖ ≤ δ
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (add_lt_add (hpK z hz) (hqK z hz)).le.trans_eq (by ring : δ / 2 + δ / 2 = δ)
  · intro z hz
    apply (euclideanPairNorm_le_sum _).trans
    change ‖MvPolynomial.eval z p - (θ z).1‖ + ‖MvPolynomial.eval z q - (θ z).2‖ ≤ δ
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (add_lt_add (hpC z hz) (hqC z hz)).le.trans_eq (by ring : δ / 2 + δ / 2 = δ)

end AutomaticContinuity.FlagApproximationTransfer
