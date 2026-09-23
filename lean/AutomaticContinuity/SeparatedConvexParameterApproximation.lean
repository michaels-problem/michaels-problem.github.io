import AutomaticContinuity.SeparatedCapPolynomialGluing
import AutomaticContinuity.CompactSeparatedCapCutoff
import AutomaticContinuity.ConvexPolynomialApproximation
import AutomaticContinuity.FlagPolynomialParameterApproximation

set_option autoImplicit false

/-! # Actual parameter approximation on separated compact convex pieces

Convex Runge approximation supplies the two local polynomials. The proved
compact cap cutoff combines them. This discharges the parameter-approximation
input of the additive approximation transfer for this concrete geometry.
-/

noncomputable section

namespace AutomaticContinuity.SeparatedCapPolynomialGluing

open Set PolynomialFunctionAlgebra

theorem exists_polynomial_approx_on_separated_convex {n : ℕ}
    {K₀ K₁ U₀ U₁ : Set (FinitePoint n)}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hconv₀ : Convex ℝ K₀) (hconv₁ : Convex ℝ K₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hsub₀ : K₀ ⊆ U₀) (hsub₁ : K₁ ⊆ U₁)
    (j : Fin n) (a : ℂ) {c d : ℝ} (hcd : c < d)
    (hsep₀ : ∀ x ∈ K₀, (a*x j).re ≤ c) (hsep₁ : ∀ x ∈ K₁, d ≤ (a*x j).re)
    (f₀ f₁ : FinitePoint n → ℂ)
    (hf₀ : DifferentiableOn ℂ f₀ U₀) (hf₁ : DifferentiableOn ℂ f₁ U₁)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      (∀ x ∈ K₀, ‖MvPolynomial.eval x p-f₀ x‖ < ε) ∧
      (∀ x ∈ K₁, ‖MvPolynomial.eval x p-f₁ x‖ < ε) := by
  apply exists_polynomial_approx_of_cutoff hK₀ hK₁ f₀ f₁
    (fun η hη ↦ exists_polynomial_approx_on_convex hK₀ hconv₀ hU₀ hsub₀ f₀ hf₀ hη)
    (fun η hη ↦ exists_polynomial_approx_on_convex hK₁ hconv₁ hU₁ hsub₁ f₁ hf₁ hη) _ hε
  intro η hη
  have hcaps : ∀ x ∈ K₀ ∪ K₁, (a*x j).re ≤ c ∨ d ≤ (a*x j).re := by
    intro x hx
    exact hx.elim (fun h ↦ Or.inl (hsep₀ x h)) (fun h ↦ Or.inr (hsep₁ x h))
  obtain ⟨q,hq₀,hq₁⟩ := exists_polynomial_cap_cutoff_of_isCompact
    (K₀ ∪ K₁) (hK₀.union hK₁) j a hcd hcaps hη
  exact ⟨q,fun x hx ↦ hq₀ x (Or.inl hx) (hsep₀ x hx),
    fun x hx ↦ hq₁ x (Or.inr hx) (hsep₁ x hx)⟩

/-- A globally entire pair map approximates the two holomorphic parameter
maps with the exact Euclidean norm requested by `ParameterApproximation`. -/
theorem parameterApproximation_of_separated_convex {n : ℕ}
    {K₀ K₁ U₀ U₁ : Set (FinitePoint n)}
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hconv₀ : Convex ℝ K₀) (hconv₁ : Convex ℝ K₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hsub₀ : K₀ ⊆ U₀) (hsub₁ : K₁ ⊆ U₁)
    (j : Fin n) (a : ℂ) {c d : ℝ} (hcd : c < d)
    (hsep₀ : ∀ x ∈ K₀, (a*x j).re ≤ c) (hsep₁ : ∀ x ∈ K₁, d ≤ (a*x j).re)
    (φ θ : FinitePoint n → ℂ × ℂ)
    (hφ : DifferentiableOn ℂ φ U₀) (hθ : DifferentiableOn ℂ θ U₁) :
    FlagApproximationTransfer.ParameterApproximation K₀ K₁ φ θ := by
  apply FlagApproximationTransfer.parameterApproximation_of_scalar_polynomials K₀ K₁ φ θ
  intro b ε hε
  apply exists_polynomial_approx_on_separated_convex hK₀ hK₁ hconv₀ hconv₁
    hU₀ hU₁ hsub₀ hsub₁ j a hcd hsep₀ hsep₁ _ _ _ _ hε
  · cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact hφ.fst
    · exact hφ.snd
  · cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact hθ.fst
    · exact hθ.snd

end AutomaticContinuity.SeparatedCapPolynomialGluing
