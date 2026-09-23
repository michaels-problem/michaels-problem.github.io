import AutomaticContinuity.CenteredSeparatorData
import AutomaticContinuity.FlagPolynomialSeparation

set_option autoImplicit false

/-!
# Centering in the actual flag source/target coordinates

This specializes the separator-to-radial-data construction to the exact
`Fin n ⊕ Bool` coordinate convention used by the flag-graph cutoff theorems.
The conclusion contains an actual two-variable polynomial family.
-/

noncomputable section

namespace AutomaticContinuity.FlagCenteredSeparator

open FlagPolynomialSeparation CenteredPolynomialFamily Set FlagTotalSpace

def fiberIndex (b : Bool) : Fin 2 := if b then 1 else 0

def polynomial {n : ℕ} (q : Polynomial n) (h : FinitePoint n → ℂ × ℂ)
    (p : FinitePoint n) : PolynomialFamilyRegularity.Poly :=
  centered q fiberIndex (fun p => p) (sectionCoordinates fiberIndex h) p

def value {n : ℕ} (q : Polynomial n) (h : FinitePoint n → ℂ × ℂ) (z : Point n) : ℂ :=
  centeredValue q fiberIndex (fun p => p) (sectionCoordinates fiberIndex h) z

theorem value_eq_eval {n : ℕ} (q : Polynomial n) (h : FinitePoint n → ℂ × ℂ) (z : Point n) :
    value q h z = MvPolynomial.eval ![z.2.1, z.2.2] (polynomial q h z.1) := rfl

theorem originalValue_eq_evaluate {n : ℕ} (q : Polynomial n) (z : Point n) :
    originalValue q fiberIndex (fun p => p) z = evaluate z q := by
  apply congrArg (fun x => MvPolynomial.eval x q)
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> rfl

theorem value_centerMap {n : ℕ} (q : Polynomial n) (h : FinitePoint n → ℂ × ℂ)
    (z : Point n) : value q h (centerMap h z) = evaluate z q := by
  exact (centeredValue_centerMap q fiberIndex (fun p => p) h z).trans
    (originalValue_eq_evaluate q z)

theorem totalDegree_polynomial_le {n : ℕ} (q : Polynomial n) (h : FinitePoint n → ℂ × ℂ)
    (p : FinitePoint n) : (polynomial q h p).totalDegree ≤ q.totalDegree :=
  totalDegree_centered_le q fiberIndex (fun p => p) (sectionCoordinates fiberIndex h) p

theorem continuousCoefficientsOn_polynomial {n : ℕ} (q : Polynomial n)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hh : ContinuousOn h U) :
    PolynomialFamilyRegularity.ContinuousCoefficientsOn (polynomial q h) U :=
  continuousCoefficientsOn_section_centered q fiberIndex (fun p => p) h
    (fun i => (continuous_apply i).continuousOn) hh

theorem holomorphicCoefficientsOn_polynomial {n : ℕ} (q : Polynomial n)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hh : DifferentiableOn ℂ h U) :
    PolynomialFamilyRegularity.HolomorphicCoefficientsOn (polynomial q h) U :=
  holomorphicCoefficientsOn_section_centered q fiberIndex (fun p => p) h
    (fun i => (differentiable_apply i).differentiableOn) hh

/-- The initial compact data for a radial push, in the actual flag-coordinate
encoding. The polynomial `q` can be supplied by the existing graph cutoff
construction at tolerance `1/32`. -/
theorem exists_separator_data {n : ℕ} (q : Polynomial n)
    (h : FinitePoint n → ℂ × ℂ)
    {L U : Set (FinitePoint n)} {K : Set (Point n)}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ) (hh : ContinuousOn h U)
    (hgraph : ∀ p ∈ L, ‖evaluate (p, h p) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖evaluate z q - 1‖ ≤ 1 / 32) :
    ∃ a : ℝ, 0 < a ∧ IsCompact (centeredObstacle h K) ∧
      centeredObstacle h K ⊆ L ×ˢ univ ∧
      (∀ z ∈ L ×ˢ closedEuclideanBall a, ‖value q h z‖ ≤ 1 / 16) ∧
      (∀ z ∈ centeredObstacle h K, ‖value q h z - 1‖ ≤ 1 / 32) ∧
      (∀ z ∈ centeredObstacle h K, a < euclideanPairNorm z.2) := by
  apply exists_centered_separator_data q fiberIndex (fun p => p) h hL hK hU hLU hKL
    (fun i => (continuous_apply i).continuousOn) hh
  · intro p hp
    change ‖originalValue q fiberIndex (fun p => p) (p, h p)‖ ≤ 1 / 32
    rw [originalValue_eq_evaluate]
    exact hgraph p hp
  · simpa only [originalValue_eq_evaluate] using hobstacle

end AutomaticContinuity.FlagCenteredSeparator
