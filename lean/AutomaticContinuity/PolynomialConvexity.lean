import AutomaticContinuity.FiniteGeometry
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false

/-!
# Polynomial hulls and the coordinate polydisc

`polynomialHullOf e K` is the polynomial hull in the coordinates `e`, pulled
back to the source. Its definition uses all real upper bounds of a polynomial
on `K`; this avoids supremum conventions for the empty set. For the identity
coordinates on a finite complex vector space it is the usual polynomial hull.
For other coordinates no injectivity or geometric identification is assumed.

The elementary separation characterization connects explicit polynomial
witnesses to this definition. Closed polydiscs are polynomially convex by
coordinate separation. No holomorphic approximation theorem is used.
-/

noncomputable section

namespace AutomaticContinuity

universe u v

variable {X : Type u} {σ : Type v}

/-- The polynomial hull expressed through a specified coordinate map. -/
def polynomialHullOf (e : X → σ → ℂ) (K : Set X) : Set X :=
  {x | ∀ (p : MvPolynomial σ ℂ) (C : ℝ),
    (∀ y ∈ K, ‖MvPolynomial.eval (e y) p‖ ≤ C) → ‖MvPolynomial.eval (e x) p‖ ≤ C}

/-- Polynomial convexity with respect to the given coordinates. -/
def IsPolynomiallyConvexOf (e : X → σ → ℂ) (K : Set X) : Prop :=
  polynomialHullOf e K = K

theorem subset_polynomialHullOf (e : X → σ → ℂ) (K : Set X) :
    K ⊆ polynomialHullOf e K := by
  intro x hx p C hC
  exact hC x hx

theorem polynomialHullOf_mono (e : X → σ → ℂ) : Monotone (polynomialHullOf e) := by
  intro K L hKL x hx p C hC
  exact hx p C (fun y hy => hC y (hKL hy))

@[simp] theorem polynomialHullOf_idempotent (e : X → σ → ℂ) (K : Set X) :
    polynomialHullOf e (polynomialHullOf e K) = polynomialHullOf e K := by
  apply Set.Subset.antisymm
  · intro x hx p C hC
    exact hx p C (fun y hy => hy p C hC)
  · exact subset_polynomialHullOf e _

theorem not_mem_polynomialHullOf_iff (e : X → σ → ℂ) (K : Set X) (x : X) :
    x ∉ polynomialHullOf e K ↔
      ∃ (p : MvPolynomial σ ℂ) (C : ℝ),
        (∀ y ∈ K, ‖MvPolynomial.eval (e y) p‖ ≤ C) ∧
          C < ‖MvPolynomial.eval (e x) p‖ := by
  classical
  simp only [polynomialHullOf, Set.mem_ofPred_eq, not_forall, not_le, exists_prop]

theorem isPolynomiallyConvexOf_iff_separation (e : X → σ → ℂ) (K : Set X) :
    IsPolynomiallyConvexOf e K ↔
      ∀ x ∉ K, ∃ (p : MvPolynomial σ ℂ) (C : ℝ),
        (∀ y ∈ K, ‖MvPolynomial.eval (e y) p‖ ≤ C) ∧
          C < ‖MvPolynomial.eval (e x) p‖ := by
  constructor
  · intro h x hx
    apply (not_mem_polynomialHullOf_iff e K x).mp
    rwa [h]
  · intro h
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxK
      exact ((not_mem_polynomialHullOf_iff e K x).mpr (h x hxK)) hx
    · exact subset_polynomialHullOf e K

theorem isClosed_polynomialHullOf [TopologicalSpace X]
    (e : X → σ → ℂ) (he : Continuous e) (K : Set X) :
    IsClosed (polynomialHullOf e K) := by
  have heq : polynomialHullOf e K =
      ⋂ (p : MvPolynomial σ ℂ) (C : ℝ)
        (_hC : ∀ y ∈ K, ‖MvPolynomial.eval (e y) p‖ ≤ C),
          {x | ‖MvPolynomial.eval (e x) p‖ ≤ C} := by
    ext x
    simp only [polynomialHullOf, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter fun p => isClosed_iInter fun C => isClosed_iInter fun _hC =>
    isClosed_le ((MvPolynomial.continuous_eval p).comp he).norm continuous_const

/-- Closed coordinate polydiscs are polynomially convex, including dimension
zero and degenerate radii. The separating polynomial is a single coordinate. -/
theorem isPolynomiallyConvex_polydisc (n : ℕ) (R : ℝ) :
    IsPolynomiallyConvexOf (fun z : FinitePoint n => z) (polydisc n R) := by
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  change ¬ (∀ j : Fin n, ‖z j‖ ≤ R) at hz
  push Not at hz
  obtain ⟨j, hj⟩ := hz
  refine ⟨MvPolynomial.X j, R, ?_, ?_⟩
  · intro w hw
    simpa only [MvPolynomial.eval_X] using hw j
  · simpa only [MvPolynomial.eval_X] using hj

end AutomaticContinuity
