import AutomaticContinuity.SeparatedCapPolynomialCutoff
import AutomaticContinuity.ConvexProductPolynomialConvexity
import AutomaticContinuity.PlanarRotatedEscapeRays

set_option autoImplicit false

/-! # Unconditional polynomial cutoffs on compact separated coordinate caps

Enclose the compact set in an actual compact product of coordinate disks,
retaining the two separated caps in the distinguished coordinate. Escape
rays prove that larger product polynomially convex. Its polynomial cutoff
restricts to the original compact set. Arbitrarily many coordinates are
allowed; no polynomial-convexity assumption on the original set is needed.
-/

noncomputable section
namespace AutomaticContinuity.PolynomialFunctionAlgebra
open Set Metric Complex

theorem exists_polynomial_cap_cutoff_of_isCompact {σ : Type*}
    (K : Set (σ → ℂ)) (hK : IsCompact K)
    (j : σ) (a : ℂ) {c d : ℝ} (hcd : c < d)
    (hcaps : ∀ x ∈ K, (a*x j).re ≤ c ∨ d ≤ (a*x j).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℂ,
      (∀ x ∈ K, (a*x j).re ≤ c → ‖MvPolynomial.eval x p-1‖ < ε) ∧
      (∀ x ∈ K, d ≤ (a*x j).re → ‖MvPolynomial.eval x p‖ < ε) := by
  classical
  choose R hR using fun i : σ =>
    hK.exists_bound_of_continuousOn ((continuous_apply i).continuousOn)
  let D : σ → Set ℂ := fun i =>
    if i = j then PlanarEscapeRays.rotatedCaps (closedBall 0 (R i)) a c d
    else closedBall 0 (R i)
  have hD : ∀ i, IsCompact (D i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp only [D, ↓reduceIte, PlanarEscapeRays.rotatedCaps]
      exact ((isCompact_closedBall (0 : ℂ) (R j)).inter_right
        (isClosed_le (show Continuous (fun z : ℂ => (a*z).re) by fun_prop) continuous_const)).union
        ((isCompact_closedBall (0 : ℂ) (R j)).inter_right
          (isClosed_le continuous_const (show Continuous (fun z : ℂ => (a*z).re) by fun_prop)))
    · simp only [D, hij, ↓reduceIte]
      exact isCompact_closedBall _ _
  let W : Set (σ → ℂ) := {x | ∀ i, x i ∈ D i}
  have hW : IsCompact W := isCompact_pi_infinite hD
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  have hKW : K ⊆ W := by
    intro x hx i
    have hxi : x i ∈ closedBall (0 : ℂ) (R i) := by
      simpa only [mem_closedBall, dist_zero_right] using hR i x hx
    by_cases hij : i = j
    · subst i
      simp only [D, ↓reduceIte, PlanarEscapeRays.rotatedCaps, mem_union, mem_inter_iff,
        mem_ofPred_eq]
      exact (hcaps x hx).elim (fun h => Or.inl ⟨hxi,h⟩) (fun h => Or.inr ⟨hxi,h⟩)
    · simpa only [D, hij, ↓reduceIte] using hxi
  have hpoly : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) W := by
    apply isPolynomiallyConvex_of_product_escape W D (fun _ => Iff.rfl)
    intro i z hz
    by_cases hij : i = j
    · subst i
      simp only [D, ↓reduceIte] at hz ⊢
      exact PlanarEscapeRays.exists_escape_rotatedCaps (convex_closedBall (0 : ℂ) (R j)) a hz
    · simp only [D, hij, ↓reduceIte] at hz ⊢
      exact PlanarEscapeRays.exists_escape_convex (convex_closedBall (0 : ℂ) (R i)) hz
  have hWcaps : ∀ x ∈ W, (a*x j).re ≤ c ∨ d ≤ (a*x j).re := by
    intro x hx
    have hh := hx j
    simp only [D, ↓reduceIte, PlanarEscapeRays.rotatedCaps, mem_union, mem_inter_iff,
      mem_ofPred_eq] at hh
    exact hh.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨p, hp, hq⟩ := exists_polynomial_cap_cutoff W hpoly j a hcd hWcaps hε
  exact ⟨p, fun x hx => hp x (hKW hx), fun x hx => hq x (hKW hx)⟩

end AutomaticContinuity.PolynomialFunctionAlgebra
