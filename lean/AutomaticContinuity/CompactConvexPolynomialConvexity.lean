import AutomaticContinuity.CompactBaseFlagGeometry
import AutomaticContinuity.LocalPolydiscApproximation
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

/-! # Compact real-convex sets are polynomially convex

A complex Hahn--Banach functional separates an exterior point in real part.
Its exponential separates in modulus. Uniform approximation of this entire
function on one containing polydisc gives an actual polynomial separator.
-/

noncomputable section

namespace AutomaticContinuity

open Set

theorem isPolynomiallyConvexOf_compact_convex {n : ℕ}
    {K : Set (FinitePoint n)} (hK : IsCompact K) (hconv : Convex ℝ K) :
    IsPolynomiallyConvexOf (fun z : FinitePoint n => z) K := by
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  obtain ⟨l, u, hlK, hlz⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv hK.isClosed hz
  let f : FinitePoint n → ℂ := fun x => Complex.exp (l x)
  have hf : Differentiable ℂ f := Complex.differentiable_exp.comp l.differentiable
  have hgap : Real.exp u < Real.exp (l z).re := Real.exp_lt_exp.mpr hlz
  let ε : ℝ := (Real.exp (l z).re - Real.exp u) / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨R, hR, hKR⟩ := CompactBaseFlagGeometry.exists_containing_polydisc
    (hK.union (isCompact_singleton : IsCompact {z}))
  obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc hR f
    isOpen_univ (subset_univ _) hf.differentiableOn hε
  refine ⟨p, Real.exp u + ε, ?_, ?_⟩
  · intro x hx
    have he := hp x (hKR (Or.inl hx))
    have hfx : ‖f x‖ ≤ Real.exp u := by
      dsimp only [f]
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.mpr (hlK x hx)).le
    have hb : ‖MvPolynomial.eval x p‖ ≤ ‖MvPolynomial.eval x p - f x‖ + ‖f x‖ := by
      simpa using norm_add_le (MvPolynomial.eval x p - f x) (f x)
    linarith
  · have he := hp z (hKR (Or.inr rfl))
    have hb : ‖f z‖ ≤ ‖MvPolynomial.eval z p - f z‖ + ‖MvPolynomial.eval z p‖ := by
      have htri := norm_add_le (f z - MvPolynomial.eval z p) (MvPolynomial.eval z p)
      simpa only [sub_add_cancel, norm_sub_rev] using htri
    dsimp only [f] at hb
    rw [Complex.norm_exp] at hb
    dsimp only [ε] at he ⊢
    linarith

end AutomaticContinuity
