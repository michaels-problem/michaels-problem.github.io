import AutomaticContinuity.LocalCauchyExpansion
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Uniform polynomial approximation on a closed finite polydisc

The polynomials are finite truncations of genuine iterated Cauchy coefficients.
The proof uses the summable geometric majorant at any ratio `r / R < 1`.
Tietze extension is used only to supply an auxiliary globally continuous function;
the extension equals the original function on the whole outer polydisc, so local
differentiability and the approximation target are preserved.

This is scalar polynomial approximation on polydiscs. It does not assert Oka
approximation or preserve avoidance on noncompact affine flags.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set Filter
open scoped BigOperators Real Topology

/-- A finite polynomial consisting of a chosen finite collection of actual
contour coefficients. -/
def coefficientPolynomial {n : ℕ} (R : ℝ) (h : FinitePoint n → ℂ)
    (s : Finset (FiniteMultiIndex n)) : MvPolynomial (Fin n) ℂ :=
  ∑ α ∈ s, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α)
    (coefficient (fun _ => R) h α)

@[simp] theorem eval_coefficientPolynomial {n : ℕ} (R : ℝ) (h : FinitePoint n → ℂ)
    (s : Finset (FiniteMultiIndex n)) (z : FinitePoint n) :
    MvPolynomial.eval z (coefficientPolynomial R h s) =
      ∑ α ∈ s, coefficient (fun _ => R) h α * monomial z α := by
  simp [coefficientPolynomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype, monomial]

/-- Uniform convergence of finite contour-coefficient truncations on every
strictly smaller closed polydisc. -/
theorem tendstoUniformlyOn_coefficientPolynomial {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (h : FinitePoint n → ℂ)
    (hhc : Continuous h) (hhd : DifferentiableOn ℂ h (polydisc n R)) :
    TendstoUniformlyOn
      (fun s : Finset (FiniteMultiIndex n) => fun z =>
        MvPolynomial.eval z (coefficientPolynomial R h s)) h atTop (polydisc n r) := by
  have hR : 0 < R := hr.trans_lt hrR
  obtain ⟨M, hM⟩ := ((isCompact_polydisc n hR.le).image hhc.norm).bddAbove
  have hbound : ∀ w ∈ polydisc n R, ‖h w‖ ≤ max M 0 := by
    intro w hw
    exact (hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  have hmajorant : Summable (fun α : FiniteMultiIndex n =>
      max M 0 * (r / R) ^ finiteTotalDegree α) :=
    (hasSum_ratio_pow_finiteTotalDegree n (div_nonneg hr hR.le)
      ((div_lt_one hR).mpr hrR)).summable.mul_left _
  have hu := tendstoUniformlyOn_tsum hmajorant
    (fun α z hz => norm_coefficient_mul_monomial_le_ratio hr hR h hbound z hz α)
  have heq : EqOn (fun z => ∑' α, coefficient (fun _ => R) h α * monomial z α)
      h (polydisc n r) := by
    intro z hz
    exact (hasSum_coefficient_mul_monomial_local_of_bound hr hrR (le_max_right M 0)
      h hhc hhd hbound z hz).tsum_eq
  simpa only [eval_coefficientPolynomial] using hu.congr_right heq

theorem exists_polynomial_approx_of_continuous_differentiableOn {n : ℕ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (h : FinitePoint n → ℂ)
    (hhc : Continuous h) (hhd : DifferentiableOn ℂ h (polydisc n R)) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z p - h z‖ < ε := by
  have hu := tendstoUniformlyOn_coefficientPolynomial hr hrR h hhc hhd
  obtain ⟨s, hs⟩ := ((Metric.tendstoUniformlyOn_iff.mp hu) ε hε).exists
  refine ⟨coefficientPolynomial R h s, ?_⟩
  intro z hz
  simpa only [dist_eq_norm, norm_sub_rev] using hs z hz

/-- Local differentiability on an outer closed polydisc suffices for uniform
polynomial approximation on a smaller one. There is no global regularity
assumption on the original function. -/
theorem exists_polynomial_approx_of_differentiableOn {n : ℕ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (h : FinitePoint n → ℂ)
    (hhd : DifferentiableOn ℂ h (polydisc n R)) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z p - h z‖ < ε := by
  have hR : 0 < R := hr.trans_lt hrR
  let f : C(polydisc n R, ℂ) := ⟨fun z => h z, hhd.continuousOn.domRestrict⟩
  obtain ⟨g, hg⟩ := f.exists_restrict_eq (isCompact_polydisc n hR.le).isClosed
  have heq : ∀ z ∈ polydisc n R, g z = h z := by
    intro z hz
    exact congrArg (fun k : C(polydisc n R, ℂ) => k ⟨z, hz⟩) hg
  have hgdiff : DifferentiableOn ℂ g (polydisc n R) := hhd.congr heq
  obtain ⟨p, hp⟩ := exists_polynomial_approx_of_continuous_differentiableOn
    hr hrR g g.continuous hgdiff hε
  refine ⟨p, ?_⟩
  intro z hz
  have hzR : z ∈ polydisc n R := fun j => (hz j).trans hrR.le
  simpa only [heq z hzR] using hp z hz

/-- The usual explicit-radius form: holomorphicity on the open outer
polydisc yields polynomial approximation on a strictly smaller closed one. -/
theorem exists_polynomial_approx_of_differentiableOn_openPolydisc {n : ℕ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (h : FinitePoint n → ℂ)
    (hhd : DifferentiableOn ℂ h {z | ∀ j, ‖z j‖ < R}) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z p - h z‖ < ε := by
  apply exists_polynomial_approx_of_differentiableOn hr (show r < (r + R) / 2 by linarith) h
  · apply hhd.mono
    intro z hz j
    exact (hz j).trans_lt (by linarith : (r + R) / 2 < R)
  · exact hε

/-- A compact polydisc contained in an open set is contained in a slightly
larger closed polydisc that still lies in the same open set. -/
theorem exists_larger_polydisc_subset {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {U : Set (FinitePoint n)} (hU : IsOpen U) (hsub : polydisc n r ⊆ U) :
    ∃ R : ℝ, r < R ∧ polydisc n R ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_polydisc n hr).exists_cthickening_subset_open hU hsub
  refine ⟨δ + r, by linarith, ?_⟩
  have heq : cthickening δ (polydisc n r) = polydisc n (δ + r) := by
    rw [polydisc_eq_closedBall n hr, cthickening_closedBall hδ.le hr,
      polydisc_eq_closedBall n (add_nonneg hδ.le hr)]
  rwa [← heq]

/-- Uniform polynomial approximation of a scalar function holomorphic on an
arbitrary open neighbourhood of the closed polydisc. -/
theorem exists_polynomial_approx_on_polydisc {n : ℕ} {r ε : ℝ} (hr : 0 ≤ r)
    (h : FinitePoint n → ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hsub : polydisc n r ⊆ U) (hhd : DifferentiableOn ℂ h U) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z p - h z‖ < ε := by
  obtain ⟨R, hrR, hRU⟩ := exists_larger_polydisc_subset hr hU hsub
  exact exists_polynomial_approx_of_differentiableOn hr hrR h (hhd.mono hRU) hε

end AutomaticContinuity.FiniteCauchy
