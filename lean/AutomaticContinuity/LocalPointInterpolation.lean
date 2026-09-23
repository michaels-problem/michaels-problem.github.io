import AutomaticContinuity.LocalPolydiscApproximation
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

/-!
# Polynomial approximation with interpolation at an exterior point

A point outside a coordinate polydisc admits polynomial peaks that take value
one there and are arbitrarily small on the polydisc. Correcting an approximating
polynomial by such a peak gives an arbitrary exact value at the exterior point.
This supplies the new-point interpolation part of the flag problem, without
claiming preservation of the bounds on the other, unbounded affine flags.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

theorem exists_polynomial_peak {n : ℕ} {r δ : ℝ} (hr : 0 ≤ r)
    {a : FinitePoint n} (ha : a ∉ polydisc n r) (hδ : 0 < δ) :
    ∃ q : MvPolynomial (Fin n) ℂ, MvPolynomial.eval a q = 1 ∧
      ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z q‖ < δ := by
  classical
  change ¬ ∀ j : Fin n, ‖a j‖ ≤ r at ha
  obtain ⟨j, hj⟩ := not_forall.mp ha
  have hja : r < ‖a j‖ := lt_of_not_ge hj
  have hjpos : 0 < ‖a j‖ := hr.trans_lt hja
  have hjne : a j ≠ 0 := norm_pos_iff.mp hjpos
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ ((div_lt_one hjpos).mpr hja)
  refine ⟨(MvPolynomial.C ((a j)⁻¹) * MvPolynomial.X j) ^ m, ?_, ?_⟩
  · simp [hjne]
  · intro z hz
    simp only [map_pow, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      norm_pow, norm_mul, norm_inv]
    apply lt_of_le_of_lt _ hm
    apply pow_le_pow_left₀ (by positivity)
    rw [div_eq_mul_inv, mul_comm r]
    exact mul_le_mul_of_nonneg_left (hz j) (by positivity)

/-- Uniform scalar polynomial approximation on a polydisc with an arbitrary
exact value at one exterior point. -/
theorem exists_polynomial_approx_interpolate_exterior {n : ℕ} {r ε : ℝ}
    (hr : 0 ≤ r) (h : FinitePoint n → ℂ) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hsub : polydisc n r ⊆ U) (hhd : DifferentiableOn ℂ h U)
    (hε : 0 < ε) {a : FinitePoint n} (ha : a ∉ polydisc n r) (v : ℂ) :
    ∃ p : MvPolynomial (Fin n) ℂ, MvPolynomial.eval a p = v ∧
      ∀ z ∈ polydisc n r, ‖MvPolynomial.eval z p - h z‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_approx_on_polydisc hr h hU hsub hhd (half_pos hε)
  let c : ℂ := v - MvPolynomial.eval a p
  by_cases hc : c = 0
  · refine ⟨p, ?_, ?_⟩
    · exact (sub_eq_zero.mp hc).symm
    · intro z hz
      exact (hp z hz).trans (half_lt_self hε)
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    obtain ⟨q, hqa, hq⟩ := exists_polynomial_peak hr ha (div_pos (half_pos hε) hcpos)
    refine ⟨p + MvPolynomial.C c * q, ?_, ?_⟩
    · simp only [map_add, map_mul, MvPolynomial.eval_C, hqa, mul_one]
      dsimp [c]
      ring
    · intro z hz
      have hsmall : ‖c * MvPolynomial.eval z q‖ < ε / 2 := by
        rw [norm_mul]
        calc
          _ < ‖c‖ * ((ε / 2) / ‖c‖) := mul_lt_mul_of_pos_left (hq z hz) hcpos
          _ = ε / 2 := mul_div_cancel₀ _ hcpos.ne'
      simp only [map_add, map_mul, MvPolynomial.eval_C]
      have htriangle := norm_add_le (MvPolynomial.eval z p - h z)
        (c * MvPolynomial.eval z q)
      have hrewrite : MvPolynomial.eval z p + c * MvPolynomial.eval z q - h z =
          (MvPolynomial.eval z p - h z) + c * MvPolynomial.eval z q := by ring
      rw [hrewrite]
      exact htriangle.trans_lt (by linarith [hp z hz])

end AutomaticContinuity.FiniteCauchy
