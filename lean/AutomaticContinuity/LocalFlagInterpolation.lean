import AutomaticContinuity.LocalPolydiscApproximation

/-!
# Entire approximation with exact interpolation on a coordinate flag

The affine projection onto the chosen flag must preserve the approximation
polydisc. For the prescribed coordinates a sufficient condition is `4*k ≤ R`.
Given an entire map supplying the prescribed flag values, subtract its pullback,
approximate the difference by a polynomial, and subtract the polynomial's
pullback as well. This gives exact interpolation and controlled compact error.

No lower bound is preserved on other noncompact flags. This elementary result
does not assert the unresolved flag-avoidance approximation theorem.
-/

noncomputable section

namespace AutomaticContinuity

open Set

/-- Replace precisely the initial `k` coordinates by their prescribed values. -/
def flagProjection (n k : ℕ) (z : FinitePoint n) : FinitePoint n :=
  fun j => if j.val < k then prescribedCoordinate j.val else z j

theorem flagProjection_mem (n k : ℕ) (z : FinitePoint n) :
    flagProjection n k z ∈ finiteFlag n k := by
  intro j hj
  simp [flagProjection, hj]

theorem flagProjection_eq_self {n k : ℕ} {z : FinitePoint n}
    (hz : z ∈ finiteFlag n k) : flagProjection n k z = z := by
  funext j
  by_cases hj : j.val < k
  · simp [flagProjection, hj, hz j hj]
  · simp [flagProjection, hj]

@[simp] theorem flagProjection_idempotent (n k : ℕ) (z : FinitePoint n) :
    flagProjection n k (flagProjection n k z) = flagProjection n k z :=
  flagProjection_eq_self (flagProjection_mem n k z)

theorem differentiable_flagProjection (n k : ℕ) :
    Differentiable ℂ (flagProjection n k) := by
  apply differentiable_pi.mpr
  intro j
  by_cases hj : j.val < k
  · simpa only [flagProjection, ite_eq_left hj] using
      (differentiable_const (prescribedCoordinate j.val) :
        Differentiable ℂ (fun _ : FinitePoint n => prescribedCoordinate j.val))
  · simpa only [flagProjection, ite_eq_right hj] using
      (differentiable_apply j : Differentiable ℂ (fun z : FinitePoint n => z j))

theorem flagProjection_maps_polydisc {n k : ℕ} {R : ℝ}
    (hR : ∀ j : Fin n, j.val < k → ‖prescribedCoordinate j.val‖ ≤ R) :
    MapsTo (flagProjection n k) (polydisc n R) (polydisc n R) := by
  intro z hz j
  by_cases hj : j.val < k
  · simpa only [flagProjection, ite_eq_left hj] using hR j hj
  · simpa only [flagProjection, ite_eq_right hj] using hz j

/-- A sufficient radius condition for the projection-preserves-polydisc
hypothesis; it also handles the zero-length flag. -/
theorem flagProjection_maps_polydisc_of_four_mul_le {n k : ℕ} {R : ℝ}
    (hkR : 4 * (k : ℝ) ≤ R) :
    MapsTo (flagProjection n k) (polydisc n R) (polydisc n R) := by
  apply flagProjection_maps_polydisc
  intro j hj
  rw [norm_prescribedCoordinate]
  have hjk : (j.val : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
  linarith

theorem differentiable_polynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun z : FinitePoint n => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (differentiable_const c)
  | add p q hp hq =>
      convert! hp.add hq using 1
      ext z
      simp
  | mul_X p j hp =>
      convert! hp.mul (differentiable_apply j) using 1
      ext z
      simp

/-- Scalar entire approximation with exact interpolation on one coordinate flag.
The entire ambient function `G` supplies the prescribed values on that flag. -/
theorem exists_entire_approx_interpolating_flag {n k : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hproj : MapsTo (flagProjection n k) (polydisc n R) (polydisc n R))
    (h G : FinitePoint n → ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hG : Differentiable ℂ G) (hagree : EqOn h G (finiteFlag n k)) :
    ∃ H : FinitePoint n → ℂ,
      Differentiable ℂ H ∧ EqOn H G (finiteFlag n k) ∧
        ∀ z ∈ polydisc n R, ‖H z - h z‖ < ε := by
  let d : FinitePoint n → ℂ := fun z => h z - G (flagProjection n k z)
  have hd : DifferentiableOn ℂ d U :=
    hh.sub (hG.comp (differentiable_flagProjection n k)).differentiableOn
  have hdproj (z : FinitePoint n) : d (flagProjection n k z) = 0 := by
    simp only [d, flagProjection_idempotent, hagree (flagProjection_mem n k z), sub_self]
  obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc
    hR d hU hKU hd (show 0 < ε / 2 by positivity)
  let H : FinitePoint n → ℂ := fun z => G (flagProjection n k z) +
    MvPolynomial.eval z p - MvPolynomial.eval (flagProjection n k z) p
  refine ⟨H, ?_, ?_, ?_⟩
  · exact ((hG.comp (differentiable_flagProjection n k)).add
      (differentiable_polynomial_eval p)).sub
        ((differentiable_polynomial_eval p).comp (differentiable_flagProjection n k))
  · intro z hz
    simp [H, flagProjection_eq_self hz]
  · intro z hz
    have hpz := hp z hz
    have hpp := hp (flagProjection n k z) (hproj hz)
    rw [hdproj, sub_zero] at hpp
    have heq : H z - h z = (MvPolynomial.eval z p - d z) -
        MvPolynomial.eval (flagProjection n k z) p := by
      dsimp [H, d]
      ring
    rw [heq]
    exact (norm_sub_le _ _).trans_lt (by linarith)

/-- The pair-valued interpolation theorem uses the manuscript's Euclidean norm
explicitly, with the scalar approximation tolerances split between components. -/
theorem exists_entire_pair_approx_interpolating_flag {n k : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hproj : MapsTo (flagProjection n k) (polydisc n R) (polydisc n R))
    (h G : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hG : Differentiable ℂ G) (hagree : EqOn h G (finiteFlag n k)) :
    ∃ H : FinitePoint n → ℂ × ℂ,
      Differentiable ℂ H ∧ EqOn H G (finiteFlag n k) ∧
        ∀ z ∈ polydisc n R, euclideanPairNorm (H z - h z) < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨f, hf, hfFlag, hfApprox⟩ := exists_entire_approx_interpolating_flag
    hR hhalf hproj (fun z => (h z).1) (fun z => (G z).1) hU hKU hh.fst hG.fst
    (fun z hz => congrArg Prod.fst (hagree hz))
  obtain ⟨g, hg, hgFlag, hgApprox⟩ := exists_entire_approx_interpolating_flag
    hR hhalf hproj (fun z => (h z).2) (fun z => (G z).2) hU hKU hh.snd hG.snd
    (fun z hz => congrArg Prod.snd (hagree hz))
  refine ⟨fun z => (f z, g z), hf.prodMk hg, ?_, ?_⟩
  · intro z hz
    exact Prod.ext (hfFlag hz) (hgFlag hz)
  · intro z hz
    refine (euclideanPairNorm_le_sum _).trans_lt ?_
    change ‖f z - (h z).1‖ + ‖g z - (h z).2‖ < ε
    linarith [hfApprox z hz, hgApprox z hz]

end AutomaticContinuity
