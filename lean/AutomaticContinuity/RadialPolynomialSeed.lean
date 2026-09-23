import AutomaticContinuity.PolynomialFunctionAlgebra
import AutomaticContinuity.LocalPolydiscApproximation

set_option autoImplicit false

/-! # The polynomial seed for radial analytic continuation

Small complex dilations of a fixed compact set lie in a polydisc around the
chosen centre. The already checked local Cauchy expansion then gives actual
polynomials after affine substitution, and hence membership in `P(K)`.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set Metric Filter
open scoped Topology

def radialPolynomial {n : ℕ} (c : FinitePoint n) (t : ℂ)
    (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => MvPolynomial.C t * (MvPolynomial.X j - MvPolynomial.C (c j))) p

theorem eval_radialPolynomial {n : ℕ} (c z : FinitePoint n) (t : ℂ)
    (p : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.eval z (radialPolynomial c t p) =
      MvPolynomial.eval (t • (z-c)) p := by
  rw [radialPolynomial, MvPolynomial.eval_eval₂]
  have hc : (MvPolynomial.eval z).comp MvPolynomial.C = RingHom.id ℂ := by
    ext a
    simp
  rw [hc, MvPolynomial.eval₂_id]
  simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

theorem mem_algebra_of_small_radial_image {n : ℕ}
    (K : Set (FinitePoint n)) [CompactSpace K]
    (c : FinitePoint n) (t : ℂ) (f : FinitePoint n → ℂ) (F : C(K, ℂ))
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ (fun w => f (c+w)) (polydisc n R))
    (himage : ∀ x : K, t • (x.val-c) ∈ polydisc n r)
    (hF : ∀ x : K, F x = f (c+t•(x.val-c))) : F ∈ algebra K := by
  change F ∈ closure (Set.range (restriction K))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_of_differentiableOn
    hr hrR (fun w => f (c+w)) hf (half_pos hε)
  refine ⟨restriction K (radialPolynomial c t p), ⟨_, rfl⟩, ?_⟩
  have hb : ‖restriction K (radialPolynomial c t p) - F‖ ≤ ε/2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    simpa only [ContinuousMap.sub_apply, restriction_apply, eval_radialPolynomial, hF x]
      using (hp _ (himage x)).le
  simpa only [dist_eq_norm, norm_sub_rev] using hb.trans_lt (half_lt_self hε)

theorem eventually_mem_algebra_radial {n : ℕ}
    (K : Set (FinitePoint n)) (hK : IsCompact K) [CompactSpace K]
    (c : FinitePoint n) (f : FinitePoint n → ℂ)
    {U : Set (FinitePoint n)} (hU : IsOpen U) (hc : c ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (F : ℂ → C(K, ℂ))
    (hF : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x : K, F t x = f (c+t•(x.val-c))) :
    ∀ᶠ t in 𝓝 (0 : ℂ), F t ∈ algebra K := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU c hc
  let R : ℝ := δ/2
  let r : ℝ := δ/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r,R]; linarith
  have hshift : DifferentiableOn ℂ (fun w => f (c+w)) (polydisc n R) := by
    apply hf.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    apply hball
    change c+w ∈ ball c δ
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hn : ‖w‖ ≤ R := (pi_norm_le_iff_of_nonneg (by dsimp [R]; positivity)).mpr hw
    exact hn.trans_lt (by dsimp [R]; linarith)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((continuous_id.sub continuous_const).continuousOn : ContinuousOn (fun z => z-c) K)
  let B : ℝ := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hη : 0 < r/B := div_pos hr hB
  filter_upwards [hF, Metric.ball_mem_nhds (0 : ℂ) hη] with t ht htball
  apply mem_algebra_of_small_radial_image K c t f (F t) hr.le hrR hshift ?_ ht
  intro x j
  have ht' : ‖t‖ < r/B := by simpa only [mem_ball, dist_zero_right] using htball
  have hx : ‖x.val-c‖ ≤ B := (hM x.val x.property).trans (by dsimp [B]; linarith [le_max_left M 0])
  have hnorm : ‖t • (x.val-c)‖ < r := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg t)).trans_lt
      ((lt_div_iff₀ hB).mp ht')
  exact (norm_le_pi_norm _ j).trans hnorm.le

end AutomaticContinuity.PolynomialFunctionAlgebra
