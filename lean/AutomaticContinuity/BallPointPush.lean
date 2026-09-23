import AutomaticContinuity.PolynomialShears
import AutomaticContinuity.EuclideanPairRotations

set_option autoImplicit false

/-!
# Small holomorphic automorphisms pushing one point away from a ball

A unitary coordinate change and one polynomial shear move any exterior point
beyond any prescribed radius. Both the automorphism and its actual inverse
remain arbitrarily close to the identity on the protected Euclidean ball.
This is a pointwise construction, not approximation of an arbitrary compact
set or a holomorphic family of such constructions.
-/

noncomputable section

namespace AutomaticContinuity.BallPointPush

open PolynomialShears EuclideanPairRotations

theorem exists_small_shear_both_directions {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (a b c : ℂ) (ha : R < ‖a‖) :
    ∃ s : (ℂ × ℂ) ≃ₜ (ℂ × ℂ),
      Differentiable ℂ s ∧ Differentiable ℂ s.symm ∧ s (a, b) = (a, c) ∧
      ∀ z : ℂ × ℂ, ‖z.1‖ ≤ R →
        euclideanPairNorm (s z - z) < ε ∧ euclideanPairNorm (s.symm z - z) < ε := by
  have hout : (fun _ : Fin 1 => a) ∉ polydisc 1 R := by
    intro hz
    exact (not_le_of_gt ha) (hz 0)
  obtain ⟨p, hp, hsmall⟩ := FiniteCauchy.exists_polynomial_approx_interpolate_exterior
    hR (fun _ : FinitePoint 1 => (0 : ℂ)) isOpen_univ (fun _ _ => Set.mem_univ _)
    (differentiable_const 0).differentiableOn hε hout (c - b)
  let h : ℂ → ℂ := fun u => MvPolynomial.eval (fun _ : Fin 1 => u) p
  have hhd : Differentiable ℂ h := (differentiable_polynomial_eval p).comp
    (differentiable_pi.mpr fun _ => differentiable_fun_id)
  refine ⟨verticalShearHomeomorph h hhd.continuous,
    differentiable_verticalShear h hhd, differentiable_verticalShear_symm h hhd, ?_, ?_⟩
  · change (a, b + MvPolynomial.eval (fun _ : Fin 1 => a) p) = (a, c)
    rw [hp]
    congr 1
    ring
  · intro z hz
    have hs : ‖h z.1‖ < ε := by
      simpa only [h, sub_zero] using hsmall (fun _ : Fin 1 => z.1) (fun _ => hz)
    constructor
    · change euclideanPairNorm (verticalShear h z - z) < ε
      simpa only [euclidean_move_verticalShear] using hs
    · change Real.sqrt (‖z.1 - z.1‖ ^ 2 + ‖z.2 - h z.1 - z.2‖ ^ 2) < ε
      have heq : z.2 - h z.1 - z.2 = -h z.1 := by ring
      simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_add, heq, norm_neg, Real.sqrt_sq (norm_nonneg _)] using hs

/-- The protected set is the actual closed Euclidean ball. There is no
restriction on the prescribed final radius `M`. -/
theorem exists_small_automorphism_pushing_point {R ε : ℝ} (hR : 0 ≤ R)
    (hε : 0 < ε) (p : ℂ × ℂ) (hp : R < euclideanPairNorm p) (M : ℝ) :
    ∃ s : (ℂ × ℂ) ≃ₜ (ℂ × ℂ),
      Differentiable ℂ s ∧ Differentiable ℂ s.symm ∧
      M < euclideanPairNorm (s p) ∧
      ∀ z : ℂ × ℂ, euclideanPairNorm z ≤ R →
        euclideanPairNorm (s z - z) < ε ∧ euclideanPairNorm (s.symm z - z) < ε := by
  have hp0 : 0 < euclideanPairNorm p := hR.trans_lt hp
  let e := normalizedUnitary p hp0
  have hen : ∀ z, euclideanPairNorm (e z) = euclideanPairNorm z :=
    norm_normalizedUnitary p hp0
  have hein : ∀ z, euclideanPairNorm (e.symm z) = euclideanPairNorm z := by
    intro z
    have hh := hen (e.symm z)
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  have haxis : e.symm p = ((euclideanPairNorm p : ℂ), 0) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (normalizedUnitary_axis p hp0).symm
  have ha : R < ‖(euclideanPairNorm p : ℂ)‖ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0] using hp
  obtain ⟨t, ht, hti, htp, hts⟩ := exists_small_shear_both_directions hR hε
    (euclideanPairNorm p : ℂ) 0 ((|M| + 1 : ℝ) : ℂ) ha
  let s := (e.symm.toHomeomorph.trans t).trans e.toHomeomorph
  refine ⟨s, e.differentiable.comp (ht.comp e.symm.differentiable),
    e.differentiable.comp (hti.comp e.symm.differentiable), ?_, ?_⟩
  · change M < euclideanPairNorm (e (t (e.symm p)))
    rw [hen, haxis, htp]
    have hlast := norm_snd_le_euclideanPairNorm
      ((euclideanPairNorm p : ℂ), ((|M| + 1 : ℝ) : ℂ))
    have hmpos : 0 < |M| + 1 := by positivity
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos] at hlast
    exact (lt_of_le_of_lt (le_abs_self M) (lt_add_one _)).trans_le hlast
  · intro z hz
    have hcoord : ‖(e.symm z).1‖ ≤ R :=
      (norm_fst_le_euclideanPairNorm _).trans ((hein z).le.trans hz)
    obtain ⟨hf, hi⟩ := hts (e.symm z) hcoord
    have heq : ∀ w, euclideanPairNorm (e w - z) =
        euclideanPairNorm (w - e.symm z) := by
      intro w
      rw [← e.apply_symm_apply z, ← map_sub, hen, e.symm_apply_apply]
    constructor
    · change euclideanPairNorm (e (t (e.symm z)) - z) < ε
      simpa only [heq] using hf
    · change euclideanPairNorm (e (t.symm (e.symm z)) - z) < ε
      simpa only [heq] using hi

end AutomaticContinuity.BallPointPush
