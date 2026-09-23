import AutomaticContinuity.LocalPointInterpolation
import AutomaticContinuity.LocalFlagInterpolation
import AutomaticContinuity.EuclideanBallGeometry

set_option autoImplicit false

/-!
# Explicit complex shears and small exterior-point moves

The shear `(u,v) ↦ (u,v+h(u))` has its actual inverse with `-h`. If `h` is
entire, both directions are holomorphic. An exterior-point peak polynomial
provides a shear that moves that point to any prescribed second coordinate,
while remaining uniformly close to the identity on a whole coordinate strip.

These are concrete automorphisms, not an invocation of an automorphism
approximation theorem. They do not expel a general compact forbidden graph.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialShears

def verticalShear (h : ℂ → ℂ) : (ℂ × ℂ) ≃ (ℂ × ℂ) where
  toFun z := (z.1, z.2 + h z.1)
  invFun z := (z.1, z.2 - h z.1)
  left_inv z := by simp
  right_inv z := by simp

def verticalShearHomeomorph (h : ℂ → ℂ) (hh : Continuous h) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toEquiv := verticalShear h
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hh.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hh.comp continuous_fst))

theorem differentiable_verticalShear (h : ℂ → ℂ) (hh : Differentiable ℂ h) :
    Differentiable ℂ (verticalShear h) :=
  differentiable_fst.prodMk (differentiable_snd.add (hh.comp differentiable_fst))

theorem differentiable_verticalShear_symm (h : ℂ → ℂ) (hh : Differentiable ℂ h) :
    Differentiable ℂ (verticalShear h).symm :=
  differentiable_fst.prodMk (differentiable_snd.sub (hh.comp differentiable_fst))

@[simp] theorem euclidean_move_verticalShear (h : ℂ → ℂ) (z : ℂ × ℂ) :
    euclideanPairNorm (verticalShear h z - z) = ‖h z.1‖ := by
  change Real.sqrt (‖z.1 - z.1‖ ^ 2 + ‖z.2 + h z.1 - z.2‖ ^ 2) = _
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add, add_sub_cancel_left]
  exact Real.sqrt_sq (norm_nonneg _)

/-- A genuine entire automorphism can change the second coordinate of one
point outside the first-coordinate disk, with arbitrary uniform smallness on
the full vertical strip over that disk. -/
theorem exists_small_shear_moving_point {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (a b c : ℂ) (ha : R < ‖a‖) :
    ∃ s : (ℂ × ℂ) ≃ₜ (ℂ × ℂ),
      Differentiable ℂ s ∧ Differentiable ℂ s.symm ∧ s (a, b) = (a, c) ∧
        ∀ z : ℂ × ℂ, ‖z.1‖ ≤ R → euclideanPairNorm (s z - z) < ε := by
  have hout : (fun _ : Fin 1 => a) ∉ polydisc 1 R := by
    intro hz
    exact (not_le_of_gt ha) (hz 0)
  obtain ⟨p, hp, hsmall⟩ := FiniteCauchy.exists_polynomial_approx_interpolate_exterior
    hR (fun _ : FinitePoint 1 => (0 : ℂ)) isOpen_univ (fun _ _ => Set.mem_univ _)
    (differentiable_const 0).differentiableOn hε hout (c - b)
  let h : ℂ → ℂ := fun u => MvPolynomial.eval (fun _ : Fin 1 => u) p
  have hhd : Differentiable ℂ h :=
    (differentiable_polynomial_eval p).comp
      (differentiable_pi.mpr fun _ => differentiable_fun_id)
  refine ⟨verticalShearHomeomorph h hhd.continuous,
    differentiable_verticalShear h hhd, differentiable_verticalShear_symm h hhd, ?_, ?_⟩
  · change (a, b + MvPolynomial.eval (fun _ : Fin 1 => a) p) = (a, c)
    rw [hp]
    congr 1
    ring
  · intro z hz
    change euclideanPairNorm (verticalShear h z - z) < ε
    rw [euclidean_move_verticalShear]
    simpa only [sub_zero] using hsmall (fun _ : Fin 1 => z.1) (fun _ => hz)

/-- A shear whose coefficient depends holomorphically on finite base parameters.
The base coordinates are fixed exactly. -/
def parameterShear {n : ℕ} (h : FinitePoint n × ℂ → ℂ) :
    (FinitePoint n × (ℂ × ℂ)) ≃ (FinitePoint n × (ℂ × ℂ)) where
  toFun z := (z.1, z.2.1, z.2.2 + h (z.1, z.2.1))
  invFun z := (z.1, z.2.1, z.2.2 - h (z.1, z.2.1))
  left_inv z := by simp
  right_inv z := by simp

@[simp] theorem parameterShear_fst {n : ℕ} (h : FinitePoint n × ℂ → ℂ)
    (z : FinitePoint n × (ℂ × ℂ)) : (parameterShear h z).1 = z.1 := rfl

theorem differentiable_parameterShear {n : ℕ} (h : FinitePoint n × ℂ → ℂ)
    (hh : Differentiable ℂ h) : Differentiable ℂ (parameterShear h) := by
  exact differentiable_fst.prodMk
    (differentiable_snd.fst.prodMk
      (differentiable_snd.snd.add (hh.comp (differentiable_fst.prodMk differentiable_snd.fst))))

theorem differentiable_parameterShear_symm {n : ℕ} (h : FinitePoint n × ℂ → ℂ)
    (hh : Differentiable ℂ h) : Differentiable ℂ (parameterShear h).symm := by
  exact differentiable_fst.prodMk
    (differentiable_snd.fst.prodMk
      (differentiable_snd.snd.sub (hh.comp (differentiable_fst.prodMk differentiable_snd.fst))))

end AutomaticContinuity.PolynomialShears
