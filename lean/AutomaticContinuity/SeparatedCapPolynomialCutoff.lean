import AutomaticContinuity.PolynomialFunctionResolvent
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

/-! # Polynomial cutoffs on two separated complex-coordinate caps

The sigmoid is constructed inside the actual Banach algebra `P(K)` using its
exponential and the inverse of a nonvanishing element. Polynomial density
then gives a genuine polynomial cutoff. No Runge theorem is assumed.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set Complex Filter
open scoped Topology

private theorem one_add_ne_zero_of_small {w : ℂ} (hw : ‖w‖ ≤ 1/2) : 1+w ≠ 0 := by
  intro h
  have hh : w = -1 := by linear_combination h
  norm_num [hh] at hw

private theorem norm_inv_one_add_le_two {w : ℂ} (hw : ‖w‖ ≤ 1/2) : ‖(1+w)⁻¹‖ ≤ 2 := by
  have hlow : 1/2 ≤ ‖1+w‖ := by
    have hh := norm_sub_le (1+w) w
    simp only [add_sub_cancel_right,norm_one] at hh
    linarith
  rw [norm_inv]
  exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hlow)

private theorem norm_inv_one_add_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖(1+w)⁻¹-1‖ ≤ 2*‖w‖ := by
  have heq : (1+w)⁻¹-1 = -w*(1+w)⁻¹ := by
    field_simp [one_add_ne_zero_of_small hw]
    ring
  rw [heq,norm_mul,norm_neg]
  nlinarith [norm_inv_one_add_le_two hw,norm_nonneg w]

private theorem norm_div_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖w/(1+w)‖ ≤ 2*‖w‖ := by
  rw [div_eq_mul_inv,norm_mul]
  nlinarith [norm_inv_one_add_le_two hw,norm_nonneg w]

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

def capExponential (j : σ) (a : ℂ) (mid s : ℝ) : P K :=
  NormedSpace.exp ((s:ℂ) • (a • polynomial K (MvPolynomial.X j) - algebraMap ℂ (P K) (mid:ℂ)))

@[simp] theorem capExponential_apply (j : σ) (a : ℂ) (mid s : ℝ) (x : K) :
    (capExponential K j a mid s).val x = Complex.exp ((s:ℂ)*(a*x.val j-(mid:ℂ))) := by
  let : NormedAlgebra ℚ (P K) := NormedAlgebra.restrictScalars ℚ ℂ (P K)
  change evaluation K x (NormedSpace.exp _) = _
  rw [NormedSpace.map_exp (evaluation K x) (map_continuous (evaluation K x))]
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp [evaluation_apply,polynomial_apply,smul_eq_mul]

private theorem exists_sigmoid_scale {c d ε : ℝ} (hcd : c < d) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧
      (∀ z : ℂ, z.re ≤ c →
        1 + Complex.exp ((s:ℂ)*(z-((c+d)/2:ℝ))) ≠ 0 ∧
        ‖(1+Complex.exp ((s:ℂ)*(z-((c+d)/2:ℝ))))⁻¹-1‖ < ε) ∧
      (∀ z : ℂ, d ≤ z.re →
        1 + Complex.exp ((s:ℂ)*(z-((c+d)/2:ℝ))) ≠ 0 ∧
        ‖(1+Complex.exp ((s:ℂ)*(z-((c+d)/2:ℝ))))⁻¹‖ < ε) := by
  let η : ℝ := min (1/2) (ε/2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hev : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < η :=
    (tendsto_order.mp Real.tendsto_exp_neg_atTop_nhds_zero).2 η hη
  obtain ⟨T,hTsmall,hTpos⟩ := (hev.and (eventually_gt_atTop (0:ℝ))).exists
  let gap : ℝ := (d-c)/2
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let s : ℝ := T/gap
  have hs : 0 < s := by dsimp [s]; positivity
  have hsg : s*gap = T := div_mul_cancel₀ _ (ne_of_gt hgap)
  have heps : 2*Real.exp (-T) < ε := by
    have := hTsmall.trans_le (min_le_right _ _)
    linarith
  have hsmall : Real.exp (-T) ≤ 1/2 := hTsmall.le.trans (min_le_left _ _)
  refine ⟨s,hs,?_,?_⟩
  · intro z hz
    let u : ℂ := (s:ℂ)*(z-((c+d)/2:ℝ))
    have hu : u.re ≤ -T := by
      have hb : z.re-(c+d)/2 ≤ -gap := by dsimp [gap]; linarith
      calc
        _ = s*(z.re-(c+d)/2) := by simp [u]
        _ ≤ s*(-gap) := mul_le_mul_of_nonneg_left hb hs.le
        _ = -T := by rw [mul_neg,hsg]
    have hn : ‖Complex.exp u‖ ≤ Real.exp (-T) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hu
    have hw : ‖Complex.exp u‖ ≤ 1/2 := hn.trans hsmall
    exact ⟨one_add_ne_zero_of_small hw,
      (norm_inv_one_add_sub_one_le hw).trans_lt (by linarith)⟩
  · intro z hz
    let u : ℂ := (s:ℂ)*(z-((c+d)/2:ℝ))
    have hu : (-u).re ≤ -T := by
      have hb : gap ≤ z.re-(c+d)/2 := by dsimp [gap]; linarith
      have hh := mul_le_mul_of_nonneg_left hb hs.le
      rw [hsg] at hh
      simp only [neg_re]
      have hre : u.re = s*(z.re-(c+d)/2) := by simp [u]
      rw [hre]
      linarith
    have hn : ‖Complex.exp (-u)‖ ≤ Real.exp (-T) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr hu
    have hw : ‖Complex.exp (-u)‖ ≤ 1/2 := hn.trans hsmall
    have hsmallne := one_add_ne_zero_of_small hw
    have hfactor : Complex.exp (-u)*(1+Complex.exp u) = 1+Complex.exp (-u) := by
      rw [mul_add,mul_one,Complex.exp_neg,inv_mul_cancel₀ (Complex.exp_ne_zero u)]
      ring
    have hne : 1+Complex.exp u ≠ 0 := by
      intro heq
      rw [heq,mul_zero] at hfactor
      exact hsmallne hfactor.symm
    have heq : (1+Complex.exp u)⁻¹ = Complex.exp (-u)/(1+Complex.exp (-u)) := by
      apply (eq_div_iff hsmallne).mpr
      rw [← hfactor]
      field_simp
    refine ⟨hne,?_⟩
    change ‖(1+Complex.exp u)⁻¹‖ < ε
    rw [heq]
    exact (norm_div_one_add_le hw).trans_lt (by linarith)

/-- On a polynomially convex compact set contained in two separated caps,
there is a genuine polynomial uniformly close to one on the left cap and
zero on the right cap. The separating coordinate may be rotated. -/
theorem exists_polynomial_cap_cutoff
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ ↦ x) K)
    (j : σ) (a : ℂ) {c d : ℝ} (hcd : c < d)
    (hcaps : ∀ x ∈ K, (a*x j).re ≤ c ∨ d ≤ (a*x j).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℂ,
      (∀ x ∈ K, (a*x j).re ≤ c → ‖MvPolynomial.eval x p-1‖ < ε) ∧
      (∀ x ∈ K, d ≤ (a*x j).re → ‖MvPolynomial.eval x p‖ < ε) := by
  obtain ⟨s,_,hleft,hright⟩ := exists_sigmoid_scale hcd (half_pos hε)
  let e : P K := capExponential K j a ((c+d)/2) s
  have he (x : K) : e.val x = Complex.exp ((s:ℂ)*(a*x.val j-((c+d)/2:ℝ))) :=
    capExponential_apply K j a ((c+d)/2) s x
  have hunit : IsUnit (1+e) := by
    apply isUnit_of_nonvanishing K hK
    intro x
    change 1+e.val x ≠ 0
    rw [he]
    rcases hcaps x.val x.property with hx | hx
    · exact (hleft _ hx).1
    · exact (hright _ hx).1
  let F : P K := Ring.inverse (1+e)
  have hF (x : K) : F.val x = (1+Complex.exp ((s:ℂ)*(a*x.val j-((c+d)/2:ℝ))))⁻¹ := by
    dsimp only [F]
    rw [inverse_apply K _ hunit]
    change (1+e.val x)⁻¹ = _
    rw [he]
  obtain ⟨p,hp⟩ := exists_polynomial_approx K F (half_pos hε)
  have happ (x : K) : ‖MvPolynomial.eval x.val p-F.val x‖ < ε/2 := by
    have hh := (ContinuousMap.norm_coe_le_norm (polynomial K p-F).val x).trans_lt hp
    simpa only [Subalgebra.coe_sub,ContinuousMap.sub_apply,polynomial_apply] using hh
  refine ⟨p,?_,?_⟩
  · intro x hx hc
    let x' : K := ⟨x,hx⟩
    have h₁ := happ x'
    have h₂ : ‖F.val x'-1‖ < ε/2 := by rw [hF]; exact (hleft _ hc).2
    have h₃ := norm_add_le (MvPolynomial.eval x p-F.val x') (F.val x'-1)
    have heq : (MvPolynomial.eval x p-F.val x')+(F.val x'-1) = MvPolynomial.eval x p-1 := by ring
    rw [heq] at h₃
    exact h₃.trans_lt (by linarith)
  · intro x hx hd
    let x' : K := ⟨x,hx⟩
    have h₁ := happ x'
    have h₂ : ‖F.val x'‖ < ε/2 := by rw [hF]; exact (hright _ hd).2
    have h₃ := norm_add_le (MvPolynomial.eval x p-F.val x') (F.val x')
    rw [sub_add_cancel] at h₃
    exact h₃.trans_lt (by linarith)

end AutomaticContinuity.PolynomialFunctionAlgebra
