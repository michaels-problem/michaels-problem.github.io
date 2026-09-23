import AutomaticContinuity.RectangleCauchyKernel

set_option autoImplicit false

/-! # Polygonal contour integrals and their kernel

Contours are actual finite sums of affine segment integrals. The kernel
calculation permits a rotated branch ray and cyclic choice of the starting
vertex. Its geometric hypotheses specify the single crossing edge directly;
they do not assume a winding number or a desired integral identity.
-/

noncomputable section
namespace AutomaticContinuity.PolygonCauchy
open Complex Set MeasureTheory Function
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def edge (a b : ℂ) (s : ℝ) : ℂ := a + (s : ℂ) * (b - a)

@[simp] theorem edge_zero (a b : ℂ) : edge a b 0 = a := by simp [edge]
@[simp] theorem edge_one (a b : ℂ) : edge a b 1 = b := by simp [edge]

theorem continuous_edge (a b : ℂ) : Continuous (edge a b) := by unfold edge; fun_prop

def segmentIntegral (a b : ℂ) (f : ℂ → E) : E :=
  (b - a) • ∫ s : ℝ in 0..1, f (edge a b s)

def polygonIntegral {n : ℕ} (v : Fin (n + 1) → ℂ) (f : ℂ → E) : E :=
  ∑ i, segmentIntegral (v i) (v (i + 1)) f

theorem polygonIntegral_eq_chain {n : ℕ} (v : Fin (n + 1) → ℂ) (f : ℂ → E) :
    polygonIntegral v f =
      (∑ i : Fin n, segmentIntegral (v i.castSucc) (v i.succ) f) +
        segmentIntegral (v (Fin.last n)) (v 0) f := by
  unfold polygonIntegral
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 2
    apply Fin.ext
    simp
  · congr 2
    apply Fin.ext
    simp

theorem polygonIntegral_cyclic {n : ℕ} (v : Fin (n + 1) → ℂ) (k : Fin (n + 1))
    (f : ℂ → E) :
    polygonIntegral (fun i => v (i + k)) f = polygonIntegral v f := by
  unfold polygonIntegral
  have hh := Equiv.sum_comp (Equiv.addRight k)
    (fun i => segmentIntegral (v i) (v (i + 1)) f)
  change (∑ i, segmentIntegral (v (i + k)) (v (i + k + 1)) f) = _ at hh
  simpa only [add_right_comm] using hh

theorem sum_successive_sub {F : Type*} [AddCommGroup F] {n : ℕ} (f : Fin (n + 1) → F) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  have h₁ := Fin.sum_univ_castSucc f
  have h₂ := Fin.sum_univ_succ f
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h₂.symm.trans h₁

theorem segmentIntegral_kernel_eq_log {a b z c : ℂ} (hc : c ≠ 0)
    (hslit : ∀ s ∈ Icc (0 : ℝ) 1, c * (edge a b s - z) ∈ slitPlane) :
    segmentIntegral a b (fun w => (w - z)⁻¹) =
      log (c * (b - z)) - log (c * (a - z)) := by
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : edge a b s - z ≠ 0 := by
    exact (mul_ne_zero_iff.mp (slitPlane_ne_zero (hslit s hs))).2
  have hcont : ContinuousOn (fun s : ℝ => (b - a) * (edge a b s - z)⁻¹) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.mul
      (((continuous_edge a b).continuousOn.sub continuousOn_const).inv₀ hne)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => log (c * (edge a b s - z)))
        ((b - a) * (edge a b s - z)⁻¹) s := by
    intro s hs
    have hh := (((((hasDerivAt_id (s : ℂ)).mul_const (b - a)).const_add a).sub_const z).const_mul c).clog
      (hslit s (by simpa only [uIcc_of_le zero_le_one] using hs))
    have heq : c * (b - a) / (c * (edge a b s - z)) = (b - a) * (edge a b s - z)⁻¹ := by
      rw [mul_div_mul_left _ _ hc, div_eq_mul_inv]
    have hh' : HasDerivAt (fun s : ℝ => log (c * (edge a b s - z)))
        (c * (b - a) / (c * (edge a b s - z))) s := by
      simpa only [edge, id_eq, one_mul] using! hh.comp_ofReal
    rwa [heq] at hh'
  unfold segmentIntegral
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  simpa only [edge_zero, edge_one] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

theorem polygonIntegral_kernel {n : ℕ} (v : Fin (n + 1) → ℂ) {z c : ℂ}
    (hc : c ≠ 0)
    (hchain : ∀ i : Fin n, ∀ s ∈ Icc (0 : ℝ) 1,
      c * (edge (v i.castSucc) (v i.succ) s - z) ∈ slitPlane)
    (hclosing : ∀ s ∈ Icc (0 : ℝ) 1,
      -(c * (edge (v (Fin.last n)) (v 0) s - z)) ∈ slitPlane)
    (hstart : (c * (v 0 - z)).im < 0)
    (hfinish : 0 < (c * (v (Fin.last n) - z)).im) :
    polygonIntegral v (fun w => (w - z)⁻¹) = (2 * Real.pi * I : ℂ) := by
  rw [polygonIntegral_eq_chain]
  have hclose := segmentIntegral_kernel_eq_log (neg_ne_zero.mpr hc)
    (a := v (Fin.last n)) (b := v 0) (z := z)
    (by simpa only [neg_mul] using hclosing)
  simp only [neg_mul] at hclose
  rw [hclose]
  simp_rw [segmentIntegral_kernel_eq_log hc (hchain _)]
  rw [sum_successive_sub (fun i => log (c * (v i - z)))]
  have hT := RectangleCauchy.log_sub_log_neg_of_im_pos hfinish
  have hB := RectangleCauchy.log_sub_log_neg_of_im_neg hstart
  calc
    _ = (log (c * (v (Fin.last n) - z)) - log (-(c * (v (Fin.last n) - z)))) -
        (log (c * (v 0 - z)) - log (-(c * (v 0 - z)))) := by ring
    _ = _ := by rw [hT, hB]; ring

end AutomaticContinuity.PolygonCauchy
