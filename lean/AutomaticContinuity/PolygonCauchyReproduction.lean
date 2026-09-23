import AutomaticContinuity.PolygonCauchyIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

/-! # Cauchy reproduction on explicitly oriented polygonal contours

Holomorphy on a convex open neighbourhood gives a primitive of the removable
divided difference. Its integral vanishes on the closed polygon. Explicit
rotated logarithm branch conditions supply the kernel's positive winding.
-/

noncomputable section
namespace AutomaticContinuity.PolygonCauchy
open Complex Set MeasureTheory Function Filter
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem edge_mem_convex {U : Set ℂ} (hU : Convex ℝ U) {a b : ℂ}
    (ha : a ∈ U) (hb : b ∈ U) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    edge a b s ∈ U := by
  have hh := hU ha hb (sub_nonneg.mpr hs.2) hs.1 (by ring : 1 - s + s = 1)
  convert hh using 1
  simp only [edge, Complex.real_smul, ofReal_sub, ofReal_one]
  ring

theorem segmentIntegral_eq_sub_of_primitive {U : Set ℂ}
    {f g : ℂ → E} (hf : ContinuousOn f U) (hg : ∀ w ∈ U, HasDerivAt g (f w) w)
    {a b : ℂ} (hedge : ∀ s ∈ Icc (0 : ℝ) 1, edge a b s ∈ U) :
    segmentIntegral a b f = g b - g a := by
  have hf' : ContinuousOn (fun s : ℝ => (b - a) • f (edge a b s)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact continuousOn_const.smul (hf.comp (continuous_edge a b).continuousOn hedge)
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (edge a b s)) ((b - a) • f (edge a b s)) s := by
    intro s hs
    have hdedge : HasDerivAt (edge a b) (b - a) s := by
      simpa only [edge, id_eq, one_mul] using!
        (((hasDerivAt_id (s : ℂ)).mul_const (b - a)).const_add a).comp_ofReal
    simpa only [comp_apply] using!
      (hg (edge a b s) (hedge s (by simpa using hs))).scomp s hdedge
  unfold segmentIntegral
  rw [← intervalIntegral.integral_smul]
  simpa only [edge_zero, edge_one] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hf'.intervalIntegrable

theorem polygonIntegral_eq_zero {n : ℕ} (v : Fin (n + 1) → ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hv : ∀ i, v i ∈ U) {f : ℂ → E} (hf : DifferentiableOn ℂ f U) :
    polygonIntegral v f = 0 := by
  obtain ⟨g, hg⟩ := hconv.exists_forall_hasDerivWithinAt hf
  have hg' : ∀ w ∈ U, HasDerivAt g (f w) w :=
    fun w hw => (hg w hw).hasDerivAt (hU.mem_nhds hw)
  have hs (a b : Fin (n + 1)) : segmentIntegral (v a) (v b) f = g (v b) - g (v a) :=
    segmentIntegral_eq_sub_of_primitive hf.continuousOn hg'
      (fun _ ht => edge_mem_convex hconv (hv a) (hv b) ht)
  rw [polygonIntegral_eq_chain]
  simp_rw [hs]
  rw [sum_successive_sub (fun i => g (v i))]
  abel

theorem polygonIntegral_inv_smul {n : ℕ} (v : Fin (n + 1) → ℂ)
    (f : ℂ → E) {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hv : ∀ i, v i ∈ U) {z c : ℂ} (hz : z ∈ U) (hc : c ≠ 0)
    (hf : DifferentiableOn ℂ f U)
    (hchain : ∀ i : Fin n, ∀ s ∈ Icc (0 : ℝ) 1,
      c * (edge (v i.castSucc) (v i.succ) s - z) ∈ slitPlane)
    (hclosing : ∀ s ∈ Icc (0 : ℝ) 1,
      -(c * (edge (v (Fin.last n)) (v 0) s - z)) ∈ slitPlane)
    (hstart : (c * (v 0 - z)).im < 0)
    (hfinish : 0 < (c * (v (Fin.last n) - z)).im) :
    polygonIntegral v (fun w => (w - z)⁻¹ • f w) = (2 * Real.pi * I : ℂ) • f z := by
  let F : ℂ → E := dslope f z
  have hF : DifferentiableOn ℂ F U := (differentiableOn_dslope (hU.mem_nhds hz)).mpr hf
  have hzero := polygonIntegral_eq_zero v hU hconv hv hF
  have hsegment (a b : Fin (n + 1))
      (hne : ∀ s ∈ Icc (0 : ℝ) 1, edge (v a) (v b) s ≠ z) :
      segmentIntegral (v a) (v b) (fun w => (w - z)⁻¹ • f w) -
        segmentIntegral (v a) (v b) (fun w => (w - z)⁻¹) • f z =
      segmentIntegral (v a) (v b) F := by
    have hmap : MapsTo (edge (v a) (v b)) (uIcc 0 1) U := by
      intro s hs
      exact edge_mem_convex hconv (hv a) (hv b) (by simpa using hs)
    have hk : ContinuousOn (fun s : ℝ => (edge (v a) (v b) s - z)⁻¹) (uIcc 0 1) :=
      ((continuous_edge (v a) (v b)).continuousOn.sub continuousOn_const).inv₀
        (fun s hs => sub_ne_zero.mpr (hne s (by simpa using hs)))
    have hi₁ : IntervalIntegrable (fun s : ℝ => (edge (v a) (v b) s - z)⁻¹ •
        f (edge (v a) (v b) s)) volume 0 1 :=
      (hk.smul (hf.continuousOn.comp (continuous_edge _ _).continuousOn hmap)).intervalIntegrable
    have hi₂ : IntervalIntegrable (fun s : ℝ => (edge (v a) (v b) s - z)⁻¹ • f z) volume 0 1 :=
      (hk.smul continuousOn_const).intervalIntegrable
    have heq : EqOn (fun s : ℝ => (edge (v a) (v b) s - z)⁻¹ • f (edge (v a) (v b) s) -
        (edge (v a) (v b) s - z)⁻¹ • f z) (fun s => F (edge (v a) (v b) s)) (uIcc 0 1) := by
      intro s hs
      dsimp only
      rw [← smul_sub]
      change _ = dslope f z (edge (v a) (v b) s)
      rw [dslope_of_ne _ (hne s (by simpa using hs))]
      rfl
    unfold segmentIntegral
    dsimp only
    rw [smul_assoc, ← intervalIntegral.integral_smul_const,
      ← smul_sub, ← intervalIntegral.integral_sub hi₁ hi₂,
      intervalIntegral.integral_congr heq]
  have hchain' (i : Fin n) := hsegment i.castSucc i.succ (fun s hs =>
    sub_ne_zero.mp (mul_ne_zero_iff.mp (slitPlane_ne_zero (hchain i s hs))).2)
  have hclosing' := hsegment (Fin.last n) 0 (fun s hs =>
    sub_ne_zero.mp (mul_ne_zero_iff.mp (neg_ne_zero.mp (slitPlane_ne_zero (hclosing s hs)))).2)
  have htotal : polygonIntegral v (fun w => (w - z)⁻¹ • f w) -
      polygonIntegral v (fun w => (w - z)⁻¹) • f z = polygonIntegral v F := by
    simp only [polygonIntegral_eq_chain, add_smul, Finset.sum_smul]
    rw [show (∑ i : Fin n, segmentIntegral (v i.castSucc) (v i.succ) (fun w => (w-z)⁻¹ • f w)) +
        segmentIntegral (v (Fin.last n)) (v 0) (fun w => (w-z)⁻¹ • f w) -
        ((∑ i : Fin n, segmentIntegral (v i.castSucc) (v i.succ) (fun w => (w-z)⁻¹) • f z) +
        segmentIntegral (v (Fin.last n)) (v 0) (fun w => (w-z)⁻¹) • f z) =
        (∑ i : Fin n, (segmentIntegral (v i.castSucc) (v i.succ) (fun w => (w-z)⁻¹ • f w) -
        segmentIntegral (v i.castSucc) (v i.succ) (fun w => (w-z)⁻¹) • f z)) +
        (segmentIntegral (v (Fin.last n)) (v 0) (fun w => (w-z)⁻¹ • f w) -
        segmentIntegral (v (Fin.last n)) (v 0) (fun w => (w-z)⁻¹) • f z) by
          rw [Finset.sum_sub_distrib]; abel]
    simp_rw [hchain', hclosing']
  rw [polygonIntegral_kernel v hc hchain hclosing hstart hfinish, hzero] at htotal
  exact sub_eq_zero.mp htotal

theorem normalized_polygonIntegral_inv_smul {n : ℕ} (v : Fin (n + 1) → ℂ)
    (f : ℂ → E) {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hv : ∀ i, v i ∈ U) {z c : ℂ} (hz : z ∈ U) (hc : c ≠ 0)
    (hf : DifferentiableOn ℂ f U)
    (hchain : ∀ i : Fin n, ∀ s ∈ Icc (0 : ℝ) 1,
      c * (edge (v i.castSucc) (v i.succ) s - z) ∈ slitPlane)
    (hclosing : ∀ s ∈ Icc (0 : ℝ) 1,
      -(c * (edge (v (Fin.last n)) (v 0) s - z)) ∈ slitPlane)
    (hstart : (c * (v 0 - z)).im < 0)
    (hfinish : 0 < (c * (v (Fin.last n) - z)).im) :
    (2 * Real.pi * I : ℂ)⁻¹ • polygonIntegral v (fun w => (w - z)⁻¹ • f w) = f z := by
  rw [polygonIntegral_inv_smul v f hU hconv hv hz hc hf hchain hclosing hstart hfinish,
    inv_smul_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

/-- A pole outside the convex holomorphy neighbourhood contributes zero. -/
theorem polygonIntegral_inv_smul_eq_zero {n : ℕ} (v : Fin (n + 1) → ℂ)
    (f : ℂ → E) {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hv : ∀ i, v i ∈ U) {z : ℂ} (hz : z ∉ U)
    (hf : DifferentiableOn ℂ f U) :
    polygonIntegral v (fun w => (w - z)⁻¹ • f w) = 0 := by
  apply polygonIntegral_eq_zero v hU hconv hv
  exact ((differentiableOn_id.sub_const z).inv
    (fun w hw => sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz))).smul hf

end AutomaticContinuity.PolygonCauchy
