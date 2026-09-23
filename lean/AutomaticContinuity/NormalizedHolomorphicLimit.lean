import AutomaticContinuity.SeveralVariableUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Normalized holomorphic limits with geometric increments

The geometric convergence step for rescaled holomorphic iterates. Uniformly
small increments give an actual limit on the closed ball; the several-variable
Weierstrass theorem supplies holomorphicity in its interior. Values and first
derivatives at the origin pass to the limit. A separate strengthening uses
continuous first derivatives of the approximants to obtain a local inverse.
-/

noncomputable section

namespace AutomaticContinuity.NormalizedHolomorphicLimit

open Filter Metric Set
open scoped Topology

universe u v

/-- Uniform geometric increments on any set give a uniform limit with the
geometric tail estimate. No topology on the domain is needed. -/
theorem exists_uniformLimit_of_geometric {X : Type u} {Y : Type v}
    [NormedAddCommGroup Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (s : Set X) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ n, ∀ x ∈ s, ‖f (n + 1) x - f n x‖ ≤ C * q ^ n) :
    ∃ g : X → Y, TendstoUniformlyOn f g atTop s ∧
      ∀ n, ∀ x ∈ s, ‖g x - f n x‖ ≤ C * q ^ n / (1 - q) := by
  classical
  have hdist (x : s) (n : ℕ) : dist (f n x) (f (n + 1) x) ≤ C * q ^ n := by
    rw [dist_comm, dist_eq_norm]
    exact hstep n x x.property
  have hex (x : s) : ∃ y : Y, Tendsto (fun n => f n x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 (hdist x))
  choose g hg using hex
  let G : X → Y := fun x => if hx : x ∈ s then g ⟨x, hx⟩ else 0
  have hbound (n : ℕ) (x : X) (hx : x ∈ s) :
      ‖G x - f n x‖ ≤ C * q ^ n / (1 - q) := by
    have he := dist_le_of_le_geometric_of_tendsto q C hq1
      (hdist ⟨x, hx⟩) (hg ⟨x, hx⟩) n
    simpa only [G, dite_eq_left hx, dist_comm (f n x), dist_eq_norm] using he
  refine ⟨G, Metric.tendstoUniformlyOn_iff.mpr ?_, hbound⟩
  intro ε hε
  have hz : Tendsto (fun n : ℕ => C * q ^ n / (1 - q)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C).div_const (1 - q)
  filter_upwards [(tendsto_order.mp hz).2 ε hε] with n hn x hx
  rw [dist_eq_norm]
  exact (hbound n x hx).trans_lt hn

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A normalized holomorphic sequence with the Koenigs geometric increment
bound has a normalized holomorphic limit. Properness or finite dimension of
the domain is not required for this fixed-ball result. -/
theorem exists_normalized_limit (f : ℕ → E → E) {r C : ℝ} (hr : 0 < r)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 r))
    (hstep : ∀ n, ∀ x ∈ closedBall 0 r,
      ‖f (n + 1) x - f n x‖ ≤ C * (4 / 9 : ℝ) ^ n)
    (hf0 : ∀ n, f n 0 = 0)
    (hdf0 : ∀ n, HasFDerivAt (f n) (ContinuousLinearMap.id ℂ E) 0) :
    ∃ g : E → E,
      TendstoUniformlyOn f g atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
      HasFDerivAt g (ContinuousLinearMap.id ℂ E) 0 := by
  obtain ⟨g, hg, _⟩ := exists_uniformLimit_of_geometric f (closedBall 0 r)
    C (4 / 9) (by norm_num) (by norm_num) hstep
  have hball := hg.mono ball_subset_closedBall
  have hgd := SeveralVariableUniformLimit.differentiableOn_of_tendstoUniformlyOn_ball hf hball
  have hg0 : g 0 = 0 := by
    have ht := hg.tendsto_at (mem_closedBall_self hr.le)
    simp only [hf0] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hderiv := SeveralVariableUniformLimit.tendstoUniformlyOn_fderiv_ball
    hf hball (by linarith : r / 2 < r)
  have hdfg : fderiv ℂ g 0 = ContinuousLinearMap.id ℂ E := by
    have ht := hderiv.tendsto_at (mem_ball_self (half_pos hr))
    have hseq : (fun n => fderiv ℂ (f n) 0) = fun _ => ContinuousLinearMap.id ℂ E :=
      funext fun n => (hdf0 n).fderiv
    rw [hseq] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨g, hg, hgd, hg0, ?_⟩
  rw [← hdfg]
  exact (hgd.differentiableAt (ball_mem_nhds 0 hr)).hasFDerivAt

/-- Continuous first derivatives of the approximants make the normalized
limit strictly differentiable, so the inverse function theorem applies. -/
theorem exists_normalized_strict_limit (f : ℕ → E → E) {r C : ℝ} (hr : 0 < r)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 r))
    (hstep : ∀ n, ∀ x ∈ closedBall 0 r,
      ‖f (n + 1) x - f n x‖ ≤ C * (4 / 9 : ℝ) ^ n)
    (hf0 : ∀ n, f n 0 = 0)
    (hdf0 : ∀ n, HasFDerivAt (f n) (ContinuousLinearMap.id ℂ E) 0)
    (hcont : ∀ n, ContinuousOn (fderiv ℂ (f n)) (ball 0 r)) :
    ∃ g : E → E,
      TendstoUniformlyOn f g atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
      HasStrictFDerivAt g (ContinuousLinearMap.id ℂ E) 0 := by
  obtain ⟨g, hg, hgd, hg0, hdfg⟩ := exists_normalized_limit f hr hf hstep hf0 hdf0
  have hderiv := SeveralVariableUniformLimit.tendstoUniformlyOn_fderiv_ball
    hf (hg.mono ball_subset_closedBall) (by linarith : r / 2 < r)
  have hcg : ContinuousOn (fderiv ℂ g) (ball 0 (r / 2)) := by
    apply hderiv.continuousOn
    exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      (hcont n).mono (ball_subset_ball (by linarith : r / 2 ≤ r)))
  have hstrict : HasStrictFDerivAt g (fderiv ℂ g 0) 0 := by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [ball_mem_nhds (0 : E) hr] with x hx
      exact (hgd.differentiableAt (isOpen_ball.mem_nhds hx)).hasFDerivAt
    · exact hcg.continuousAt (ball_mem_nhds 0 (half_pos hr))
  rw [hdfg.fderiv] at hstrict
  exact ⟨g, hg, hgd, hg0, hstrict⟩

/-- The normalized limit is the forward map of an actual local homeomorphism
around the origin. Its inverse is strictly differentiable there with derivative
the identity. All inverse identities are supplied by the bundled homeomorphism. -/
theorem exists_normalized_localHomeomorph (f : ℕ → E → E) {r C : ℝ} (hr : 0 < r)
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 r))
    (hstep : ∀ n, ∀ x ∈ closedBall 0 r,
      ‖f (n + 1) x - f n x‖ ≤ C * (4 / 9 : ℝ) ^ n)
    (hf0 : ∀ n, f n 0 = 0)
    (hdf0 : ∀ n, HasFDerivAt (f n) (ContinuousLinearMap.id ℂ E) 0)
    (hcont : ∀ n, ContinuousOn (fderiv ℂ (f n)) (ball 0 r)) :
    ∃ e : OpenPartialHomeomorph E E,
      TendstoUniformlyOn f e atTop (closedBall 0 r) ∧
      DifferentiableOn ℂ e (ball 0 r) ∧ e 0 = 0 ∧
      (0 : E) ∈ e.source ∧ (0 : E) ∈ e.target ∧
      HasStrictFDerivAt e (ContinuousLinearMap.id ℂ E) 0 ∧
      HasStrictFDerivAt e.symm (ContinuousLinearMap.id ℂ E) 0 := by
  obtain ⟨g, hg, hgd, hg0, hstrict⟩ :=
    exists_normalized_strict_limit f hr hf hstep hf0 hdf0 hcont
  have hstrict' : HasStrictFDerivAt g
      ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) 0 := hstrict
  let e := hstrict'.toOpenPartialHomeomorph g
  have hsource : (0 : E) ∈ e.source := hstrict'.mem_toOpenPartialHomeomorph_source
  have htarget : (0 : E) ∈ e.target := by
    simpa only [hg0] using hstrict'.image_mem_toOpenPartialHomeomorph_target
  refine ⟨e, hg, hgd, hg0, hsource, htarget, hstrict, ?_⟩
  simpa only [e, HasStrictFDerivAt.localInverse_def, hg0,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl] using hstrict'.to_localInverse

end AutomaticContinuity.NormalizedHolomorphicLimit
