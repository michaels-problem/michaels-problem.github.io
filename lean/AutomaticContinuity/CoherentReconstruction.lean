import AutomaticContinuity.CoefficientCompleteness
import AutomaticContinuity.DenseInverseLimit

set_option autoImplicit false

/-!
# Reconstructing coefficient series from coherent normed stages

This uses completeness of the actual coefficient topology and simultaneous
approximation in its increasing norms. It does not identify completions with a
second coefficient model or assume that a dense completion map is surjective.
-/

noncomputable section

namespace AutomaticContinuity.CoherentReconstruction

open Filter CoefficientSeries
open scoped Topology

universe u

variable {B : ℕ → Type u} [∀ n, NormedAddCommGroup (B n)]
variable (p : (n : ℕ) → CoefficientSeries →+ B n)

def allProjection (a : CoefficientSeries) : (n : ℕ) → B n := fun n => p n a

theorem projection_comap (hnorm : ∀ n a, ‖p n a‖ = q (n + 1) a) (n : ℕ) :
    UniformSpace.comap (p n) (inferInstance : UniformSpace (B n)) =
      (definingSeminorm n).toSeminormedAddCommGroup.toUniformSpace := by
  let _ := (definingSeminorm n).toSeminormedAddCommGroup
  let _ : UniformSpace CoefficientSeries :=
    (definingSeminorm n).toSeminormedAddCommGroup.toUniformSpace
  have h : Isometry (p n) := AddMonoidHomClass.isometry_of_norm (p n) (hnorm n)
  exact h.isUniformInducing.comap_uniformSpace

theorem allProjection_isUniformInducing
    (hnorm : ∀ n a, ‖p n a‖ = q (n + 1) a) :
    IsUniformInducing (allProjection p) := by
  rw [isUniformInducing_iff_uniformSpace]
  simp only [Pi.uniformSpace_eq, UniformSpace.comap_iInf,
    ← UniformSpace.comap_comap]
  change (⨅ n : ℕ, UniformSpace.comap (p n)
    (inferInstance : UniformSpace (B n))) = _
  simp_rw [projection_comap p hnorm]
  rfl

variable (f : (n : ℕ) → B (n + 1) → B n)

theorem down_projection (hpf : ∀ n a, f n (p (n + 1) a) = p n a)
    {r n : ℕ} (h : r ≤ n) (a : CoefficientSeries) :
    DenseInverseLimit.down f h (p n a) = p r a := by
  induction h with
  | refl => simp
  | @step n h ih =>
      rw [DenseInverseLimit.down_succ f h]
      simpa only [Function.comp_apply, hpf] using ih

omit [∀ n, NormedAddCommGroup (B n)] in
theorem down_compatible (b : (n : ℕ) → B n)
    (hb : ∀ n, f n (b (n + 1)) = b n) {r n : ℕ} (h : r ≤ n) :
    DenseInverseLimit.down f h (b n) = b r := by
  induction h with
  | refl => simp
  | @step n h ih =>
      rw [DenseInverseLimit.down_succ f h]
      simpa only [Function.comp_apply, hb] using ih

/-- Coherent elements of dense contracting normed stages come from an actual
coefficient series, provided their norms are exactly the defining norms. -/
theorem exists_of_compatible
    (hnorm : ∀ n a, ‖p n a‖ = q (n + 1) a)
    (hdense : ∀ n, DenseRange (p n))
    (hf : ∀ n, LipschitzWith 1 (f n))
    (hpf : ∀ n a, f n (p (n + 1) a) = p n a)
    (b : (n : ℕ) → B n) (hb : ∀ n, f n (b (n + 1)) = b n) :
    ∃ a : CoefficientSeries, ∀ n, p n a = b n := by
  classical
  have happrox (n : ℕ) : ∃ a : CoefficientSeries,
      dist (p n a) (b n) < (1 / 2 : ℝ) ^ n := by
    simpa only [dist_comm] using
      (hdense n).exists_dist_lt (b n) (by positivity : 0 < (1 / 2 : ℝ) ^ n)
  choose a ha using happrox
  have hcoord (r : ℕ) : Tendsto (fun n => p r (a n)) atTop (𝓝 (b r)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg)
      (show ∀ᶠ n in atTop, dist (p r (a n)) (b r) ≤ (1 / 2 : ℝ) ^ n from ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    filter_upwards [eventually_ge_atTop r] with n hn
    rw [← down_projection p f hpf hn (a n), ← down_compatible f b hb hn]
    exact ((DenseInverseLimit.down_lipschitz f hf hn).dist_le_mul _ _).trans
      (by simpa using (ha n).le)
  have hlim : Tendsto (fun n => allProjection p (a n)) atTop (𝓝 b) :=
    tendsto_pi_nhds.mpr hcoord
  have hclosed : IsClosed (Set.range (allProjection p)) :=
    (allProjection_isUniformInducing p hnorm).isComplete_range.isClosed
  have hbmem : b ∈ Set.range (allProjection p) :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => ⟨a n, rfl⟩)
  obtain ⟨x, hx⟩ := hbmem
  exact ⟨x, fun n => congrFun hx n⟩

end AutomaticContinuity.CoherentReconstruction
