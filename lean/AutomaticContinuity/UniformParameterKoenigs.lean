import AutomaticContinuity.SmallScaleKoenigsEstimates
import AutomaticContinuity.NormalizedHolomorphicLimit

set_option autoImplicit false

/-!
# A jointly holomorphic Koenigs limit with uniform parameter bounds

Uniform inverse-linear and contraction bounds `M,q` with `M*q² < 1` give a
uniformly convergent rescaled-iterate sequence on the full parameter set times
a closed source ball. Joint holomorphy of the nonlinear map and inverse-linear
application implies joint holomorphy of the limit in the interior. All bounds
and parameter-regularity hypotheses are explicit; no parameter family of
automorphisms or approximation property is constructed in this module.
-/

noncomputable section

namespace AutomaticContinuity.UniformParameterKoenigs

open Filter Metric Set KoenigsEstimates
open scoped Topology

universe u v
variable {P : Type u} {E : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An operator bound on the inverse linear map controls every inverse power. -/
theorem norm_inversePower_le (A : E ≃L[ℂ] E) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ x, ‖A.symm x‖ ≤ M * ‖x‖) (n : ℕ) (x : E) :
    ‖inversePower A n x‖ ≤ M ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp [inversePower]
  | succ n ih =>
      change ‖((A.symm : E →L[ℂ] E) ^ (n + 1)) x‖ ≤ _
      rw [pow_succ, mul_apply_eq_comp]
      change ‖inversePower A n (A.symm x)‖ ≤ _
      calc
        _ ≤ M ^ n * ‖A.symm x‖ := ih _
        _ ≤ M ^ n * (M * ‖x‖) := mul_le_mul_of_nonneg_left (hA x) (pow_nonneg hM n)
        _ = _ := by rw [pow_succ]; ring

/-- The general rescaled increment rate is `M*q²`. -/
theorem norm_rescaledIterate_sub_le {A : E ≃L[ℂ] E} {T : E → E}
    {M q r C : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A.symm x‖ ≤ M * ‖x‖)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ q * ‖x‖)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2)
    (n : ℕ) (x : E) (hx : x ∈ closedBall (0 : E) r) :
    ‖rescaledIterate A T (n + 1) x - rescaledIterate A T n x‖ ≤
      (M * C * r ^ 2) * (M * q ^ 2) ^ n := by
  obtain ⟨hn, hmem⟩ := SmallScaleKoenigsEstimates.norm_iterate_le hr hq hq1 hT hx n
  rw [rescaledIterate_sub]
  have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  calc
    _ ≤ M ^ (n + 1) * ‖T (T^[n] x) - A (T^[n] x)‖ := norm_inversePower_le A hM hA _ _
    _ ≤ M ^ (n + 1) * (C * ‖T^[n] x‖ ^ 2) := by gcongr; exact hrem _ hmem
    _ ≤ M ^ (n + 1) * (C * ((q ^ n * r) ^ 2)) := by
      gcongr
      exact hn.trans (mul_le_mul_of_nonneg_left hxnorm (pow_nonneg hq n))
    _ = (M * C * r ^ 2) * (M * q ^ 2) ^ n := by
      rw [mul_pow, pow_succ, mul_pow]
      have hpow : (q ^ n) ^ 2 = (q ^ 2) ^ n :=
        (pow_mul _ n 2).symm.trans (by rw [Nat.mul_comm, pow_mul])
      rw [hpow]
      ring

section JointDifferentiability

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Joint holomorphy of every nonlinear iterate follows from invariance of the
source domain and joint holomorphy of the original map. -/
theorem differentiableOn_iterates (T : P → E → E) {U : Set P} {V : Set E}
    (hT : DifferentiableOn ℂ (fun z : P × E => T z.1 z.2) (U ×ˢ V))
    (hinv : ∀ p ∈ U, MapsTo (T p) V V) (n : ℕ) :
    DifferentiableOn ℂ (fun z : P × E => (T z.1)^[n] z.2) (U ×ˢ V) := by
  induction n with
  | zero => exact differentiableOn_snd
  | succ n ih =>
      have hd := hT.comp (differentiableOn_fst.prodMk ih) (by
        intro z hz
        exact ⟨hz.1, (hinv z.1 hz.1).iterate n hz.2⟩)
      simpa only [Function.comp_def, Function.iterate_succ_apply'] using hd

/-- Inverse powers depend jointly holomorphically on parameter and vector
when inverse-linear application does. -/
theorem differentiableOn_inversePowers (A : P → E ≃L[ℂ] E) {U : Set P}
    (hA : DifferentiableOn ℂ (fun z : P × E => (A z.1).symm z.2) (U ×ˢ univ))
    (n : ℕ) :
    DifferentiableOn ℂ (fun z : P × E => inversePower (A z.1) n z.2) (U ×ˢ univ) := by
  induction n with
  | zero => simpa only [inversePower, pow_zero, one_apply_eq_self] using
      (differentiableOn_snd : DifferentiableOn ℂ (Prod.snd : P × E → E) (U ×ˢ univ))
  | succ n ih =>
      have hd := hA.comp (differentiableOn_fst.prodMk ih) (by
        intro z hz
        exact ⟨hz.1, mem_univ _⟩)
      simpa only [Function.comp_def, inversePower, pow_succ', mul_apply_eq_comp,
        ContinuousLinearEquiv.coe_coe] using hd

theorem differentiableOn_rescaledIterates (A : P → E ≃L[ℂ] E) (T : P → E → E)
    {U : Set P} {V : Set E}
    (hA : DifferentiableOn ℂ (fun z : P × E => (A z.1).symm z.2) (U ×ˢ univ))
    (hT : DifferentiableOn ℂ (fun z : P × E => T z.1 z.2) (U ×ˢ V))
    (hinv : ∀ p ∈ U, MapsTo (T p) V V) (n : ℕ) :
    DifferentiableOn ℂ (fun z : P × E => rescaledIterate (A z.1) (T z.1) n z.2) (U ×ˢ V) := by
  exact (differentiableOn_inversePowers A hA n).comp
    (differentiableOn_fst.prodMk (differentiableOn_iterates T hT hinv n))
    (fun z hz => ⟨hz.1, mem_univ _⟩)

variable [CompleteSpace E]

/-- Uniform convergence on an open set gives holomorphy without a properness
assumption: restrict directly to a ball at each point. -/
theorem differentiableOn_of_tendstoUniformlyOn_open {f : ℕ → P → E} {g : P → E}
    {U : Set P} (hU : IsOpen U) (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hlim : TendstoUniformlyOn f g atTop U) : DifferentiableOn ℂ g U := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hd := SeveralVariableUniformLimit.differentiableOn_of_tendstoUniformlyOn_ball
    (fun n => (hf n).mono hsub) (hlim.mono hsub)
  exact (hd.differentiableAt (ball_mem_nhds x hr)).differentiableWithinAt

/-- Uniform parameter estimates produce an actual joint holomorphic limit.
The convergence and explicit tail bound hold on the full `U × closedBall`,
even when the parameter set is not compact. -/
theorem exists_joint_limit (A : P → E ≃L[ℂ] E) (T : P → E → E)
    {U : Set P} (hU : IsOpen U) {M q r C : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hrate : M * q ^ 2 < 1)
    (hAhol : DifferentiableOn ℂ (fun z : P × E => (A z.1).symm z.2) (U ×ˢ univ))
    (hThol : DifferentiableOn ℂ (fun z : P × E => T z.1 z.2) (U ×ˢ ball 0 r))
    (hA : ∀ p ∈ U, ∀ x, ‖(A p).symm x‖ ≤ M * ‖x‖)
    (hT : ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r, ‖T p x‖ ≤ q * ‖x‖)
    (hrem : ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r,
      ‖T p x - A p x‖ ≤ C * ‖x‖ ^ 2) :
    ∃ H : P × E → E,
      TendstoUniformlyOn (fun n z => rescaledIterate (A z.1) (T z.1) n z.2)
        H atTop (U ×ˢ closedBall 0 r) ∧
      DifferentiableOn ℂ H (U ×ˢ ball 0 r) ∧
      ∀ n, ∀ z ∈ U ×ˢ closedBall (0 : E) r,
        ‖H z - rescaledIterate (A z.1) (T z.1) n z.2‖ ≤
          (M * C * r ^ 2) * (M * q ^ 2) ^ n / (1 - M * q ^ 2) := by
  have hinv : ∀ p ∈ U, MapsTo (T p) (ball (0 : E) r) (ball 0 r) := by
    intro p hp x hx
    rw [mem_ball, dist_zero_right] at hx ⊢
    calc
      ‖T p x‖ ≤ q * ‖x‖ := hT p hp x (by simpa only [mem_closedBall, dist_zero_right] using hx.le)
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hq1 (norm_nonneg x)
      _ < r := by simpa using hx
  obtain ⟨H, hH, htail⟩ := NormalizedHolomorphicLimit.exists_uniformLimit_of_geometric
    (fun (n : ℕ) (z : P × E) => rescaledIterate (A z.1) (T z.1) n z.2)
    (U ×ˢ closedBall 0 r) (M * C * r ^ 2) (M * q ^ 2) (by positivity) hrate
    (fun n z hz => norm_rescaledIterate_sub_le hM hq hq1 hr hC
      (hA z.1 hz.1) (hT z.1 hz.1) (hrem z.1 hz.1) n z.2 hz.2)
  refine ⟨H, hH, ?_, htail⟩
  exact differentiableOn_of_tendstoUniformlyOn_open (hU.prod isOpen_ball)
    (differentiableOn_rescaledIterates A T hAhol hThol hinv)
    (hH.mono (prod_mono (Subset.refl _) ball_subset_closedBall))

omit [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace E] in
/-- The actual uniform limit satisfies conjugacy on every closed-ball fibre.
The equation is a consequence of the rescaled-iterate identity, not an extra
linearization assumption. -/
theorem conjugacy_of_uniform_limit (A : P → E ≃L[ℂ] E) (T : P → E → E)
    {U : Set P} {r q : ℝ} (hq1 : q ≤ 1)
    (hT : ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r, ‖T p x‖ ≤ q * ‖x‖)
    {H : P × E → E}
    (hH : TendstoUniformlyOn (fun n z => rescaledIterate (A z.1) (T z.1) n z.2)
      H atTop (U ×ˢ closedBall 0 r)) :
    ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r, H (p, T p x) = A p (H (p, x)) := by
  intro p hp x hx
  have hTx : T p x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right] at hx ⊢
    exact (hT p hp x (by simpa only [mem_closedBall, dist_zero_right] using hx)).trans
      ((mul_le_mul_of_nonneg_right hq1 (norm_nonneg x)).trans (by simpa using hx))
  have hleft := hH.tendsto_at (show (p, T p x) ∈ U ×ˢ closedBall 0 r from ⟨hp, hTx⟩)
  have hshift : Tendsto (fun n => rescaledIterate (A p) (T p) (n + 1) x)
      atTop (𝓝 (H (p, x))) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hH.tendsto_at (x := (p, x)) ⟨hp, hx⟩)
  have hright : Tendsto (fun n => A p (rescaledIterate (A p) (T p) (n + 1) x))
      atTop (𝓝 (A p (H (p, x)))) :=
    (A p).continuous.continuousAt.tendsto.comp hshift
  have heq : (fun n => rescaledIterate (A p) (T p) n (T p x)) =
      (fun n => A p (rescaledIterate (A p) (T p) (n + 1) x)) :=
    funext fun n => rescaledIterate_comp (A p) (T p) n x
  change Tendsto (fun n => rescaledIterate (A p) (T p) n (T p x)) atTop _ at hleft
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Origin values and fibre derivatives of a normalized rescaled family pass
to its uniform limit. This supplies the fibre normalization needed for a
subsequent inverse-function argument. -/
theorem normalization_of_uniform_limit (A : P → E ≃L[ℂ] E) (T : P → E → E)
    {U : Set P} {r : ℝ} (hr : 0 < r)
    (hd : ∀ n, DifferentiableOn ℂ
      (fun z : P × E => rescaledIterate (A z.1) (T z.1) n z.2) (U ×ˢ ball 0 r))
    (hT0 : ∀ p ∈ U, T p 0 = 0)
    (hTd : ∀ p ∈ U, HasFDerivAt (T p) ((A p) : E →L[ℂ] E) 0)
    {H : P × E → E}
    (hH : TendstoUniformlyOn (fun n z => rescaledIterate (A z.1) (T z.1) n z.2)
      H atTop (U ×ˢ closedBall 0 r)) :
    ∀ p ∈ U, H (p, 0) = 0 ∧
      HasFDerivAt (fun x => H (p, x)) (ContinuousLinearMap.id ℂ E) 0 := by
  intro p hp
  have hslice : TendstoUniformlyOn (fun n x => rescaledIterate (A p) (T p) n x)
      (fun x => H (p, x)) atTop (closedBall 0 r) :=
    (hH.comp (fun x : E => (p, x))).mono (fun _ hx => ⟨hp, hx⟩)
  have hf : ∀ n, DifferentiableOn ℂ (rescaledIterate (A p) (T p) n) (ball 0 r) := by
    intro n
    exact (hd n).comp ((differentiable_const p).prodMk differentiable_id).differentiableOn
      (fun _ hx => ⟨hp, hx⟩)
  have hzero : H (p, 0) = 0 := by
    have ht := hslice.tendsto_at (mem_closedBall_self hr.le)
    simp only [rescaledIterate_zero (A p) (hT0 p hp)] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hder := SeveralVariableUniformLimit.tendstoUniformlyOn_fderiv_ball hf
    (hslice.mono ball_subset_closedBall) (by linarith : r / 2 < r)
  have hdf : fderiv ℂ (fun x => H (p, x)) 0 = ContinuousLinearMap.id ℂ E := by
    have ht := hder.tendsto_at (mem_ball_self (half_pos hr))
    have hn : (fun n => fderiv ℂ (rescaledIterate (A p) (T p) n) 0) =
        fun _ => ContinuousLinearMap.id ℂ E := by
      funext n
      exact (hasFDerivAt_rescaledIterate_zero (A p) (hT0 p hp) (hTd p hp) n).fderiv
    rw [hn] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  refine ⟨hzero, ?_⟩
  rw [← hdf]
  exact ((SeveralVariableUniformLimit.differentiableOn_of_tendstoUniformlyOn_ball hf
    (hslice.mono ball_subset_closedBall)).differentiableAt (ball_mem_nhds 0 hr)).hasFDerivAt

/-- The joint Koenigs limit, its quantitative uniform convergence, its fibre
normalization, and its conjugacy equation in one existence statement. -/
theorem exists_normalized_joint_limit (A : P → E ≃L[ℂ] E) (T : P → E → E)
    {U : Set P} (hU : IsOpen U) {M q r C : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < r) (hC : 0 ≤ C)
    (hrate : M * q ^ 2 < 1)
    (hAhol : DifferentiableOn ℂ (fun z : P × E => (A z.1).symm z.2) (U ×ˢ univ))
    (hThol : DifferentiableOn ℂ (fun z : P × E => T z.1 z.2) (U ×ˢ ball 0 r))
    (hA : ∀ p ∈ U, ∀ x, ‖(A p).symm x‖ ≤ M * ‖x‖)
    (hT : ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r, ‖T p x‖ ≤ q * ‖x‖)
    (hrem : ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r,
      ‖T p x - A p x‖ ≤ C * ‖x‖ ^ 2)
    (hT0 : ∀ p ∈ U, T p 0 = 0)
    (hTd : ∀ p ∈ U, HasFDerivAt (T p) ((A p) : E →L[ℂ] E) 0) :
    ∃ H : P × E → E,
      TendstoUniformlyOn (fun n z => rescaledIterate (A z.1) (T z.1) n z.2)
        H atTop (U ×ˢ closedBall 0 r) ∧
      DifferentiableOn ℂ H (U ×ˢ ball 0 r) ∧
      (∀ n, ∀ z ∈ U ×ˢ closedBall (0 : E) r,
        ‖H z - rescaledIterate (A z.1) (T z.1) n z.2‖ ≤
          (M * C * r ^ 2) * (M * q ^ 2) ^ n / (1 - M * q ^ 2)) ∧
      (∀ p ∈ U, H (p, 0) = 0 ∧
        HasFDerivAt (fun x => H (p, x)) (ContinuousLinearMap.id ℂ E) 0) ∧
      ∀ p ∈ U, ∀ x ∈ closedBall (0 : E) r, H (p, T p x) = A p (H (p, x)) := by
  obtain ⟨H, hH, hdH, htail⟩ := exists_joint_limit A T hU hM hq hq1 hr.le hC hrate
    hAhol hThol hA hT hrem
  have hinv : ∀ p ∈ U, MapsTo (T p) (ball (0 : E) r) (ball 0 r) := by
    intro p hp x hx
    rw [mem_ball, dist_zero_right] at hx ⊢
    calc
      ‖T p x‖ ≤ q * ‖x‖ := hT p hp x (by simpa only [mem_closedBall, dist_zero_right] using hx.le)
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hq1 (norm_nonneg x)
      _ < r := by simpa using hx
  exact ⟨H, hH, hdH, htail,
    normalization_of_uniform_limit A T hr
      (differentiableOn_rescaledIterates A T hAhol hThol hinv) hT0 hTd hH,
    conjugacy_of_uniform_limit A T hq1 hT hH⟩

end JointDifferentiability

end AutomaticContinuity.UniformParameterKoenigs
