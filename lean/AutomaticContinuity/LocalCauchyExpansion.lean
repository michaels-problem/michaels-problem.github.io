import AutomaticContinuity.FiniteCauchyExpansion

/-!
# Local finite-polydisc Cauchy expansion

Only continuity on the full ambient space is used for parameterized contour
integrals. Complex differentiability is required on the one closed polydisc
containing the contours; no entire-function assumption is made.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set
open scoped BigOperators Real

set_option backward.isDefEq.respectTransparency false in
theorem hasSum_ratio_pow_finiteTotalDegree (n : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HasSum (fun α : FiniteMultiIndex n => ρ ^ finiteTotalDegree α) ((1 - ρ)⁻¹ ^ n) := by
  classical
  induction n with
  | zero => simp [finiteTotalDegree]
  | succ n ih =>
      have hgeom : HasSum (fun j : ℕ => ρ ^ j) (1 - ρ)⁻¹ :=
        hasSum_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hρ0] using hρ1)
      have hmul : Summable (fun p : ℕ × FiniteMultiIndex n =>
          ρ ^ p.1 * ρ ^ finiteTotalDegree p.2) :=
        Summable.mul_of_nonneg
          (f := fun j : ℕ => ρ ^ j)
          (g := fun α : FiniteMultiIndex n => ρ ^ finiteTotalDegree α)
          hgeom.summable ih.summable (fun j => pow_nonneg hρ0 j)
          (fun α => pow_nonneg hρ0 (finiteTotalDegree α))
      have hprod : HasSum (fun p : ℕ × FiniteMultiIndex n =>
          ρ ^ p.1 * ρ ^ finiteTotalDegree p.2) ((1 - ρ)⁻¹ * (1 - ρ)⁻¹ ^ n) :=
        HasSum.mul (f := fun j : ℕ => ρ ^ j)
          (g := fun α : FiniteMultiIndex n => ρ ^ finiteTotalDegree α)
          hgeom ih hmul
      apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff.mp
      simpa [Function.comp_def, Fin.consEquiv, finiteTotalDegree,
        Fin.sum_univ_succ, pow_add, pow_succ'] using hprod

theorem norm_coefficient_mul_monomial_le_ratio {n : ℕ} {r R M : ℝ}
    (hr : 0 ≤ r) (hR : 0 < R) (h : FinitePoint n → ℂ)
    (hbound : ∀ w ∈ polydisc n R, ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) (α : FiniteMultiIndex n) :
    ‖coefficient (fun _ => R) h α * monomial z α‖ ≤
      M * (r / R) ^ finiteTotalDegree α := by
  calc
    ‖coefficient (fun _ => R) h α * monomial z α‖ ≤
        ‖coefficient (fun _ => R) h α‖ * r ^ finiteTotalDegree α := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_monomial_le hr z hz α) (norm_nonneg _)
    _ ≤ (M / R ^ finiteTotalDegree α) * r ^ finiteTotalDegree α :=
      mul_le_mul_of_nonneg_right (norm_coefficient_le_common hR h hbound α) (pow_nonneg hr _)
    _ = M * (r / R) ^ finiteTotalDegree α := by rw [div_pow]; ring

theorem summable_coefficient_mul_monomial_of_lt {n : ℕ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (h : FinitePoint n → ℂ)
    (hbound : ∀ w ∈ polydisc n R, ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) :
    Summable (fun α => coefficient (fun _ => R) h α * monomial z α) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hρ0 : 0 ≤ r / R := div_nonneg hr hR.le
  have hρ1 : r / R < 1 := (div_lt_one hR).mpr hrR
  exact ((hasSum_ratio_pow_finiteTotalDegree n hρ0 hρ1).summable.mul_left M).of_norm_bounded
    (norm_coefficient_mul_monomial_le_ratio hr hR h hbound z hz)

/-- Cauchy's formula on a single closed disc, with the exact normalization used
by the finite coefficient integrals. -/
theorem normalized_cauchyIntegral_eq_of_differentiableOn {h : ℂ → ℂ} {R : ℝ}
    (hh : DifferentiableOn ℂ h (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, R), h ζ / (ζ - z)) = h z := by
  have hformula := (hh.mono closure_ball_subset_closedBall).diffContOnCl
    |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
      (show z ∈ ball (0 : ℂ) R by simpa only [mem_ball, dist_zero_right] using hz)
  simpa only [smul_eq_mul, div_eq_inv_mul] using hformula

private theorem circleCoeff_mul_const_local (R : ℝ) (m : ℕ) (c : ℂ) (h : ℂ → ℂ) :
    circleCoeff R m (fun z => h z * c) = circleCoeff R m h * c := by
  simpa only [mul_comm] using circleCoeff_const_mul R m c h

/-- A local holomorphic function has its coefficient expansion throughout every
strictly smaller closed polydisc. Global continuity is sufficient for contour
parameter dependence; complex differentiability is used only on the outer disc. -/
theorem hasSum_coefficient_mul_monomial_local_of_bound {n : ℕ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 ≤ M) (h : FinitePoint n → ℂ)
    (hhc : Continuous h) (hhd : DifferentiableOn ℂ h (polydisc n R))
    (hbound : ∀ w ∈ polydisc n R, ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) :
    HasSum (fun α => coefficient (fun _ => R) h α * monomial z α) (h z) := by
  have hR : 0 < R := hr.trans_lt hrR
  have hρ0 : 0 ≤ r / R := div_nonneg hr hR.le
  have hρ1 : r / R < 1 := (div_lt_one hR).mpr hrR
  induction n with
  | zero =>
      have heq : h Fin.elim0 = h z := congrArg h (Subsingleton.elim _ _)
      simp [coefficient, monomial, heq]
  | succ n ih =>
      have hz0 : ‖z 0‖ < R := (hz 0).trans_lt hrR
      have hzTail : Fin.tail z ∈ polydisc n r := fun j => hz j.succ
      let b : FiniteMultiIndex n → ℂ → ℂ := fun β ζ =>
        coefficient (fun _ => R) (fun w => h (Fin.cons ζ w)) β * monomial (Fin.tail z) β
      let g : ℂ → ℂ := fun ζ => h (Fin.cons ζ (Fin.tail z))
      have hbcont (β : FiniteMultiIndex n) : Continuous (b β) :=
        (continuous_coefficient (fun _ => R) (fun _ => hR)
          (fun ζ w => h (Fin.cons ζ w))
          (hhc.comp
            (continuous_fst.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_snd)) β).mul_const _
      have htailCont (ζ : ℂ) : Continuous (fun w : FinitePoint n => h (Fin.cons ζ w)) :=
        hhc.comp (continuous_const.finCons continuous_id)
      have hconsMem (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R)
          (w : FinitePoint n) (hw : w ∈ polydisc n R) : Fin.cons ζ w ∈ polydisc (n + 1) R := by
        intro j
        refine Fin.cases ?_ (fun j => hw j) j
        have heq : ‖ζ‖ = R := by simpa only [mem_sphere, dist_zero_right] using hζ
        exact heq.le
      have hsliceBound (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) :
          ∀ w ∈ polydisc n R, ‖h (Fin.cons ζ w)‖ ≤ M :=
        fun w hw => hbound _ (hconsMem ζ hζ w hw)
      have hsliceDiff (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) :
          DifferentiableOn ℂ (fun w : FinitePoint n => h (Fin.cons ζ w)) (polydisc n R) :=
        hhd.comp ((differentiable_const ζ).finCons differentiable_id).differentiableOn
          (hconsMem ζ hζ)
      have hbBound (β : FiniteMultiIndex n) (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) :
          ‖b β ζ‖ ≤ M * (r / R) ^ finiteTotalDegree β :=
        norm_coefficient_mul_monomial_le_ratio hr hR _ (hsliceBound ζ hζ) _ hzTail β
      have hbSum (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) :
          HasSum (fun β => b β ζ) (g ζ) :=
        ih (fun w => h (Fin.cons ζ w)) (htailCont ζ) (hsliceDiff ζ hζ)
          (hsliceBound ζ hζ) (Fin.tail z) hzTail
      have hsumIntegral := hasSum_cauchyIntegral_of_summable_bound hR hz0 b g hbcont
        (fun β => M * (r / R) ^ finiteTotalDegree β)
        ((hasSum_ratio_pow_finiteTotalDegree n hρ0 hρ1).summable.mul_left M)
        (fun β => mul_nonneg hM (pow_nonneg hρ0 _)) hbBound hbSum
      have hg : DifferentiableOn ℂ g (closedBall 0 R) := by
        apply hhd.comp (differentiable_id.finCons
          (differentiable_const (Fin.tail z))).differentiableOn
        intro ζ hζ j
        refine Fin.cases ?_ (fun j => (hzTail j).trans hrR.le) j
        simpa only [mem_closedBall, dist_zero_right, Fin.cons_zero, id_eq] using hζ
      have hintegral :
          ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, R), g ζ / (ζ - z 0)) = h z := by
        simpa [g] using normalized_cauchyIntegral_eq_of_differentiableOn hg hz0
      rw [hintegral] at hsumIntegral
      let e : (FiniteMultiIndex n × ℕ) ≃ FiniteMultiIndex (n + 1) :=
        (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))
      let t : FiniteMultiIndex (n + 1) → ℂ :=
        fun α => coefficient (fun _ => R) h α * monomial z α
      have hs : Summable (fun p : FiniteMultiIndex n × ℕ => t (e p)) :=
        (e.summable_iff (f := t)).mpr
          (summable_coefficient_mul_monomial_of_lt hr hrR h hbound z hz)
      have hrow (β : FiniteMultiIndex n) :
          HasSum (fun m => t (e (β, m)))
            ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, R), b β ζ / (ζ - z 0)) := by
        have hgeneric := OneVariableCauchy.hasSum_circleCoeff_mul_pow_integral_of_continuousOn
          (hbcont β).continuousOn hz0
        convert hgeneric using 1
        funext m
        change coefficient (fun _ => R) h (Fin.cons m β) * monomial z (Fin.cons m β) =
          circleCoeff R m (b β) * z 0 ^ m
        rw [monomial_cons]
        change (circleCoeff R m (fun ζ =>
          coefficient (fun _ => R) (fun w => h (Fin.cons ζ w)) β)) *
            (z 0 ^ m * monomial (Fin.tail z) β) =
          circleCoeff R m (fun ζ => coefficient (fun _ => R) (fun w => h (Fin.cons ζ w)) β *
              monomial (Fin.tail z) β) * z 0 ^ m
        rw [circleCoeff_mul_const_local]
        ring
      have heq := (hs.hasSum.prod_fiberwise hrow).unique hsumIntegral
      apply (e.hasSum_iff (f := t)).mp
      exact heq ▸ hs.hasSum

end AutomaticContinuity.FiniteCauchy
