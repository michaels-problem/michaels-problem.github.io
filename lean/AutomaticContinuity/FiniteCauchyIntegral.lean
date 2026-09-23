import AutomaticContinuity.FiniteCauchyBounds
import AutomaticContinuity.FiniteGeometry
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp

/-!
# Finite iterated Cauchy coefficient integrals

These are actual contour integrals. Their coefficient bounds are proved here;
identifying them with a Taylor expansion requires the analytic lemmas developed
separately. No holomorphicity or radius compatibility is built into the definition.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set
open scoped BigOperators Real

/-- A one-variable coefficient integral on a positively oriented circle. -/
def circleCoeff (R : ℝ) (m : ℕ) (h : ℂ → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ z in C(0, R), h z / z ^ (m + 1)

/-- The sharp coefficient estimate only uses the bound on the contour. -/
theorem norm_circleCoeff_le {R M : ℝ} (hR : 0 < R) (m : ℕ) (h : ℂ → ℂ)
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ ≤ M) :
    ‖circleCoeff R m h‖ ≤ M / R ^ m := by
  have hb : ∀ z ∈ sphere (0 : ℂ) R,
      ‖h z / z ^ (m + 1)‖ ≤ M / R ^ (m + 1) := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [norm_div, norm_pow, hz']
    exact div_le_div_of_nonneg_right (hbound z hz) (pow_nonneg hR.le _)
  have hc := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hb
  change ‖circleCoeff R m h‖ ≤ _ at hc
  refine hc.trans_eq ?_
  rw [pow_succ]
  field_simp

/-- The finite product contour, with a separate radius for each coordinate. -/
def torus {n : ℕ} (R : Fin n → ℝ) : Set (FinitePoint n) :=
  {z | ∀ j, ‖z j‖ = R j}

/-- Integrate the last `n` coordinates before the initial coordinate. -/
def coefficient : {n : ℕ} → (Fin n → ℝ) → (FinitePoint n → ℂ) → FiniteMultiIndex n → ℂ
  | 0, _, h, _ => h Fin.elim0
  | _n + 1, R, h, α => circleCoeff (R 0) (α 0)
      (fun z => coefficient (Fin.tail R) (fun w => h (Fin.cons z w)) (Fin.tail α))

@[simp] theorem coefficient_zero (R : Fin 0 → ℝ) (h : FinitePoint 0 → ℂ)
    (α : FiniteMultiIndex 0) : coefficient R h α = h Fin.elim0 := rfl

@[simp] theorem coefficient_succ {n : ℕ} (R : Fin (n + 1) → ℝ)
    (h : FinitePoint (n + 1) → ℂ) (α : FiniteMultiIndex (n + 1)) :
    coefficient R h α = circleCoeff (R 0) (α 0)
      (fun z => coefficient (Fin.tail R) (fun w => h (Fin.cons z w)) (Fin.tail α)) := rfl

/-- The exact product-radius coefficient bound for the iterated integral. -/
theorem norm_coefficient_le {n : ℕ} (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    (h : FinitePoint n → ℂ) (M : ℝ)
    (hbound : ∀ z ∈ torus R, ‖h z‖ ≤ M) (α : FiniteMultiIndex n) :
    ‖coefficient R h α‖ ≤ M / ∏ j, R j ^ α j := by
  induction n with
  | zero =>
      simpa [coefficient] using hbound Fin.elim0 (by intro j; exact Fin.elim0 j)
  | succ n ih =>
      rw [coefficient_succ]
      have hb : ∀ z ∈ sphere (0 : ℂ) (R 0),
          ‖coefficient (Fin.tail R) (fun w => h (Fin.cons z w)) (Fin.tail α)‖ ≤
            M / ∏ j, (Fin.tail R j) ^ (Fin.tail α j) := by
        intro z hz
        apply ih (Fin.tail R) (fun j => hR j.succ)
        intro w hw
        apply hbound (Fin.cons z w)
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [Fin.cons_zero, mem_sphere, dist_zero_right] using hz
        · exact hw j
      refine (norm_circleCoeff_le (hR 0) (α 0) _ hb).trans_eq ?_
      rw [Fin.prod_univ_succ, div_div]
      congr 1
      exact mul_comm _ _

/-- At a common radius the product denominator is the total-degree power. -/
theorem norm_coefficient_le_common {n : ℕ} {R M : ℝ} (hR : 0 < R)
    (h : FinitePoint n → ℂ)
    (hbound : ∀ z ∈ polydisc n R, ‖h z‖ ≤ M) (α : FiniteMultiIndex n) :
    ‖coefficient (fun _ => R) h α‖ ≤ M / R ^ finiteTotalDegree α := by
  have hb : ∀ z ∈ torus (fun _ : Fin n => R), ‖h z‖ ≤ M := by
    intro z hz
    exact hbound z (fun j => (hz j).le)
  simpa only [Finset.prod_pow_eq_pow_sum, finiteTotalDegree] using
    norm_coefficient_le (fun _ => R) (fun _ => hR) h M hb α

/-- Taking a contour coefficient preserves continuous dependence on finite or
locally compact parameters. -/
theorem continuous_circleCoeff {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    {R : ℝ} (hR : 0 < R) (m : ℕ) (h : X → ℂ → ℂ)
    (hh : Continuous h.uncurry) :
    Continuous (fun x => circleCoeff R m (h x)) := by
  have hc : Continuous (fun p : X × ℝ => circleMap 0 R p.2) := by fun_prop
  have hne (p : X × ℝ) : circleMap 0 R p.2 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_circleMap_zero, abs_of_pos hR]
    exact hR.ne'
  have hd : Continuous (fun p : X × ℝ => deriv (circleMap 0 R) p.2) := by
    simp_rw [deriv_circleMap]
    fun_prop
  have hh' : Continuous (fun p : X × ℝ => h p.1 (circleMap 0 R p.2)) :=
    hh.comp (continuous_fst.prodMk hc)
  have hkernel : Continuous (fun p : X × ℝ =>
      deriv (circleMap 0 R) p.2 *
        (h p.1 (circleMap 0 R p.2) / (circleMap 0 R p.2) ^ (m + 1))) :=
    hd.mul (hh'.div (hc.pow _) (fun p => pow_ne_zero _ (hne p)))
  have hi := continuous_parametric_integral_of_continuous
    (μ := MeasureTheory.volume)
    (s := Icc (0 : ℝ) (2 * Real.pi))
    (f := fun x θ => deriv (circleMap 0 R) θ *
      (h x (circleMap 0 R θ) / (circleMap 0 R θ) ^ (m + 1)))
    hkernel isCompact_Icc
  have hic : Continuous (fun x => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∫ θ in Icc (0 : ℝ) (2 * Real.pi), deriv (circleMap 0 R) θ *
        (h x (circleMap 0 R θ) / (circleMap 0 R θ) ^ (m + 1))) :=
    continuous_const.mul hi
  simpa only [circleCoeff, circleIntegral_def_Icc, smul_eq_mul] using hic

/-- The iterated coefficient depends continuously on locally compact parameters. -/
theorem continuous_coefficient {n : ℕ} {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (R : Fin n → ℝ) (hR : ∀ j, 0 < R j) (h : X → FinitePoint n → ℂ)
    (hh : Continuous h.uncurry) (α : FiniteMultiIndex n) :
    Continuous (fun x => coefficient R (h x) α) := by
  induction n generalizing X with
  | zero =>
      exact hh.comp (continuous_id.prodMk continuous_const)
  | succ n ih =>
      apply continuous_circleCoeff (hR 0) (α 0)
      apply ih (Fin.tail R) (fun j => hR j.succ)
      exact hh.comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.finCons continuous_snd))

theorem circleCoeff_congr {R : ℝ} (hR : 0 ≤ R) (m : ℕ) {h k : ℂ → ℂ}
    (heq : EqOn h k (sphere (0 : ℂ) R)) : circleCoeff R m h = circleCoeff R m k := by
  unfold circleCoeff
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact congrArg (fun v : ℂ => v / z ^ (m + 1)) (heq hz)

theorem circleIntegrable_coefficientKernel {R : ℝ} (hR : 0 < R) (m : ℕ)
    {h : ℂ → ℂ} (hh : Continuous h) :
    CircleIntegrable (fun z => h z / z ^ (m + 1)) 0 R := by
  apply ContinuousOn.circleIntegrable hR.le
  apply hh.continuousOn.div (continuousOn_id.pow _)
  intro z hz
  apply pow_ne_zero
  intro hz0
  change z = 0 at hz0
  have hz' : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
  rw [hz0, norm_zero] at hz'
  exact hR.ne hz'

theorem circleCoeff_sub {R : ℝ} (hR : 0 < R) (m : ℕ)
    {h k : ℂ → ℂ} (hh : Continuous h) (hk : Continuous k) :
    circleCoeff R m (fun z => h z - k z) = circleCoeff R m h - circleCoeff R m k := by
  simp only [circleCoeff, sub_div]
  rw [circleIntegral.integral_sub (circleIntegrable_coefficientKernel hR m hh)
    (circleIntegrable_coefficientKernel hR m hk), mul_sub]

theorem circleCoeff_const_mul (R : ℝ) (m : ℕ) (c : ℂ) (h : ℂ → ℂ) :
    circleCoeff R m (fun z => c * h z) = c * circleCoeff R m h := by
  simp only [circleCoeff, mul_div_assoc]
  rw [circleIntegral.integral_const_mul]
  ring

theorem coefficient_sub {n : ℕ} (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {h k : FinitePoint n → ℂ} (hh : Continuous h) (hk : Continuous k)
    (α : FiniteMultiIndex n) :
    coefficient R (fun z => h z - k z) α = coefficient R h α - coefficient R k α := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coefficient_succ]
      have heq (z : ℂ) :
          coefficient (Fin.tail R) (fun w => h (Fin.cons z w) - k (Fin.cons z w))
            (Fin.tail α) =
          coefficient (Fin.tail R) (fun w => h (Fin.cons z w)) (Fin.tail α) -
            coefficient (Fin.tail R) (fun w => k (Fin.cons z w)) (Fin.tail α) :=
        ih (Fin.tail R) (fun j => hR j.succ)
          (hh.comp (continuous_const.finCons continuous_id))
          (hk.comp (continuous_const.finCons continuous_id)) (Fin.tail α)
      simp_rw [heq]
      apply circleCoeff_sub (hR 0)
      · exact continuous_coefficient _ (fun j => hR j.succ) (fun z w => h (Fin.cons z w))
          (hh.comp (continuous_fst.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_snd)) _
      · exact continuous_coefficient _ (fun j => hR j.succ) (fun z w => k (Fin.cons z w))
          (hk.comp (continuous_fst.finCons (A := fun _ : Fin (n + 1) => ℂ) continuous_snd)) _

theorem coefficient_const_mul {n : ℕ} (R : Fin n → ℝ) (c : ℂ)
    (h : FinitePoint n → ℂ) (α : FiniteMultiIndex n) :
    coefficient R (fun z => c * h z) α = c * coefficient R h α := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coefficient_succ]
      simp_rw [ih]
      exact circleCoeff_const_mul _ _ _ _

end AutomaticContinuity.FiniteCauchy
