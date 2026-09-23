import AutomaticContinuity.HenonTrapping

/-!
# Explicit small-scale Hénon trapping maps

The coupling scale is a real number `β ∈ (0, 1/4]`. The derivative at either
fixed point scales both the actual Euclidean norm and the ambient product norm
by exactly `β`. A sufficiently large finite Hermite exponent traps a prescribed
closed Euclidean ball, while the second fixed point stays outside it.
-/

noncomputable section

namespace AutomaticContinuity.SmallScaleHenonTrapping

open HenonTrapping Complex Metric Filter
open scoped Topology

def peakAmplitude (β : ℝ) (a : ℂ) : ℂ := (1 + (β : ℂ) ^ 2) * a

def exteriorPoint (β : ℝ) (a : ℂ) : ℂ × ℂ := (a, (β : ℂ) * a)

def henonMap (β : ℝ) (a : ℂ) (m : ℕ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (hermitePeak a (peakAmplitude β a) m v.1 - (β : ℂ) * v.2,
    (β : ℂ) * v.1)

def henonInverse (β : ℝ) (a : ℂ) (m : ℕ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (v.2 / (β : ℂ), (hermitePeak a (peakAmplitude β a) m (v.2 / (β : ℂ)) - v.1) / (β : ℂ))

theorem henonInverse_left {β : ℝ} (hβ : β ≠ 0) (a : ℂ) (m : ℕ) :
    Function.LeftInverse (henonInverse β a m) (henonMap β a m) := by
  have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  intro v
  ext <;> simp [henonMap, henonInverse, hb]

theorem henonInverse_right {β : ℝ} (hβ : β ≠ 0) (a : ℂ) (m : ℕ) :
    Function.RightInverse (henonInverse β a m) (henonMap β a m) := by
  have hb : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  intro v
  ext <;> dsimp [henonMap, henonInverse]
  · field_simp
    ring
  · field_simp

def henonEquiv {β : ℝ} (hβ : β ≠ 0) (a : ℂ) (m : ℕ) : (ℂ × ℂ) ≃ (ℂ × ℂ) where
  toFun := henonMap β a m
  invFun := henonInverse β a m
  left_inv := henonInverse_left hβ a m
  right_inv := henonInverse_right hβ a m

theorem henonMap_bijective {β : ℝ} (hβ : β ≠ 0) (a : ℂ) (m : ℕ) :
    Function.Bijective (henonMap β a m) := (henonEquiv hβ a m).bijective

@[fun_prop] theorem differentiable_henonMap (β : ℝ) (a : ℂ) (m : ℕ) :
    Differentiable ℂ (henonMap β a m) := by
  change Differentiable ℂ (fun v : ℂ × ℂ =>
    (hermitePeak a (peakAmplitude β a) m v.1 - (β : ℂ) * v.2, (β : ℂ) * v.1))
  fun_prop

@[fun_prop] theorem differentiable_henonInverse (β : ℝ) (a : ℂ) (m : ℕ) :
    Differentiable ℂ (henonInverse β a m) := by
  change Differentiable ℂ (fun v : ℂ × ℂ =>
    (v.2 / (β : ℂ), (hermitePeak a (peakAmplitude β a) m (v.2 / (β : ℂ)) - v.1) / (β : ℂ)))
  fun_prop

def henonHomeomorph {β : ℝ} (hβ : β ≠ 0) (a : ℂ) (m : ℕ) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toEquiv := henonEquiv hβ a m
  continuous_toFun := (differentiable_henonMap β a m).continuous
  continuous_invFun := (differentiable_henonInverse β a m).continuous

@[simp] theorem henonMap_zero (β : ℝ) (a : ℂ) (m : ℕ) : henonMap β a m 0 = 0 := by
  simp [henonMap]

theorem henonMap_exteriorPoint {a : ℂ} (ha : a ≠ 0) (β : ℝ) (m : ℕ) :
    henonMap β a m (exteriorPoint β a) = exteriorPoint β a := by
  apply Prod.ext
  · change hermitePeak a (peakAmplitude β a) m a - (β : ℂ) * ((β : ℂ) * a) = a
    rw [hermitePeak_self ha]
    dsimp [peakAmplitude]
    ring
  · rfl

def henonDerivative (β : ℝ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (-(β : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((β : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem henonDerivative_apply (β : ℝ) (v : ℂ × ℂ) :
    henonDerivative β v = (-(β : ℂ) * v.2, (β : ℂ) * v.1) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_henonMap_of_peak_deriv_zero (β : ℝ) (a : ℂ) (m : ℕ) (v : ℂ × ℂ)
    (hq : HasDerivAt (hermitePeak a (peakAmplitude β a) m) 0 v.1) :
    HasFDerivAt (henonMap β a m) (henonDerivative β) v := by
  have hq' : HasFDerivAt (hermitePeak a (peakAmplitude β a) m)
      (0 : ℂ →L[ℂ] ℂ) v.1 := by
    simpa using hq.hasFDerivAt
  have hqfst : HasFDerivAt (fun w : ℂ × ℂ => hermitePeak a (peakAmplitude β a) m w.1)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) v := by
    simpa using! hq'.comp v (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
  have hsnd := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := v) |>.const_smul (β : ℂ)
  have hfst := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt (x := v) |>.const_smul (β : ℂ)
  convert! (hqfst.sub hsnd).prodMk hfst using 1
  ext <;> simp [henonDerivative, smul_eq_mul]

theorem hasFDerivAt_henonMap_zero (β : ℝ) (a : ℂ) (m : ℕ) :
    HasFDerivAt (henonMap β a m) (henonDerivative β) 0 :=
  hasFDerivAt_henonMap_of_peak_deriv_zero β a m 0 (hasDerivAt_hermitePeak_zero a _ m)

theorem hasFDerivAt_henonMap_exteriorPoint {a : ℂ} (ha : a ≠ 0) (β : ℝ) (m : ℕ) :
    HasFDerivAt (henonMap β a m) (henonDerivative β) (exteriorPoint β a) :=
  hasFDerivAt_henonMap_of_peak_deriv_zero β a m (exteriorPoint β a)
    (hasDerivAt_hermitePeak_self ha _ m)

theorem euclideanPairNorm_henonDerivative {β : ℝ} (hβ : 0 ≤ β) (v : ℂ × ℂ) :
    euclideanPairNorm (henonDerivative β v) = β * euclideanPairNorm v := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _)
    (mul_nonneg hβ (euclideanPairNorm_nonneg v))).mp
  rw [euclideanPairNorm_sq, mul_pow, euclideanPairNorm_sq, henonDerivative_apply]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
  ring

theorem norm_henonDerivative {β : ℝ} (hβ : 0 ≤ β) (v : ℂ × ℂ) :
    ‖henonDerivative β v‖ = β * ‖v‖ := by
  rw [henonDerivative_apply, Prod.norm_def, Prod.norm_def]
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
  rw [mul_max_of_nonneg _ _ hβ, max_comm]

theorem henonMap_traps_ball_of_peak_bound {β : ℝ} (hβ : 0 ≤ β) (hβq : β ≤ 1 / 4)
    {a : ℂ} {m : ℕ} {r : ℝ} (hr : 0 < r)
    (hq : ∀ u : ℂ, ‖u‖ ≤ r → ‖hermitePeak a (peakAmplitude β a) m u‖ ≤ r / 4) :
    ∀ v : ℂ × ℂ, euclideanPairNorm v ≤ r → euclideanPairNorm (henonMap β a m v) < r := by
  intro v hv
  have hv1 : ‖v.1‖ ≤ r := (norm_fst_le_euclideanPairNorm v).trans hv
  have hv2 : ‖v.2‖ ≤ r := (norm_snd_le_euclideanPairNorm v).trans hv
  have hfirst : ‖(henonMap β a m v).1‖ ≤ r / 2 := by
    dsimp [henonMap]
    calc
      _ ≤ ‖hermitePeak a (peakAmplitude β a) m v.1‖ + ‖(β : ℂ) * v.2‖ := norm_sub_le _ _
      _ ≤ r / 4 + β * r := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
        exact add_le_add (hq v.1 hv1) (mul_le_mul_of_nonneg_left hv2 hβ)
      _ ≤ r / 2 := by nlinarith
  have hsecond : ‖(henonMap β a m v).2‖ ≤ r / 4 := by
    dsimp [henonMap]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
    exact (mul_le_mul_of_nonneg_left hv1 hβ).trans (by nlinarith)
  exact (euclideanPairNorm_le_sum _).trans_lt (by linarith)

theorem exists_henon_trapping {β : ℝ} (hβ : 0 < β) (hβq : β ≤ 1 / 4)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hra : r < ‖a‖) :
    ∃ m : ℕ,
      (∀ v : ℂ × ℂ, euclideanPairNorm v ≤ r → euclideanPairNorm (henonMap β a m v) < r) ∧
      henonMap β a m (exteriorPoint β a) = exteriorPoint β a ∧
      r < euclideanPairNorm (exteriorPoint β a) ∧
      HasFDerivAt (henonMap β a m) (henonDerivative β) (exteriorPoint β a) := by
  have ha : a ≠ 0 := norm_pos_iff.mp (hr.trans hra)
  obtain ⟨m, hm⟩ := exists_hermitePeak_small (A := peakAmplitude β a) hr.le hra
    (show 0 < r / 4 by positivity)
  exact ⟨m, henonMap_traps_ball_of_peak_bound hβ.le hβq hr (fun u hu => (hm u hu).le),
    henonMap_exteriorPoint ha β m,
    hra.trans_le (norm_fst_le_euclideanPairNorm (exteriorPoint β a)),
    hasFDerivAt_henonMap_exteriorPoint ha β m⟩

end AutomaticContinuity.SmallScaleHenonTrapping
