import AutomaticContinuity.EuclideanBallGeometry
import AutomaticContinuity.OneVariableCauchy
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# An explicit polynomial automorphism with a trapped ball and exterior fixed point

The Hermite peak has prescribed value and zero first derivative at an exterior
point, while both its value and derivative vanish at the origin. Its norm tends
uniformly to zero on a smaller disc. Inserting it into a two-coordinate Henon
map gives an entire bijection with explicit entire inverse. For a sufficiently
large exponent it traps the closed Euclidean ball, fixes an exterior point, and
has derivative there equal to one quarter of a coordinate rotation.

No Fatou--Bieberbach basin theorem, parameterized construction, or Oka conclusion
is asserted here. Those would require additional analytic arguments.
-/

noncomputable section

namespace AutomaticContinuity.HenonTrapping

open Complex Metric Filter
open scoped Topology

/-- Exponent `m+2` guarantees the vanishing first-order jet at zero. -/
def hermitePeak (a A : ℂ) (m : ℕ) (u : ℂ) : ℂ :=
  A * (u / a) ^ (m + 2) * ((m : ℂ) + 3 - ((m : ℂ) + 2) * (u / a))

/-- The peak is literally a polynomial, including the zero-denominator convention. -/
def hermitePeakPolynomial (a A : ℂ) (m : ℕ) : Polynomial ℂ :=
  Polynomial.C A * (Polynomial.X * Polynomial.C a⁻¹) ^ (m + 2) *
    (Polynomial.C ((m : ℂ) + 3) -
      Polynomial.C ((m : ℂ) + 2) * (Polynomial.X * Polynomial.C a⁻¹))

@[simp] theorem eval_hermitePeakPolynomial (a A u : ℂ) (m : ℕ) :
    (hermitePeakPolynomial a A m).eval u = hermitePeak a A m u := by
  simp only [hermitePeakPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_sub, hermitePeak, div_eq_mul_inv]

@[fun_prop] theorem differentiable_hermitePeak (a A : ℂ) (m : ℕ) :
    Differentiable ℂ (hermitePeak a A m) := by
  simpa only [eval_hermitePeakPolynomial] using (hermitePeakPolynomial a A m).differentiable

@[simp] theorem hermitePeak_zero (a A : ℂ) (m : ℕ) : hermitePeak a A m 0 = 0 := by
  simp [hermitePeak, pow_succ]

@[simp] theorem hermitePeak_self {a : ℂ} (ha : a ≠ 0) (A : ℂ) (m : ℕ) :
    hermitePeak a A m a = A := by
  simp [hermitePeak, ha]
  ring

theorem hasDerivAt_hermitePeak_zero (a A : ℂ) (m : ℕ) :
    HasDerivAt (hermitePeak a A m) 0 0 := by
  have hu : HasDerivAt (fun u : ℂ => u / a) (1 / a) 0 := (hasDerivAt_id 0).div_const a
  have hl := (hasDerivAt_const 0 ((m : ℂ) + 3)).sub (hu.const_mul ((m : ℂ) + 2))
  have hp := ((hu.pow (m + 2)).mul hl).const_mul A
  have hm : m + 2 - 1 = m + 1 := by omega
  convert! hp using 1
  · funext u
    dsimp [hermitePeak]
    ring
  · simp [hm, pow_succ]

theorem hasDerivAt_hermitePeak_self {a : ℂ} (ha : a ≠ 0) (A : ℂ) (m : ℕ) :
    HasDerivAt (hermitePeak a A m) 0 a := by
  have hu : HasDerivAt (fun u : ℂ => u / a) (1 / a) a := (hasDerivAt_id a).div_const a
  have hl := (hasDerivAt_const a ((m : ℂ) + 3)).sub (hu.const_mul ((m : ℂ) + 2))
  have hp := ((hu.pow (m + 2)).mul hl).const_mul A
  convert! hp using 1
  · funext u
    dsimp [hermitePeak]
    ring
  · simp only [Pi.sub_apply, Pi.pow_apply, div_self ha, one_pow, Nat.cast_add, Nat.cast_ofNat]
    ring

theorem norm_hermitePeak_le {a A u : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hu : ‖u‖ ≤ r) (m : ℕ) :
    ‖hermitePeak a A m u‖ ≤ ‖A‖ * (r / ‖a‖) ^ (m + 2) *
      ((m : ℝ) + 3 + ((m : ℝ) + 2) * (r / ‖a‖)) := by
  have hρ : 0 ≤ r / ‖a‖ := div_nonneg hr (norm_nonneg a)
  have hdiv : ‖u / a‖ ≤ r / ‖a‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hu (norm_nonneg a)
  have hconst (k : ℕ) : ‖(m : ℂ) + k‖ = (m : ℝ) + k := by
    rw [← Nat.cast_add, Complex.norm_natCast, Nat.cast_add]
  have hc3 : ‖(m : ℂ) + 3‖ = (m : ℝ) + 3 := by simpa only [Nat.cast_ofNat] using hconst 3
  have hc2 : ‖(m : ℂ) + 2‖ = (m : ℝ) + 2 := by simpa only [Nat.cast_ofNat] using hconst 2
  have hl : ‖(m : ℂ) + 3 - ((m : ℂ) + 2) * (u / a)‖ ≤
      (m : ℝ) + 3 + ((m : ℝ) + 2) * (r / ‖a‖) := by
    calc
      _ ≤ ‖(m : ℂ) + 3‖ + ‖((m : ℂ) + 2) * (u / a)‖ := norm_sub_le _ _
      _ = (m : ℝ) + 3 + ((m : ℝ) + 2) * ‖u / a‖ := by
        rw [norm_mul, hc3, hc2]
      _ ≤ _ := by gcongr
  rw [hermitePeak, norm_mul, norm_mul, norm_pow]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdiv _) (norm_nonneg _)
  · exact hl
  · exact norm_nonneg _
  · positivity

theorem tendsto_hermitePeak_bound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (A : ℂ) :
    Tendsto (fun m : ℕ => ‖A‖ * ρ ^ (m + 2) *
      ((m : ℝ) + 3 + ((m : ℝ) + 2) * ρ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hmp := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
  have ht := ((hmp.const_mul (1 + ρ)).add (hp.const_mul (3 + 2 * ρ))).const_mul (‖A‖ * ρ ^ 2)
  convert! ht using 1
  · funext m
    rw [pow_add]
    ring
  · ring

/-- An actual finite exponent makes the Hermite peak uniformly small on the
whole smaller closed disc, with an arbitrary positive tolerance. -/
theorem exists_hermitePeak_small {a A : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hra : r < ‖a‖) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ u : ℂ, ‖u‖ ≤ r → ‖hermitePeak a A m u‖ < ε := by
  have ha : 0 < ‖a‖ := hr.trans_lt hra
  have ht := tendsto_hermitePeak_bound (div_nonneg hr ha.le) ((div_lt_one ha).mpr hra) A
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨m, fun u hu => (norm_hermitePeak_le hr hu m).trans_lt hm⟩

/-- The exterior fixed point for the symmetric coupling `b=c=1/4`. -/
def exteriorPoint (a : ℂ) : ℂ × ℂ := (a, (1 / 4 : ℂ) * a)

def henonMap (a : ℂ) (m : ℕ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (hermitePeak a ((17 / 16 : ℂ) * a) m v.1 - (1 / 4 : ℂ) * v.2,
    (1 / 4 : ℂ) * v.1)

def henonInverse (a : ℂ) (m : ℕ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (4 * v.2, 4 * (hermitePeak a ((17 / 16 : ℂ) * a) m (4 * v.2) - v.1))

theorem henonInverse_left (a : ℂ) (m : ℕ) : Function.LeftInverse (henonInverse a m) (henonMap a m) := by
  intro v
  ext <;> simp [henonMap, henonInverse]

theorem henonInverse_right (a : ℂ) (m : ℕ) : Function.RightInverse (henonInverse a m) (henonMap a m) := by
  intro v
  ext <;> simp [henonMap, henonInverse]

def henonEquiv (a : ℂ) (m : ℕ) : (ℂ × ℂ) ≃ (ℂ × ℂ) where
  toFun := henonMap a m
  invFun := henonInverse a m
  left_inv := henonInverse_left a m
  right_inv := henonInverse_right a m

theorem henonMap_bijective (a : ℂ) (m : ℕ) : Function.Bijective (henonMap a m) :=
  (henonEquiv a m).bijective

theorem differentiable_henonMap (a : ℂ) (m : ℕ) : Differentiable ℂ (henonMap a m) := by
  change Differentiable ℂ (fun v : ℂ × ℂ =>
    (hermitePeak a ((17 / 16 : ℂ) * a) m v.1 - (1 / 4 : ℂ) * v.2, (1 / 4 : ℂ) * v.1))
  fun_prop

theorem differentiable_henonInverse (a : ℂ) (m : ℕ) : Differentiable ℂ (henonInverse a m) := by
  change Differentiable ℂ (fun v : ℂ × ℂ =>
    (4 * v.2, 4 * (hermitePeak a ((17 / 16 : ℂ) * a) m (4 * v.2) - v.1)))
  fun_prop

@[simp] theorem henonMap_zero (a : ℂ) (m : ℕ) : henonMap a m 0 = 0 := by
  simp [henonMap]

theorem henonMap_exteriorPoint {a : ℂ} (ha : a ≠ 0) (m : ℕ) :
    henonMap a m (exteriorPoint a) = exteriorPoint a := by
  apply Prod.ext
  · change hermitePeak a ((17 / 16 : ℂ) * a) m a - (1 / 4 : ℂ) * ((1 / 4 : ℂ) * a) = a
    rw [hermitePeak_self ha]
    ring
  · rfl

/-- The derivative is one quarter of the coordinate rotation `(u,v) -> (-v,u)`. -/
def henonDerivative : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (-(1 / 4 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((1 / 4 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem henonDerivative_apply (v : ℂ × ℂ) :
    henonDerivative v = (-(1 / 4 : ℂ) * v.2, (1 / 4 : ℂ) * v.1) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_henonMap_of_peak_deriv_zero (a : ℂ) (m : ℕ) (v : ℂ × ℂ)
    (hq : HasDerivAt (hermitePeak a ((17 / 16 : ℂ) * a) m) 0 v.1) :
    HasFDerivAt (henonMap a m) henonDerivative v := by
  have hq' : HasFDerivAt (hermitePeak a ((17 / 16 : ℂ) * a) m)
      (0 : ℂ →L[ℂ] ℂ) v.1 := by
    simpa using hq.hasFDerivAt
  have hqfst : HasFDerivAt (fun w : ℂ × ℂ => hermitePeak a ((17 / 16 : ℂ) * a) m w.1)
      (0 : (ℂ × ℂ) →L[ℂ] ℂ) v := by
    simpa using! hq'.comp v (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
  have hsnd := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := v) |>.const_smul (1 / 4 : ℂ)
  have hfst := (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt (x := v) |>.const_smul (1 / 4 : ℂ)
  convert! (hqfst.sub hsnd).prodMk hfst using 1
  ext <;> simp [henonDerivative, smul_eq_mul]

theorem hasFDerivAt_henonMap_zero (a : ℂ) (m : ℕ) :
    HasFDerivAt (henonMap a m) henonDerivative 0 :=
  hasFDerivAt_henonMap_of_peak_deriv_zero a m 0 (hasDerivAt_hermitePeak_zero a _ m)

theorem hasFDerivAt_henonMap_exteriorPoint {a : ℂ} (ha : a ≠ 0) (m : ℕ) :
    HasFDerivAt (henonMap a m) henonDerivative (exteriorPoint a) :=
  hasFDerivAt_henonMap_of_peak_deriv_zero a m (exteriorPoint a) (hasDerivAt_hermitePeak_self ha _ m)

theorem euclideanPairNorm_henonDerivative (v : ℂ × ℂ) :
    euclideanPairNorm (henonDerivative v) = (1 / 4 : ℝ) * euclideanPairNorm v := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _)
    (mul_nonneg (by norm_num) (euclideanPairNorm_nonneg v))).mp
  rw [euclideanPairNorm_sq, mul_pow, euclideanPairNorm_sq, henonDerivative_apply]
  simp only [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  ring

theorem henonMap_traps_ball_of_peak_bound {a : ℂ} {m : ℕ} {r : ℝ} (hr : 0 < r)
    (hq : ∀ u : ℂ, ‖u‖ ≤ r → ‖hermitePeak a ((17 / 16 : ℂ) * a) m u‖ ≤ r / 4) :
    ∀ v : ℂ × ℂ, euclideanPairNorm v ≤ r → euclideanPairNorm (henonMap a m v) < r := by
  intro v hv
  have hv1 : ‖v.1‖ ≤ r := (norm_fst_le_euclideanPairNorm v).trans hv
  have hv2 : ‖v.2‖ ≤ r := (norm_snd_le_euclideanPairNorm v).trans hv
  have hfirst : ‖(henonMap a m v).1‖ ≤ r / 2 := by
    dsimp [henonMap]
    calc
      _ ≤ ‖hermitePeak a ((17 / 16 : ℂ) * a) m v.1‖ + ‖(1 / 4 : ℂ) * v.2‖ := norm_sub_le _ _
      _ ≤ r / 4 + (1 / 4 : ℝ) * r := by
        rw [norm_mul]
        norm_num
        nlinarith [hq v.1 hv1]
      _ = r / 2 := by ring
  have hsecond : ‖(henonMap a m v).2‖ ≤ r / 4 := by
    dsimp [henonMap]
    rw [norm_mul]
    norm_num
    linarith
  exact (euclideanPairNorm_le_sum _).trans_lt (by linarith)

/-- A concrete finite exponent produces a polynomial automorphism trapping the
closed Euclidean ball and with an exterior fixed point whose derivative is a
strict Euclidean contraction. No basin parameterization is assumed. -/
theorem exists_henon_trapping {a : ℂ} {r : ℝ} (hr : 0 < r) (hra : r < ‖a‖) :
    ∃ m : ℕ,
      (∀ v : ℂ × ℂ, euclideanPairNorm v ≤ r → euclideanPairNorm (henonMap a m v) < r) ∧
      henonMap a m (exteriorPoint a) = exteriorPoint a ∧
      r < euclideanPairNorm (exteriorPoint a) ∧
      HasFDerivAt (henonMap a m) henonDerivative (exteriorPoint a) := by
  have ha : a ≠ 0 := norm_pos_iff.mp (hr.trans hra)
  obtain ⟨m, hm⟩ := exists_hermitePeak_small (A := (17 / 16 : ℂ) * a) hr.le hra
    (show 0 < r / 4 by positivity)
  exact ⟨m, henonMap_traps_ball_of_peak_bound hr (fun u hu => (hm u hu).le),
    henonMap_exteriorPoint ha m,
    hra.trans_le (norm_fst_le_euclideanPairNorm (exteriorPoint a)),
    hasFDerivAt_henonMap_exteriorPoint ha m⟩

end AutomaticContinuity.HenonTrapping
