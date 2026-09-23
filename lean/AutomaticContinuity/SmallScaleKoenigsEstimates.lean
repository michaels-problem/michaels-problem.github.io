import AutomaticContinuity.KoenigsEstimates

set_option autoImplicit false

/-!
# Koenigs estimates at an arbitrarily small positive linear scale

The rescaled iterates are exactly those of `KoenigsEstimates`. A similarity
factor `0 < β ≤ 1/4`, together with a sufficiently small quadratic remainder,
gives the same summable `4/9` increment bound as the quarter-scale case.
-/

noncomputable section

namespace AutomaticContinuity.SmallScaleKoenigsEstimates

open Function Metric KoenigsEstimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_symm (A : E ≃L[ℂ] E) {β : ℝ} (hβ : 0 < β)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (x : E) :
    ‖A.symm x‖ = β⁻¹ * ‖x‖ := by
  have h := hA (A.symm x)
  rw [A.apply_symm_apply] at h
  calc
    ‖A.symm x‖ = β⁻¹ * (β * ‖A.symm x‖) := by field_simp
    _ = β⁻¹ * ‖x‖ := by rw [← h]

theorem norm_inversePower (A : E ≃L[ℂ] E) {β : ℝ} (hβ : 0 < β)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (n : ℕ) (x : E) :
    ‖inversePower A n x‖ = β⁻¹ ^ n * ‖x‖ := by
  induction n generalizing x with
  | zero => simp [inversePower]
  | succ n ih =>
      change ‖((A.symm : E →L[ℂ] E) ^ (n + 1)) x‖ = _
      rw [pow_succ, mul_apply_eq_comp]
      change ‖inversePower A n (A.symm x)‖ = _
      rw [ih, norm_symm A hβ hA, pow_succ]
      ring

omit [NormedSpace ℂ E] in
/-- Iteration of any nonnegative contraction factor at most one. -/
theorem norm_iterate_le {T : E → E} {r q : ℝ} (_hr : 0 ≤ r)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ q * ‖x‖)
    {x : E} (hx : x ∈ closedBall (0 : E) r) (n : ℕ) :
    ‖T^[n] x‖ ≤ q ^ n * ‖x‖ ∧ T^[n] x ∈ closedBall (0 : E) r := by
  induction n with
  | zero => simpa using And.intro (le_refl ‖x‖) hx
  | succ n ih =>
      have hn : ‖T (T^[n] x)‖ ≤ q ^ (n + 1) * ‖x‖ := by
        calc
          _ ≤ q * ‖T^[n] x‖ := hT _ ih.2
          _ ≤ q * (q ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih.1 hq
          _ = _ := by rw [pow_succ]; ring
      rw [Function.iterate_succ_apply']
      refine ⟨hn, ?_⟩
      apply mem_closedBall.mpr
      rw [dist_zero_right]
      have hi : ‖T^[n] x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using ih.2
      calc
        ‖T (T^[n] x)‖ ≤ q * ‖T^[n] x‖ := hT _ ih.2
        _ ≤ 1 * ‖T^[n] x‖ := mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ ≤ r := by simpa using hi

/-- A quadratic remainder small relative to the linear scale supplies the
contraction factor `(4/3) β`. -/
theorem contraction_of_quadratic_remainder {A : E ≃L[ℂ] E} {T : E → E}
    {β r C : ℝ} (hA : ∀ x, ‖A x‖ = β * ‖x‖) (hC : 0 ≤ C)
    (hsmall : C * r ≤ β / 3)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ ((4 / 3 : ℝ) * β) * ‖x‖ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  have hCr : C * ‖x‖ ≤ β / 3 := (mul_le_mul_of_nonneg_left hxnorm hC).trans hsmall
  have hn := norm_add_le (T x - A x) (A x)
  rw [sub_add_cancel, hA] at hn
  have herr := hrem x hx
  nlinarith [mul_le_mul_of_nonneg_right hCr (norm_nonneg x)]

/-- The exact geometric rate is `(16/9) β`. -/
theorem norm_rescaledIterate_sub_le_exact {A : E ≃L[ℂ] E} {T : E → E}
    {β r C : ℝ} (hβ : 0 < β) (hβquarter : β ≤ 1 / 4)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ ((4 / 3 : ℝ) * β) * ‖x‖)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2)
    (n : ℕ) (x : E) (hx : x ∈ closedBall (0 : E) r) :
    ‖rescaledIterate A T (n + 1) x - rescaledIterate A T n x‖ ≤
      (C / β * r ^ 2) * ((16 / 9 : ℝ) * β) ^ n := by
  obtain ⟨hn, hmem⟩ := norm_iterate_le hr (by positivity : 0 ≤ (4 / 3 : ℝ) * β)
    (by linarith : (4 / 3 : ℝ) * β ≤ 1) hT hx n
  rw [rescaledIterate_sub, norm_inversePower A hβ hA]
  have hxnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
  calc
    _ ≤ β⁻¹ ^ (n + 1) * (C * ‖T^[n] x‖ ^ 2) := by gcongr; exact hrem _ hmem
    _ ≤ β⁻¹ ^ (n + 1) * (C * ((((4 / 3 : ℝ) * β) ^ n * r) ^ 2)) := by
      gcongr
      exact hn.trans (mul_le_mul_of_nonneg_left hxnorm (by positivity))
    _ = (C / β * r ^ 2) * ((16 / 9 : ℝ) * β) ^ n := by
      rw [mul_pow, pow_succ]
      have hpow : (((4 / 3 : ℝ) * β) ^ n) ^ 2 = (((4 / 3 : ℝ) * β) ^ 2) ^ n :=
        (pow_mul _ n 2).symm.trans (by rw [Nat.mul_comm, pow_mul])
      rw [hpow]
      have hcombine : β⁻¹ ^ n * (((4 / 3 : ℝ) * β) ^ 2) ^ n =
          ((16 / 9 : ℝ) * β) ^ n := by
        rw [← mul_pow]
        congr 1
        field_simp
        ring
      calc
        _ = (C / β * r ^ 2) * (β⁻¹ ^ n * (((4 / 3 : ℝ) * β) ^ 2) ^ n) := by
          rw [div_eq_mul_inv]
          ring
        _ = _ := by rw [hcombine]

/-- All scales at most `1/4` share the summable rate `4/9`. -/
theorem norm_rescaledIterate_sub_le {A : E ≃L[ℂ] E} {T : E → E}
    {β r C : ℝ} (hβ : 0 < β) (hβquarter : β ≤ 1 / 4)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hT : ∀ x ∈ closedBall (0 : E) r, ‖T x‖ ≤ ((4 / 3 : ℝ) * β) * ‖x‖)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2)
    (n : ℕ) (x : E) (hx : x ∈ closedBall (0 : E) r) :
    ‖rescaledIterate A T (n + 1) x - rescaledIterate A T n x‖ ≤
      (C / β * r ^ 2) * (4 / 9 : ℝ) ^ n := by
  apply (norm_rescaledIterate_sub_le_exact hβ hβquarter hA hr hC hT hrem n x hx).trans
  gcongr
  linarith

/-- A convenient form deriving both iteration control and the increment
estimate solely from a sufficiently small quadratic remainder. -/
theorem norm_rescaledIterate_sub_le_of_remainder {A : E ≃L[ℂ] E} {T : E → E}
    {β r C : ℝ} (hβ : 0 < β) (hβquarter : β ≤ 1 / 4)
    (hA : ∀ x, ‖A x‖ = β * ‖x‖) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hsmall : C * r ≤ β / 3)
    (hrem : ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2)
    (n : ℕ) (x : E) (hx : x ∈ closedBall (0 : E) r) :
    ‖rescaledIterate A T (n + 1) x - rescaledIterate A T n x‖ ≤
      (C / β * r ^ 2) * (4 / 9 : ℝ) ^ n :=
  norm_rescaledIterate_sub_le hβ hβquarter hA hr hC
    (contraction_of_quadratic_remainder hA hC hsmall hrem) hrem n x hx

end AutomaticContinuity.SmallScaleKoenigsEstimates
