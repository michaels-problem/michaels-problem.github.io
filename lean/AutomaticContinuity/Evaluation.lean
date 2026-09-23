import AutomaticContinuity.Coefficients
import AutomaticContinuity.Flags

/-! # Absolutely convergent evaluations

Evaluation here is an analytic sum of the coefficients. It is deliberately
separate from Mathlib's adic evaluation of formal power series, whose hypotheses
do not cover arbitrary bounded complex sequences.
-/

noncomputable section

namespace AutomaticContinuity

/-- Evaluate a finite monomial at an arbitrary complex sequence. -/
def monomialValue (w : ℕ → ℂ) (α : MultiIndex) : ℂ :=
  α.prod (fun j n => w j ^ n)

@[simp] theorem monomialValue_zero (w : ℕ → ℂ) : monomialValue w 0 = 1 := by
  simp [monomialValue]

@[simp] theorem monomialValue_single (w : ℕ → ℂ) (j n : ℕ) :
    monomialValue w (Finsupp.single j n) = w j ^ n := by
  simp [monomialValue]

theorem monomialValue_add (w : ℕ → ℂ) (α β : MultiIndex) :
    monomialValue w (α + β) = monomialValue w α * monomialValue w β := by
  simp [monomialValue, Finsupp.prod_add_index, pow_add]

theorem norm_monomialValue_le {w : ℕ → ℂ} {R : ℝ}
    (_hR : 0 ≤ R) (hw : ∀ j, ‖w j‖ ≤ R) (α : MultiIndex) :
    ‖monomialValue w α‖ ≤ R ^ totalDegree α := by
  classical
  unfold monomialValue Finsupp.prod
  rw [norm_prod]
  calc
    (∏ j ∈ α.support, ‖w j ^ α j‖) ≤ ∏ j ∈ α.support, R ^ α j := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hw j) _
    _ = R ^ totalDegree α := by
      simp [totalDegree, Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]

/-- A bounded complex sequence has an integral radius at least one. -/
theorem BoundedSequence.exists_integral_radius (w : BoundedSequence) :
    ∃ R : ℕ, 0 < R ∧ ∀ j, ‖w.val j‖ ≤ (R : ℝ) := by
  obtain ⟨C, hC⟩ := w.property
  obtain ⟨R, hR⟩ := exists_nat_gt (max C 0)
  refine ⟨R, ?_, fun j => (hC j).trans (le_max_left _ _) |>.trans hR.le⟩
  exact_mod_cast (lt_of_le_of_lt (le_max_right C 0) hR)

namespace CoefficientSeries

/-- The analytic value of an entire coefficient series at a bounded sequence. -/
def evaluate (w : BoundedSequence) (f : CoefficientSeries) : ℂ :=
  ∑' α : MultiIndex, coeff f α * monomialValue w.val α

theorem norm_evaluationTerm_le (w : BoundedSequence) (f : CoefficientSeries)
    {R : ℕ} (hw : ∀ j, ‖w.val j‖ ≤ (R : ℝ)) (α : MultiIndex) :
    ‖coeff f α * monomialValue w.val α‖ ≤ weightedTerm R (f : FormalSeries) α := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_monomialValue_le (Nat.cast_nonneg R) hw α) (norm_nonneg _)

/-- The series defining evaluation converges absolutely. -/
theorem summable_evaluation_norm (w : BoundedSequence) (f : CoefficientSeries) :
    Summable (fun α : MultiIndex => ‖coeff f α * monomialValue w.val α‖) := by
  obtain ⟨R, hR, hw⟩ := w.exists_integral_radius
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_evaluationTerm_le w f hw) (summable f hR)

theorem summable_evaluation (w : BoundedSequence) (f : CoefficientSeries) :
    Summable (fun α : MultiIndex => coeff f α * monomialValue w.val α) :=
  (summable_evaluation_norm w f).of_norm

/-- The manuscript's evaluation estimate, at every adequate integral radius. -/
theorem norm_evaluate_le (w : BoundedSequence) (f : CoefficientSeries)
    {R : ℕ} (hR : 0 < R) (hw : ∀ j, ‖w.val j‖ ≤ (R : ℝ)) :
    ‖evaluate w f‖ ≤ q R f := by
  exact tsum_of_norm_bounded (summable f hR).hasSum (norm_evaluationTerm_le w f hw)

@[simp] theorem evaluate_monomial (w : BoundedSequence) (α : MultiIndex) (c : ℂ) :
    evaluate w (monomial α c) = c * monomialValue w.val α := by
  classical
  unfold evaluate
  rw [tsum_eq_single α]
  · simp
  · intro β hβα
    simp [hβα]

@[simp] theorem evaluate_coordinate (w : BoundedSequence) (j : ℕ) :
    evaluate w (coordinate j) = w.val j := by
  simp [coordinate]

@[simp] theorem evaluate_constant (w : BoundedSequence) (c : ℂ) :
    evaluate w (constant c) = c := by
  change evaluate w (monomial 0 c) = c
  simp

@[simp] theorem evaluate_add (w : BoundedSequence) (f g : CoefficientSeries) :
    evaluate w (f + g) = evaluate w f + evaluate w g := by
  unfold evaluate
  simp only [coeff, Subalgebra.coe_add, map_add, add_mul]
  exact (summable_evaluation w f).tsum_add (summable_evaluation w g)

@[simp] theorem evaluate_smul (w : BoundedSequence) (c : ℂ) (f : CoefficientSeries) :
    evaluate w (c • f) = c * evaluate w f := by
  unfold evaluate
  simp only [coeff, Subalgebra.coe_smul, MvPowerSeries.coeff_smul,
    mul_assoc, tsum_mul_left]

set_option maxHeartbeats 800000 in
@[simp] theorem evaluate_mul (w : BoundedSequence) (f g : CoefficientSeries) :
    evaluate w (f * g) = evaluate w f * evaluate w g := by
  classical
  calc
    evaluate w (f * g) = ∑' α : MultiIndex, ∑ p ∈ Finset.antidiagonal α,
        (coeff f p.1 * monomialValue w.val p.1) *
        (coeff g p.2 * monomialValue w.val p.2) := by
      apply tsum_congr
      intro α
      simp only [coeff, Subalgebra.coe_mul, MvPowerSeries.coeff_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hsum : p.1 + p.2 = α := Finset.mem_antidiagonal.mp hp
      rw [← hsum, monomialValue_add]
      ring
    _ = evaluate w f * evaluate w g := by
      let a : MultiIndex → ℂ := fun α => coeff f α * monomialValue w.val α
      let b : MultiIndex → ℂ := fun α => coeff g α * monomialValue w.val α
      have ha : Summable a := summable_evaluation w f
      have hb : Summable b := summable_evaluation w g
      have hab : Summable (fun p : MultiIndex × MultiIndex => a p.1 * b p.2) :=
        summable_mul_of_summable_norm
          (summable_evaluation_norm w f) (summable_evaluation_norm w g)
      exact (Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
        (f := a) (g := b) ha hb hab).symm

/-- Evaluation at a bounded sequence is a genuine unital algebra homomorphism. -/
def evaluationHom (w : BoundedSequence) : CoefficientSeries →ₐ[ℂ] ℂ where
  toFun := evaluate w
  map_one' := by
    change evaluate w (constant 1) = 1
    simp
  map_mul' := evaluate_mul w
  map_zero' := by
    simp [evaluate, coeff]
  map_add' := evaluate_add w
  commutes' c := by
    change evaluate w (constant c) = c
    simp

@[simp] theorem evaluationHom_apply (w : BoundedSequence) (f : CoefficientSeries) :
    evaluationHom w f = evaluate w f := rfl

end CoefficientSeries

end AutomaticContinuity
