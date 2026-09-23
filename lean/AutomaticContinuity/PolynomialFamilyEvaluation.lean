import AutomaticContinuity.PolynomialFieldArrays

set_option autoImplicit false

/-! # Joint evaluation of coefficientwise regular polynomial families

A common degree bound turns actual polynomial evaluation into one fixed finite
sum. No topology on the space of all multivariate polynomials is introduced.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFamilyEvaluation

open MvPolynomial HomogeneousPowerBasis PolynomialFieldArrays
open scoped BigOperators

theorem sum_homogeneousComponents (D : ℕ) (q : Poly) (hq : q.totalDegree ≤ D) :
    (∑ d : Fin (D + 1), homogeneousComponent d.val q) = q := by
  have heq : (∑ d ∈ Finset.range (q.totalDegree + 1), homogeneousComponent d q) =
      ∑ d ∈ Finset.range (D + 1), homogeneousComponent d q := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hq))
    intro d _ hnot
    exact homogeneousComponent_eq_zero d q (by
      simp only [Finset.mem_range] at hnot
      omega)
  rw [sum_homogeneousComponent] at heq
  rw [← Fin.sum_univ_eq_sum_range] at heq
  exact heq.symm

/-- A fixed finite formula for evaluation, including the constant term. -/
theorem eval_eq_sum (D : ℕ) (q : Poly) (hq : q.totalDegree ≤ D) (w : ℂ × ℂ) :
    eval ![w.1, w.2] q = ∑ d : Fin (D + 1), ∑ k : Fin (d.val + 1),
      q.coeff (degreeExponent d.val k) * w.1 ^ (d.val - k.val) * w.2 ^ k.val := by
  conv_lhs => rw [← sum_homogeneousComponents D q hq]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← sum_coeff_monomialAt d.val q]
  simp only [map_sum, smul_eq_C_mul, monomialAt, map_mul, map_pow,
    eval_C, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuousOn_joint_eval {P : Type*} [TopologicalSpace P]
    (D : ℕ) {U : Set P} {q : P → Poly}
    (hq : ∀ p ∈ U, (q p).totalDegree ≤ D)
    (hc : ∀ α, ContinuousOn (fun p => (q p).coeff α) U) :
    ContinuousOn (fun z : P × (ℂ × ℂ) => eval ![z.2.1, z.2.2] (q z.1))
      {z | z.1 ∈ U} := by
  have hs : ContinuousOn (fun z : P × (ℂ × ℂ) =>
      ∑ d : Fin (D + 1), ∑ k : Fin (d.val + 1),
      (q z.1).coeff (degreeExponent d.val k) *
        z.2.1 ^ (d.val - k.val) * z.2.2 ^ k.val) {z | z.1 ∈ U} := by
    apply continuousOn_finsetSum
    intro d _
    apply continuousOn_finsetSum
    intro k _
    have hcoef : ContinuousOn (fun z : P × (ℂ × ℂ) =>
        (q z.1).coeff (degreeExponent d.val k)) {z | z.1 ∈ U} :=
      (hc (degreeExponent d.val k)).comp continuousOn_fst (fun _ hz => hz)
    exact (hcoef.mul ((continuous_snd.fst.pow _).continuousOn)).mul
      ((continuous_snd.snd.pow _).continuousOn)
  apply hs.congr
  intro z hz
  exact eval_eq_sum D (q z.1) (hq z.1 hz) z.2

theorem differentiableOn_joint_eval {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℂ P] (D : ℕ) {U : Set P} {q : P → Poly}
    (hq : ∀ p ∈ U, (q p).totalDegree ≤ D)
    (hc : ∀ α, DifferentiableOn ℂ (fun p => (q p).coeff α) U) :
    DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) => eval ![z.2.1, z.2.2] (q z.1))
      {z | z.1 ∈ U} := by
  have hs : DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) =>
      ∑ d : Fin (D + 1), ∑ k : Fin (d.val + 1),
      (q z.1).coeff (degreeExponent d.val k) *
        z.2.1 ^ (d.val - k.val) * z.2.2 ^ k.val) {z | z.1 ∈ U} := by
    apply DifferentiableOn.fun_sum
    intro d _
    apply DifferentiableOn.fun_sum
    intro k _
    have hcoef : DifferentiableOn ℂ (fun z : P × (ℂ × ℂ) =>
        (q z.1).coeff (degreeExponent d.val k)) {z | z.1 ∈ U} :=
      (hc (degreeExponent d.val k)).comp differentiableOn_fst (fun _ hz => hz)
    exact (hcoef.mul ((differentiable_snd.fst.pow _).differentiableOn)).mul
      ((differentiable_snd.snd.pow _).differentiableOn)
  apply hs.congr
  intro z hz
  exact eval_eq_sum D (q z.1) (hq z.1 hz) z.2

end AutomaticContinuity.PolynomialFamilyEvaluation
