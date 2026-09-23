import AutomaticContinuity.PolynomialFamilyEvaluation
import AutomaticContinuity.PolynomialFamilyRegularity
import AutomaticContinuity.CompactCutoffTubes
import AutomaticContinuity.EuclideanPairRotations

set_option autoImplicit false

/-! # A polynomial separator survives a sufficiently accurate radial push

One cubic amplification restores a strict scalar margin after fibre dilation.
Compactness makes that margin stable under one common positive perturbation.
The updated separator is an actual polynomial family of degree at most three
times the original bound, with the same local coefficient regularity.
-/

noncomputable section

namespace AutomaticContinuity.RadialSeparatorPropagation

open Set Metric PolynomialCutoff FlagTotalSpace
open PolynomialFamilyRegularity RadialPolynomialField

abbrev Pair := ℂ × ℂ
abbrev Poly := MvPolynomial (Fin 2) ℂ

variable {P : Type*}

def dilate (b : ℝ) (z : P × Pair) : P × Pair := (z.1, b • z.2)

def nextCutoff (q : P × Pair → ℂ) (b : ℝ) (z : P × Pair) : ℂ :=
  smoothStep (q (z.1, b⁻¹ • z.2))

theorem nextCutoff_dilate (q : P × Pair → ℂ) {b : ℝ} (hb : b ≠ 0) (z : P × Pair) :
    nextCutoff q b (dilate b z) = smoothStep (q z) := by
  simp [nextCutoff, dilate, smul_smul, inv_mul_cancel₀ hb]

theorem nextCutoff_small {q : P × Pair → ℂ} {L : Set P} {a b : ℝ}
    (hb : 0 < b)
    (hzero : ∀ z ∈ L ×ˢ closedEuclideanBall a, ‖q z‖ ≤ 1 / 16) :
    ∀ z ∈ L ×ˢ closedEuclideanBall (b * a), ‖nextCutoff q b z‖ ≤ 1 / 32 := by
  intro z hz
  have hmem : (z.1, b⁻¹ • z.2) ∈ L ×ˢ closedEuclideanBall a := by
    refine ⟨hz.1, ?_⟩
    change euclideanPairNorm (b⁻¹ • z.2) ≤ a
    rw [euclideanPairNorm_real_smul (inv_nonneg.mpr hb.le)]
    calc
      b⁻¹ * euclideanPairNorm z.2 ≤ b⁻¹ * (b * a) :=
        mul_le_mul_of_nonneg_left hz.2 (inv_nonneg.mpr hb.le)
      _ = a := by rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
  have hq := hzero _ hmem
  exact (norm_smoothStep_le (hq.trans (by norm_num))).trans (by linarith)

section Topology

variable [PseudoMetricSpace P]

theorem continuous_dilate (b : ℝ) : Continuous (dilate (P := P) b) := by
  unfold dilate
  fun_prop

theorem continuousOn_nextCutoff {q : P × Pair → ℂ} {U : Set P} (b : ℝ)
    (hq : ContinuousOn q (U ×ˢ univ)) :
    ContinuousOn (nextCutoff q b) (U ×ˢ univ) := by
  have hi : Continuous (fun z : P × Pair => (z.1, b⁻¹ • z.2)) :=
    by fun_prop
  have hs : Continuous smoothStep := by unfold smoothStep; fun_prop
  exact hs.comp_continuousOn (hq.comp hi.continuousOn (fun _ hz => ⟨hz.1, mem_univ _⟩))

/-- The perturbation radius is uniform on the entire compact obstacle. The
map being tested need not have regularity for this implication. -/
theorem exists_perturbation_radius (q : P × Pair → ℂ) {K : Set (P × Pair)}
    {U : Set P} {b : ℝ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U ×ˢ univ) (hb : 0 < b)
    (hq : ContinuousOn q (U ×ˢ univ))
    (hone : ∀ z ∈ K, ‖q z - 1‖ ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Ψ : P × Pair → Pair,
      (∀ z ∈ K, euclideanPairNorm (Ψ z - b • z.2) < δ) →
      ∀ z ∈ K, ‖nextCutoff q b (z.1, Ψ z) - 1‖ < 1 / 16 := by
  let S := dilate b '' K
  have hS : IsCompact S := hK.image (continuous_dilate b)
  let V := (U ×ˢ (univ : Set Pair)) ∩
    (fun z => ‖nextCutoff q b z - 1‖) ⁻¹' Iio (1 / 16)
  have hV : IsOpen V :=
    (((continuousOn_nextCutoff b hq).sub continuousOn_const).norm).isOpen_inter_preimage
      (hU.prod isOpen_univ) isOpen_Iio
  have hSV : S ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨(hKU hz).1, mem_univ _⟩, ?_⟩
    change ‖nextCutoff q b (dilate b z) - 1‖ < 1 / 16
    rw [nextCutoff_dilate q hb.ne']
    have hh := norm_smoothStep_sub_one_le ((hone z hz).trans (by norm_num))
    linarith [hone z hz]
  obtain ⟨δ, hδ, hδV⟩ := hS.exists_cthickening_subset_open hV hSV
  refine ⟨δ, hδ, ?_⟩
  intro Ψ hΨ z hz
  have hdist : dist (z.1, Ψ z) (dilate b z) ≤ δ := by
    change max (dist z.1 z.1) (dist (Ψ z) (b • z.2)) ≤ δ
    rw [dist_self, max_eq_right dist_nonneg, dist_eq_norm]
    exact (norm_le_euclideanPairNorm _).trans (hΨ z hz).le
  have hmem : (z.1, Ψ z) ∈ cthickening δ S :=
    mem_cthickening_of_dist_le _ (dilate b z) δ S ⟨z, hz, rfl⟩ hdist
  exact (hδV hmem).2

theorem isCompact_image {K : Set (P × Pair)} (hK : IsCompact K)
    {Ψ : P × Pair → Pair} (hΨ : ContinuousOn Ψ K) :
    IsCompact ((fun z => (z.1, Ψ z)) '' K) :=
  hK.image_of_continuousOn (continuousOn_fst.prodMk hΨ)

end Topology

/-- The actual next polynomial; a single cubic iterate is enough. -/
def nextPolynomial (q : Poly) (b : ℝ) : Poly :=
  iterate (rescale ((b : ℂ)⁻¹) q) 1

theorem eval_nextPolynomial (q : P → Poly) (b : ℝ) (z : P × Pair) :
    MvPolynomial.eval ![z.2.1, z.2.2] (nextPolynomial (q z.1) b) =
      nextCutoff (fun w : P × Pair => MvPolynomial.eval ![w.2.1, w.2.2] (q w.1)) b z := by
  rw [nextPolynomial, eval_iterate_succ, eval_iterate_zero, eval_rescale]
  congr 3
  funext i
  fin_cases i <;> simp [Complex.real_smul, Complex.ofReal_inv]

theorem nextPolynomial_degree (q : Poly) (b : ℝ) :
    (nextPolynomial q b).totalDegree ≤ 3 * q.totalDegree := by
  exact (totalDegree_iterate_le _ 1).trans (by
    simpa only [pow_one] using Nat.mul_le_mul_left 3 (totalDegree_rescale_le q _))

theorem continuousCoefficientsOn_nextPolynomial {X : Type*} [TopologicalSpace X]
    {q : X → Poly} {U : Set X} (b : ℝ) (hq : ContinuousCoefficientsOn q U) :
    ContinuousCoefficientsOn (fun p => nextPolynomial (q p) b) U :=
  (hq.rescale continuousOn_const).iterate 1

theorem holomorphicCoefficientsOn_nextPolynomial {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {q : X → Poly} {U : Set X}
    (b : ℝ) (hq : HolomorphicCoefficientsOn q U) :
    HolomorphicCoefficientsOn (fun p => nextPolynomial (q p) b) U :=
  (hq.rescale (differentiableOn_const _)).iterate 1

theorem nextPolynomial_small {q : P → Poly} {L : Set P} {a b : ℝ}
    (hb : 0 < b)
    (hzero : ∀ z ∈ L ×ˢ closedEuclideanBall a,
      ‖MvPolynomial.eval ![z.2.1, z.2.2] (q z.1)‖ ≤ 1 / 16) :
    ∀ z ∈ L ×ˢ closedEuclideanBall (b * a),
      ‖MvPolynomial.eval ![z.2.1, z.2.2] (nextPolynomial (q z.1) b)‖ ≤ 1 / 32 := by
  intro z hz
  rw [eval_nextPolynomial]
  exact nextCutoff_small hb hzero z hz

/-- The perturbation tolerance for actual polynomial families. The same
updated polynomial works for every sufficiently accurate map. -/
theorem exists_polynomial_perturbation_radius
    [NormedAddCommGroup P] [NormedSpace ℂ P] (D : ℕ) (q : P → Poly)
    {K : Set (P × Pair)} {U : Set P} {b : ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U ×ˢ univ) (hb : 0 < b)
    (hdegree : ∀ p ∈ U, (q p).totalDegree ≤ D)
    (hq : HolomorphicCoefficientsOn q U)
    (hone : ∀ z ∈ K, ‖MvPolynomial.eval ![z.2.1, z.2.2] (q z.1) - 1‖ ≤ 1 / 16) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Ψ : P × Pair → Pair,
      (∀ z ∈ K, euclideanPairNorm (Ψ z - b • z.2) < δ) →
      ∀ z ∈ K, ‖MvPolynomial.eval ![(Ψ z).1, (Ψ z).2]
        (nextPolynomial (q z.1) b) - 1‖ < 1 / 16 := by
  have hcontinuous : ContinuousOn
      (fun z : P × Pair => MvPolynomial.eval ![z.2.1, z.2.2] (q z.1))
      (U ×ˢ univ) :=
    (PolynomialFamilyEvaluation.continuousOn_joint_eval D hdegree
      (fun α => (hq α).continuousOn)).mono (fun _ hz => hz.1)
  obtain ⟨δ, hδ, hprop⟩ := exists_perturbation_radius _ hK hU hKU hb hcontinuous hone
  refine ⟨δ, hδ, ?_⟩
  intro Ψ hΨ z hz
  have hh := hprop Ψ hΨ z hz
  rw [← eval_nextPolynomial q b (z.1, Ψ z)] at hh
  exact hh

theorem image_subset_base {K : Set (P × Pair)} {L : Set P}
    (hKL : K ⊆ L ×ˢ univ) (Ψ : P × Pair → Pair) :
    (fun z => (z.1, Ψ z)) '' K ⊆ L ×ˢ univ := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨(hKL hz).1, mem_univ _⟩

end AutomaticContinuity.RadialSeparatorPropagation
