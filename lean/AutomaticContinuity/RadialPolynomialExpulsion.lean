import AutomaticContinuity.RadialPolynomialPush

set_option autoImplicit false

/-! # Expelling a separated compact beyond any prescribed fibre radius -/

noncomputable section

namespace AutomaticContinuity.RadialPolynomialPush

open Set RadialPolynomialField RadialPolynomialFamily
open PolynomialFamilyRegularity (HolomorphicCoefficientsOn)

variable {P : Type*}

/-- The two scalar cutoff margins already imply strict geometric separation
from the protected cylinder. -/
theorem outside_protected_ball (q : P → Poly) {L : Set P} {K : Set (P × Pair)} {a : ℝ}
    (hKL : K ⊆ L ×ˢ univ)
    (hzero : ∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a, ‖value q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖value q z - 1‖ ≤ 1 / 16) {z : P × Pair} (hz : z ∈ K) :
    a < euclideanPairNorm z.2 := by
  by_contra hnot
  have hsmall := hzero z ⟨(hKL hz).1, le_of_not_gt hnot⟩
  have hlarge := hone z hz
  have htri := norm_sub_le (value q z) (value q z - 1)
  have heq : value q z - (value q z - 1) = 1 := by ring
  rw [heq, norm_one] at htri
  linarith

private theorem euclidean_reverse_triangle (v w : Pair) :
    euclideanPairNorm v ≤ euclideanPairNorm (w - v) + euclideanPairNorm w := by
  have hh := euclideanPairNorm_add_le (v - w) w
  have hrev : euclideanPairNorm (v - w) = euclideanPairNorm (w - v) := by
    change Real.sqrt (‖v.1 - w.1‖ ^ 2 + ‖v.2 - w.2‖ ^ 2) = _
    rw [norm_sub_rev v.1 w.1, norm_sub_rev v.2 w.2]
    rfl
  rwa [sub_add_cancel, hrev] at hh

variable [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

/-- For every target radius, a single actual holomorphic fibre automorphism
expels the separated compact beyond that radius, while its forward and inverse
remain as close to the identity as prescribed on the original cylinder. -/
theorem exists_expelling_push (q : P → Poly) (D : ℕ)
    {L U : Set P} {K : Set (P × Pair)} {a ε : ℝ} (r : ℝ)
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U) (hLU : L ⊆ U)
    (hKL : K ⊆ L ×ˢ univ) (ha : 0 < a) (hε : 0 < ε)
    (hq : HolomorphicCoefficientsOn q U)
    (hdegree : ∀ p ∈ U, (q p).totalDegree ≤ D)
    (hzero : ∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a, ‖value q z‖ ≤ 1 / 16)
    (hone : ∀ z ∈ K, ‖value q z - 1‖ ≤ 1 / 16) :
    ∃ Φ : P → Pair ≃ₜ Pair,
      (∀ p, Φ p 0 = 0) ∧
      DifferentiableOn ℂ (fun z : P × Pair => Φ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : P × Pair => (Φ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ z ∈ L ×ˢ FlagTotalSpace.closedEuclideanBall a,
        euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
        euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
      (∀ z ∈ K, r < euclideanPairNorm (Φ z.1 z.2)) := by
  obtain ⟨c, hc, hca⟩ := exists_pos_lt_mul ha (r + ε)
  obtain ⟨Φ, hΦ0, hΦhol, hΦinv, hΦprot, hΦrad⟩ :=
    exists_compact_push q D hL hK hU hLU hKL hc.le hε hq hdegree hzero hone
  refine ⟨Φ, hΦ0, hΦhol, hΦinv, hΦprot, ?_⟩
  intro z hz
  have hsep := outside_protected_ball q hKL hzero hone hz
  have hrad : r + ε < (1 + c) * euclideanPairNorm z.2 := by
    apply hca.trans_le
    calc
      c * a ≤ c * euclideanPairNorm z.2 := mul_le_mul_of_nonneg_left hsep.le hc.le
      _ ≤ (1 + c) * euclideanPairNorm z.2 :=
        mul_le_mul_of_nonneg_right (by linarith) (euclideanPairNorm_nonneg _)
  have htri := euclidean_reverse_triangle ((1 + c) • z.2) (Φ z.1 z.2)
  rw [euclideanPairNorm_real_smul (by linarith : 0 ≤ 1 + c)] at htri
  have herr := hΦrad z hz
  linarith

end AutomaticContinuity.RadialPolynomialPush
