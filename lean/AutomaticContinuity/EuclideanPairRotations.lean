import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# Complex linear rotations of the Euclidean pair space

The explicit two-by-two unitary matrix gives transitivity on each nonzero
Euclidean sphere. The ambient norm instance remains the product maximum norm;
all Euclidean preservation claims are explicit equalities.
-/

noncomputable section

namespace AutomaticContinuity.EuclideanPairRotations

open ComplexConjugate

def pairMatrix (u : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun v := (u.1 * v.1 - conj u.2 * v.2, u.2 * v.1 + conj u.1 * v.2)
  map_add' v w := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring
  map_smul' c v := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply] <;> ring

theorem norm_pairMatrix (u v : ℂ × ℂ) :
    euclideanPairNorm (pairMatrix u v) = euclideanPairNorm u * euclideanPairNorm v := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _)
    (mul_nonneg (euclideanPairNorm_nonneg u) (euclideanPairNorm_nonneg v))).mp
  rw [mul_pow, euclideanPairNorm_sq, euclideanPairNorm_sq, euclideanPairNorm_sq]
  simp only [pairMatrix, LinearMap.coe_mk, AddHom.coe_mk, Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

def unitaryEquiv (u : ℂ × ℂ) (hu : euclideanPairNorm u = 1) :
    (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) where
  toLinearMap := pairMatrix u
  invFun v := (conj u.1 * v.1 + conj u.2 * v.2, -u.2 * v.1 + u.1 * v.2)
  left_inv v := by
    have hone : conj u.1 * u.1 + conj u.2 * u.2 = 1 := by
      rw [Complex.conj_mul', Complex.conj_mul']
      have h := euclideanPairNorm_sq u
      rw [hu] at h
      norm_cast
      nlinarith
    change (conj u.1 * (u.1 * v.1 - conj u.2 * v.2) +
      conj u.2 * (u.2 * v.1 + conj u.1 * v.2),
      -u.2 * (u.1 * v.1 - conj u.2 * v.2) + u.1 * (u.2 * v.1 + conj u.1 * v.2)) = v
    apply Prod.ext
    · linear_combination v.1 * hone
    · linear_combination v.2 * hone
  right_inv v := by
    have hone : conj u.1 * u.1 + conj u.2 * u.2 = 1 := by
      rw [Complex.conj_mul', Complex.conj_mul']
      have h := euclideanPairNorm_sq u
      rw [hu] at h
      norm_cast
      nlinarith
    change (u.1 * (conj u.1 * v.1 + conj u.2 * v.2) -
      conj u.2 * (-u.2 * v.1 + u.1 * v.2),
      u.2 * (conj u.1 * v.1 + conj u.2 * v.2) + conj u.1 * (-u.2 * v.1 + u.1 * v.2)) = v
    apply Prod.ext
    · linear_combination v.1 * hone
    · linear_combination v.2 * hone

def unitaryContinuousEquiv (u : ℂ × ℂ) (hu : euclideanPairNorm u = 1) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := (unitaryEquiv u hu).toContinuousLinearEquiv

theorem norm_unitaryContinuousEquiv (u : ℂ × ℂ) (hu : euclideanPairNorm u = 1)
    (v : ℂ × ℂ) : euclideanPairNorm (unitaryContinuousEquiv u hu v) = euclideanPairNorm v := by
  change euclideanPairNorm (pairMatrix u v) = _
  rw [norm_pairMatrix, hu, one_mul]

theorem euclideanPairNorm_complex_smul (c : ℂ) (v : ℂ × ℂ) :
    euclideanPairNorm (c • v) = ‖c‖ * euclideanPairNorm v := by
  apply (sq_eq_sq₀ (euclideanPairNorm_nonneg _)
    (mul_nonneg (norm_nonneg c) (euclideanPairNorm_nonneg v))).mp
  rw [mul_pow, euclideanPairNorm_sq, euclideanPairNorm_sq]
  simp only [Prod.smul_fst, Prod.smul_snd, norm_smul]
  ring

def normalizedUnitary (p : ℂ × ℂ) (hp : 0 < euclideanPairNorm p) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  unitaryContinuousEquiv ((euclideanPairNorm p : ℂ)⁻¹ • p) (by
    rw [euclideanPairNorm_complex_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp, inv_mul_cancel₀ hp.ne'])

theorem norm_normalizedUnitary (p : ℂ × ℂ) (hp : 0 < euclideanPairNorm p)
    (v : ℂ × ℂ) : euclideanPairNorm (normalizedUnitary p hp v) = euclideanPairNorm v :=
  norm_unitaryContinuousEquiv _ _ v

theorem normalizedUnitary_axis (p : ℂ × ℂ) (hp : 0 < euclideanPairNorm p) :
    normalizedUnitary p hp ((euclideanPairNorm p : ℂ), 0) = p := by
  have hne : (euclideanPairNorm p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change pairMatrix ((euclideanPairNorm p : ℂ)⁻¹ • p) ((euclideanPairNorm p : ℂ), 0) = p
  calc
    _ = (euclideanPairNorm p : ℂ) •
        pairMatrix ((euclideanPairNorm p : ℂ)⁻¹ • p) (1, 0) := by
      rw [← map_smul]
      congr 1
      ext <;> simp
    _ = (euclideanPairNorm p : ℂ) • ((euclideanPairNorm p : ℂ)⁻¹ • p) := by
      congr 1
      ext <;> simp [pairMatrix]
    _ = p := by rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- Every two nonzero points of the same Euclidean norm are related by an
actual complex continuous linear equivalence preserving that norm everywhere. -/
theorem exists_rotation (p q : ℂ × ℂ) (hp : 0 < euclideanPairNorm p)
    (hpq : euclideanPairNorm p = euclideanPairNorm q) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
      e p = q ∧ ∀ v, euclideanPairNorm (e v) = euclideanPairNorm v := by
  have hq : 0 < euclideanPairNorm q := hpq ▸ hp
  let ep := normalizedUnitary p hp
  let eq := normalizedUnitary q hq
  refine ⟨ep.symm.trans eq, ?_, ?_⟩
  · change eq (ep.symm p) = q
    rw [← normalizedUnitary_axis p hp, ContinuousLinearEquiv.symm_apply_apply]
    rw [hpq]
    exact normalizedUnitary_axis q hq
  · intro v
    change euclideanPairNorm (eq (ep.symm v)) = _
    rw [norm_normalizedUnitary]
    have h := norm_normalizedUnitary p hp (ep.symm v)
    rw [show normalizedUnitary p hp (ep.symm v) = v from ep.apply_symm_apply v] at h
    exact h.symm

end AutomaticContinuity.EuclideanPairRotations
