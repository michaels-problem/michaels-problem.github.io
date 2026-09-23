import AutomaticContinuity.HomogeneousPowerBasis
import AutomaticContinuity.RadialCutoffField
import Mathlib.Algebra.MvPolynomial.Monad

set_option autoImplicit false

/-!
# The localized radial field is an actual bounded-degree polynomial field

Scaling the two variables, iterating the cubic cutoff, and multiplying by the
radial coordinates give concrete multivariate polynomials. Evaluation agrees
with the analytic field formula, the field vanishes at the origin, and the
degree bound is uniform over every scalar scaling and rate parameter.
-/

noncomputable section

namespace AutomaticContinuity.RadialPolynomialField

open MvPolynomial
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 2) ℂ

def rescale (s : ℂ) : Poly →ₐ[ℂ] Poly := bind₁ (fun i => C s * X i)

theorem eval_rescale (q : Poly) (s : ℂ) (w : Fin 2 → ℂ) :
    eval w (rescale s q) = eval (fun i => s * w i) q := by
  change eval₂Hom (RingHom.id ℂ) w (bind₁ (fun i => C s * X i) q) = _
  rw [eval₂Hom_bind₁]
  simp only [map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply]
  rfl

theorem totalDegree_rescale_le (q : Poly) (s : ℂ) : (rescale s q).totalDegree ≤ q.totalDegree := by
  conv_lhs => rw [← sum_homogeneousComponent q, map_sum]
  apply totalDegree_finsetSum_le
  intro i hi
  have hh := (homogeneousComponent_isHomogeneous i q).aeval
    (fun j : Fin 2 => C s * X j) (fun j => (isHomogeneous_X ℂ j).C_mul s)
  have hhi : (rescale s (homogeneousComponent i q)).IsHomogeneous i := by
    simpa only [one_mul] using! hh
  exact hhi.totalDegree_le.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem totalDegree_iterate_le (q : Poly) (m : ℕ) :
    (PolynomialCutoff.iterate q m).totalDegree ≤ 3 ^ m * q.totalDegree := by
  induction m with
  | zero => simp [PolynomialCutoff.iterate]
  | succ m ih =>
      let p := PolynomialCutoff.iterate q m
      have h3 : ((3 : Poly) * p ^ 2).totalDegree ≤ 2 * p.totalDegree := by
        have hh := totalDegree_mul (C (3 : ℂ)) (p ^ 2)
        simpa only [map_ofNat, totalDegree_C, zero_add] using hh.trans
          (by simpa only [totalDegree_C, zero_add] using totalDegree_pow p 2)
      have h2 : ((2 : Poly) * p ^ 3).totalDegree ≤ 3 * p.totalDegree := by
        have hh := totalDegree_mul (C (2 : ℂ)) (p ^ 3)
        simpa only [map_ofNat, totalDegree_C, zero_add] using hh.trans
          (by simpa only [totalDegree_C, zero_add] using totalDegree_pow p 3)
      change (3 * p ^ 2 - 2 * p ^ 3).totalDegree ≤ _
      apply (totalDegree_sub _ _).trans
      apply max_le
      · apply h3.trans
        calc
          2 * p.totalDegree ≤ 3 * p.totalDegree := Nat.mul_le_mul_right _ (by omega)
          _ ≤ 3 * (3 ^ m * q.totalDegree) := Nat.mul_le_mul_left _ ih
          _ = 3 ^ (m + 1) * q.totalDegree := by rw [pow_succ]; ring
      · apply h2.trans
        calc
          3 * p.totalDegree ≤ 3 * (3 ^ m * q.totalDegree) := Nat.mul_le_mul_left _ ih
          _ = 3 ^ (m + 1) * q.totalDegree := by rw [pow_succ]; ring

def fieldPolynomial (q : Poly) (s rate : ℂ) (m : ℕ) : Poly × Poly :=
  (C rate * PolynomialCutoff.iterate (rescale s q) m * X 0,
   C rate * PolynomialCutoff.iterate (rescale s q) m * X 1)

theorem fieldPolynomial_degree (q : Poly) (s rate : ℂ) (m : ℕ) :
    (fieldPolynomial q s rate m).1.totalDegree ≤ 3 ^ m * q.totalDegree + 1 ∧
    (fieldPolynomial q s rate m).2.totalDegree ≤ 3 ^ m * q.totalDegree + 1 := by
  have hb : (C rate * PolynomialCutoff.iterate (rescale s q) m).totalDegree ≤
      3 ^ m * q.totalDegree := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact (totalDegree_iterate_le _ m).trans
      (Nat.mul_le_mul_left _ (totalDegree_rescale_le q s))
  constructor <;> apply (totalDegree_mul _ _).trans <;>
    simpa only [totalDegree_X] using Nat.add_le_add_right hb 1

theorem fieldPolynomial_zero (q : Poly) (s rate : ℂ) (m : ℕ) :
    eval (0 : Fin 2 → ℂ) (fieldPolynomial q s rate m).1 = 0 ∧
    eval (0 : Fin 2 → ℂ) (fieldPolynomial q s rate m).2 = 0 := by
  simp [fieldPolynomial]

/-- Evaluation agrees exactly with the cutoff field, with rescaling performed
on the input of the original polynomial. -/
theorem eval_fieldPolynomial (q : Poly) (s rate : ℂ) (m : ℕ) (w : ℂ × ℂ) :
    (eval ![w.1, w.2] (fieldPolynomial q s rate m).1,
      eval ![w.1, w.2] (fieldPolynomial q s rate m).2) =
      (rate * RadialCutoffField.amplified m (eval (fun i => s * ![w.1, w.2] i) q)) • w := by
  apply Prod.ext <;>
    simp [fieldPolynomial, PolynomialCutoff.eval_iterate, eval_rescale,
      RadialCutoffField.amplified, smul_eq_mul]

end AutomaticContinuity.RadialPolynomialField
