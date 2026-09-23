import AutomaticContinuity.Statement
import AutomaticContinuity.Coefficients
import AutomaticContinuity.CoefficientTopology
import AutomaticContinuity.LocallyMultiplicativelyConvex
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Tactic.Positivity

/-!
# Polynomial substitution estimates

The target algebra is not assumed normable. Every estimate is made with one
of its submultiplicative seminorms. The factor `max 1 (p 1)` explicitly accounts
for a defining seminorm that is not normalised on the identity.
-/

noncomputable section

namespace AutomaticContinuity

universe u

section PolynomialBounds

variable {A : Type u} [CommRing A] [Algebra ℂ A]

theorem seminorm_sum_le (p : Seminorm ℂ A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

theorem seminorm_pow_mul_le (p : Seminorm ℂ A) (hp : IsSubmultiplicative A p)
    (a b : A) (n : ℕ) : p (a ^ n * b) ≤ p a ^ n * p b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact (hp _ _).trans ((mul_le_mul_of_nonneg_left ih (apply_nonneg p a)).trans_eq
        (by rw [← mul_assoc, ← pow_succ']))

theorem seminorm_prod_pow_mul_le (p : Seminorm ℂ A) (hp : IsSubmultiplicative A p)
    {x : ℕ → A} {R : ℝ} (hR : 0 ≤ R) (hx : ∀ j, p (x j) ≤ R)
    (s : Finset ℕ) (α : ℕ → ℕ) (b : A) :
    p ((∏ j ∈ s, x j ^ α j) * b) ≤ R ^ (∑ j ∈ s, α j) * p b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_assoc]
      calc
        p (x i ^ α i * ((∏ j ∈ s, x j ^ α j) * b))
          ≤ p (x i) ^ α i * p ((∏ j ∈ s, x j ^ α j) * b) :=
            seminorm_pow_mul_le p hp _ _ _
        _ ≤ R ^ α i * (R ^ (∑ j ∈ s, α j) * p b) :=
          mul_le_mul (pow_le_pow_left₀ (apply_nonneg p _) (hx i) _) ih
            (apply_nonneg p _) (pow_nonneg hR _)
        _ = R ^ (α i + ∑ j ∈ s, α j) * p b := by rw [pow_add, mul_assoc]

/-- Monomial substitution incurs at most one factor `p 1`, independent of degree. -/
theorem seminorm_monomialValue_le (p : Seminorm ℂ A) (hp : IsSubmultiplicative A p)
    {x : ℕ → A} {R : ℝ} (hR : 0 ≤ R) (hx : ∀ j, p (x j) ≤ R)
    (α : MultiIndex) :
    p (α.prod (fun j n => x j ^ n)) ≤ max 1 (p 1) * R ^ totalDegree α := by
  have h := seminorm_prod_pow_mul_le p hp hR hx α.support α (1 : A)
  simp only [mul_one] at h
  change p (α.prod (fun j n => x j ^ n)) ≤ R ^ totalDegree α * p 1 at h
  exact h.trans ((mul_le_mul_of_nonneg_left (le_max_right 1 (p 1))
    (pow_nonneg hR _)).trans_eq (mul_comm _ _))

namespace CoefficientSeries

/-- For a finite polynomial the coefficient norm is the expected finite sum. -/
theorem q_ofPolynomial (R : ℕ) (f : MvPolynomial ℕ ℂ) :
    q R (ofPolynomial f) =
      ∑ α ∈ f.support, ‖f.coeff α‖ * (R : ℝ) ^ totalDegree α := by
  classical
  unfold q
  apply tsum_eq_sum
  intro α hα
  have hc : f.coeff α = 0 := by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hα
  simp [weightedTerm, ofPolynomial, hc]

/-- The finite-polynomial estimate needed before completing substitution. -/
theorem seminorm_aeval_le_q (p : Seminorm ℂ A) (hp : IsSubmultiplicative A p)
    {x : ℕ → A} {R : ℕ} (hx : ∀ j, p (x j) ≤ (R : ℝ))
    (f : MvPolynomial ℕ ℂ) :
    p (MvPolynomial.aeval x f) ≤ max 1 (p 1) * q R (ofPolynomial f) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, q_ofPolynomial]
  calc
    p (∑ α ∈ f.support,
        algebraMap ℂ A (f.coeff α) * ∏ j ∈ α.support, x j ^ α j)
      ≤ ∑ α ∈ f.support,
        p (algebraMap ℂ A (f.coeff α) * ∏ j ∈ α.support, x j ^ α j) :=
          seminorm_sum_le p _ _
    _ ≤ ∑ α ∈ f.support, max 1 (p 1) * (‖f.coeff α‖ * (R : ℝ) ^ totalDegree α) := by
      apply Finset.sum_le_sum
      intro α hα
      rw [← Algebra.smul_def, map_smul_eq_mul]
      exact (mul_le_mul_of_nonneg_left
        (seminorm_monomialValue_le p hp (Nat.cast_nonneg R) hx α)
        (norm_nonneg _)).trans_eq (by ring)
    _ = max 1 (p 1) * ∑ α ∈ f.support, ‖f.coeff α‖ * (R : ℝ) ^ totalDegree α :=
      (Finset.mul_sum _ _ _).symm

end CoefficientSeries

end PolynomialBounds

namespace PolynomialSubstitution

open CoefficientSeries

/-- Polynomials carry the uniformity inherited from the coefficient algebra. -/
@[instance_reducible] def polynomialUniformSpace : UniformSpace (MvPolynomial ℕ ℂ) :=
  UniformSpace.comap polynomialHom inferInstance

attribute [local instance] polynomialUniformSpace

local instance polynomialIsUniformAddGroup : IsUniformAddGroup (MvPolynomial ℕ ℂ) :=
  IsUniformInducing.isUniformAddGroup polynomialHom.toLinearMap ⟨rfl⟩

theorem polynomialHom_isUniformInducing : IsUniformInducing polynomialHom := ⟨rfl⟩

def polynomialSeminorm (n : ℕ) : Seminorm ℂ (MvPolynomial ℕ ℂ) :=
  (definingSeminorm n).comp polynomialHom.toLinearMap

theorem polynomial_withSeminorms : WithSeminorms polynomialSeminorm :=
  polynomialHom.toLinearMap.withSeminorms_induced withSeminorms

/-- Substitution of a bounded sequence is continuous on finite polynomials,
with their topology inherited from the coefficient algebra. -/
theorem continuous_aeval {A : Type u} [CommRing A] [Algebra ℂ A]
    [TopologicalSpace A] (hA : IsLocallyMultiplicativelyConvex A)
    {x : ℕ → A} (hx : Bornology.IsVonNBounded ℂ (Set.range x)) :
    Continuous (MvPolynomial.aeval x : MvPolynomial ℕ ℂ →ₐ[ℂ] A) := by
  classical
  obtain ⟨P, hP, hp⟩ := hA
  apply polynomial_withSeminorms.continuous_of_isBounded hp (MvPolynomial.aeval x).toLinearMap
  intro p
  obtain ⟨C, hC, hbound⟩ := hp.isVonNBounded_iff_seminorm_bounded.mp hx p
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let M : NNReal := ⟨max 1 (p.val 1), le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨{N}, M, ?_⟩
  simp only [Finset.sup_singleton]
  intro f
  change p.val (MvPolynomial.aeval x f) ≤ max 1 (p.val 1) * q (N + 1) (ofPolynomial f)
  apply seminorm_aeval_le_q p.val (hP p.val p.property)
  intro j
  exact (hbound (x j) ⟨j, rfl⟩).le.trans
    (hN.le.trans (by exact_mod_cast Nat.le_succ N))

/-- Universal substitution along a bounded sequence in a complete Hausdorff
locally multiplicatively convex algebra. The codomain may be nonmetrizable. -/
theorem exists_substitution {A : Type u} [CommRing A] [Algebra ℂ A]
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (hA : IsLocallyMultiplicativelyConvex A) (x : ℕ → A)
    (hx : Bornology.IsVonNBounded ℂ (Set.range x)) :
    ∃ T : CoefficientSeries →ₐ[ℂ] A,
      Continuous T ∧ ∀ j : ℕ, T (coordinate j) = x j := by
  classical
  let : ContinuousMul A := hA.continuousMul
  let : IsTopologicalRing A := { toIsTopologicalSemiring := ⟨⟩ }
  let : ContinuousMul CoefficientSeries :=
    CoefficientSeries.isLocallyMultiplicativelyConvex.continuousMul
  let : IsTopologicalRing CoefficientSeries := { toIsTopologicalSemiring := ⟨⟩ }
  let evalCLM : MvPolynomial ℕ ℂ →L[ℂ] A :=
    ⟨(MvPolynomial.aeval x).toLinearMap, continuous_aeval hA hx⟩
  let T₀ : CoefficientSeries →+* A := IsDenseInducing.extendRingHom
    (i := polynomialHom.toRingHom)
    (f := (MvPolynomial.aeval x : MvPolynomial ℕ ℂ →ₐ[ℂ] A).toRingHom)
    polynomialHom_isUniformInducing polynomialHom_denseRange evalCLM.uniformContinuous
  have heq (f : MvPolynomial ℕ ℂ) : T₀ (polynomialHom f) = MvPolynomial.aeval x f :=
    uniformly_extend_of_ind polynomialHom_isUniformInducing polynomialHom_denseRange
      evalCLM.uniformContinuous f
  let T : CoefficientSeries →ₐ[ℂ] A :=
    { T₀ with
      commutes' := fun c => by
        rw [← polynomialHom.commutes c]
        exact (heq (algebraMap ℂ (MvPolynomial ℕ ℂ) c)).trans
          ((MvPolynomial.aeval x).commutes c) }
  refine ⟨T, ?_, ?_⟩
  · exact (uniformContinuous_uniformly_extend polynomialHom_isUniformInducing
      polynomialHom_denseRange evalCLM.uniformContinuous).continuous
  · intro j
    change T₀ (coordinate j) = x j
    rw [← polynomialHom_X j, heq]
    simp

end PolynomialSubstitution

end AutomaticContinuity
