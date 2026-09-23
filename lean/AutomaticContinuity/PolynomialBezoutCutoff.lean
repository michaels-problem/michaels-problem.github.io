import AutomaticContinuity.ArensBanach
import AutomaticContinuity.PolynomialConvexity
import AutomaticContinuity.PolynomialFunctionAlgebra

set_option autoImplicit false

/-!
# Approximate finite Bézout identities and polynomial cutoffs

The Banach-algebra dichotomy supplies an exact identity in a completed algebra.
Density then gives arbitrarily small residuals using its original generators.
The polynomial specialization is a separation statement, not an Oka–Weil
approximation theorem for arbitrary holomorphic functions.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialBezoutCutoff

open Set
open scoped BigOperators

universe u v w

variable {ι : Type u} [Fintype ι]
variable {A : Type v} [NormedCommRing A]
variable {R : Type w}

/-- Approximating the finitely many coefficients of an actual Bézout solution
gives arbitrarily small residuals. No bound on a chosen solution is needed. -/
theorem exists_small_residual_of_solution (a : ι → A) (b : Bezout.Solution a)
    (φ : R → A) (hφ : DenseRange φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ι → R, ‖1 - ∑ i, a i * φ (p i)‖ < ε := by
  have hd : DenseRange (fun p : ι → R => fun i => φ (p i)) :=
    DenseRange.piMap (fun _ : ι => hφ)
  have ho : IsOpen {v : ι → A | ‖1 - Bezout.pairing a v‖ < ε} :=
    isOpen_lt ((continuous_const.sub (Bezout.continuous_pairing a)).norm) continuous_const
  have hn : ({v : ι → A | ‖1 - Bezout.pairing a v‖ < ε} : Set (ι → A)).Nonempty := by
    refine ⟨b.val, ?_⟩
    simpa only [mem_ofPred_eq, b.property, sub_self, norm_zero] using hε
  obtain ⟨v, hv, p, rfl⟩ := hd.inter_open_nonempty _ ho hn
  exact ⟨p, hv⟩

/-- A complex Banach algebra with no common character zero admits approximate
Bézout solutions in any dense family. -/
theorem exists_small_residual [NormedAlgebra ℂ A] [CompleteSpace A]
    (a : ι → A) (φ : R → A) (hφ : DenseRange φ)
    (hzero : ∀ η : A →ₐ[ℂ] ℂ, ∃ i : ι, η (a i) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ι → R, ‖1 - ∑ i, a i * φ (p i)‖ < ε := by
  rcases Arens.solution_or_character a with hb | ⟨η, _hη, hηzero⟩
  · obtain ⟨b⟩ := hb
    exact exists_small_residual_of_solution a b φ hφ hε
  · obtain ⟨i, hi⟩ := hzero η
    exact (hi (hηzero i)).elim

/-- The residual of a finite polynomial Bézout expression. -/
def residual {σ : Type*} (q p : ι → MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := 1 - ∑ i, q i * p i

@[simp] theorem eval_residual {σ : Type*} (q p : ι → MvPolynomial σ ℂ)
    (z : σ → ℂ) :
    MvPolynomial.eval z (residual q p) =
      1 - ∑ i, MvPolynomial.eval z (q i) * MvPolynomial.eval z (p i) := by
  simp [residual]

/-- The residual equals one on the entire common zero set, including points
outside the compact on which the residual will be made small. -/
theorem eval_residual_eq_one {σ : Type*} (q p : ι → MvPolynomial σ ℂ)
    {z : σ → ℂ} (hz : ∀ i, MvPolynomial.eval z (q i) = 0) :
    MvPolynomial.eval z (residual q p) = 1 := by
  simp [hz]

open PolynomialFunctionAlgebra

/-- If a finite polynomial family has no common zero on the polynomial hull,
its ideal contains polynomials arbitrarily uniformly close to one on `K`. -/
theorem exists_polynomial_residual_small_on_hull {σ : Type*}
    (K : Set (σ → ℂ)) [CompactSpace K]
    (q : ι → MvPolynomial σ ℂ)
    (hq : ∀ z ∈ polynomialHullOf (fun x : σ → ℂ => x) K,
      ∃ i, MvPolynomial.eval z (q i) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ι → MvPolynomial σ ℂ,
      ∀ z ∈ K, ‖MvPolynomial.eval z (residual q p)‖ < ε := by
  have hzero : ∀ η : P K →ₐ[ℂ] ℂ, ∃ i, η (polynomial K (q i)) ≠ 0 := by
    intro η
    obtain ⟨i, hi⟩ := hq (characterPoint K η) (character_point_mem_hull K η)
    exact ⟨i, by simpa only [character_polynomial] using hi⟩
  obtain ⟨p, hp⟩ := exists_small_residual (fun i => polynomial K (q i))
    (polynomial K) (denseRange_polynomial K) hzero hε
  have hnorm : ‖polynomial K (residual q p)‖ < ε := by
    simpa only [residual, map_sub, map_one, map_sum, map_mul] using hp
  refine ⟨p, ?_⟩
  intro z hz
  have hle := ContinuousMap.norm_coe_le_norm
    (polynomial K (residual q p)).val (⟨z, hz⟩ : K)
  have hle' : ‖MvPolynomial.eval z (residual q p)‖ ≤
      ‖polynomial K (residual q p)‖ := by
    change ‖MvPolynomial.eval z (residual q p)‖ ≤
      ‖(polynomial K (residual q p)).val‖
    simpa only [polynomial_apply] using! hle
  exact hle'.trans_lt hnorm

/-- On a polynomially convex compact, absence of common zeros suffices. -/
theorem exists_polynomial_residual_small {σ : Type*}
    (K : Set (σ → ℂ)) [CompactSpace K]
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (q : ι → MvPolynomial σ ℂ)
    (hq : ∀ z ∈ K, ∃ i, MvPolynomial.eval z (q i) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ι → MvPolynomial σ ℂ,
      ∀ z ∈ K, ‖MvPolynomial.eval z (residual q p)‖ < ε := by
  apply exists_polynomial_residual_small_on_hull K q _ hε
  change polynomialHullOf (fun x : σ → ℂ => x) K = K at hK
  simpa only [hK] using hq

/-- A genuine polynomial is arbitrarily small on the compact and exactly one
on the complete common zero set of the specified finite family. -/
theorem exists_polynomial_cutoff {σ : Type*}
    (K : Set (σ → ℂ)) [CompactSpace K]
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (q : ι → MvPolynomial σ ℂ)
    (hq : ∀ z ∈ K, ∃ i, MvPolynomial.eval z (q i) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : MvPolynomial σ ℂ,
      (∀ z ∈ K, ‖MvPolynomial.eval z r‖ < ε) ∧
      ∀ z : σ → ℂ, (∀ i, MvPolynomial.eval z (q i) = 0) →
        MvPolynomial.eval z r = 1 := by
  obtain ⟨p, hp⟩ := exists_polynomial_residual_small K hK q hq hε
  exact ⟨residual q p, hp, fun _ hz => eval_residual_eq_one q p hz⟩

end AutomaticContinuity.PolynomialBezoutCutoff
