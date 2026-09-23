import AutomaticContinuity.FlagCoordinateEquivalence
import AutomaticContinuity.PolynomialCutoff

set_option autoImplicit false

/-!
# Polynomial cutoffs near an exterior point

An actual polynomial separator can be normalized and raised to a power so
that it equals one at the exterior point and is arbitrarily small on the
original set. Continuity gives a fixed neighbourhood of the exterior point;
the cubic cutoff then approximates zero on the set and one on that same
neighbourhood to every tolerance. The compact forbidden flag graph is a
concrete instance. No union-convexity or Runge theorem is assumed or claimed.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialExteriorCutoff

open Set MvPolynomial

universe u v
variable {X : Type u} {σ : Type v}

/-- Powering a normalized separator gives an arbitrarily small polynomial
on the set and the exact value one at the separated point. -/
theorem exists_normalized_polynomial (e : X → σ → ℂ) (K : Set X) (x : X)
    (hx : x ∉ polynomialHullOf e K) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      eval (e x) q = 1 ∧ ∀ y ∈ K, ‖eval (e y) q‖ < ε := by
  classical
  by_cases hK : K.Nonempty
  · obtain ⟨p, C, hC, hsep⟩ := (not_mem_polynomialHullOf_iff e K x).mp hx
    obtain ⟨y₀, hy₀⟩ := hK
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y₀ hy₀)
    have hp0 : 0 < ‖eval (e x) p‖ := hC0.trans_lt hsep
    have hpne : eval (e x) p ≠ 0 := norm_pos_iff.mp hp0
    have hratio : C / ‖eval (e x) p‖ < 1 := (div_lt_one hp0).mpr hsep
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hratio
    refine ⟨(MvPolynomial.C ((eval (e x) p)⁻¹) * p) ^ m, ?_, ?_⟩
    · simp only [map_pow, map_mul, eval_C, inv_mul_cancel₀ hpne, one_pow]
    · intro y hy
      simp only [map_pow, map_mul, eval_C, norm_pow, norm_mul, norm_inv]
      apply lt_of_le_of_lt _ hm
      apply pow_le_pow_left₀ (by positivity)
      calc
        ‖eval (e x) p‖⁻¹ * ‖eval (e y) p‖ ≤ ‖eval (e x) p‖⁻¹ * C := by
          gcongr
          exact hC y hy
        _ = C / ‖eval (e x) p‖ := by rw [div_eq_mul_inv]; ring
  · refine ⟨1, by simp, ?_⟩
    intro y hy
    exact False.elim (hK ⟨y, hy⟩)

/-- A polynomially convex set has normalized polynomial separators at every
exterior point, with arbitrary positive uniform tolerance. -/
theorem exists_normalized_polynomial_of_convex (e : X → σ → ℂ) (K : Set X)
    (hK : IsPolynomiallyConvexOf e K) (x : X) (hx : x ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : MvPolynomial σ ℂ,
      eval (e x) q = 1 ∧ ∀ y ∈ K, ‖eval (e y) q‖ < ε :=
  exists_normalized_polynomial e K x (by rwa [hK]) hε

/-- The neighbourhood is chosen once, independently of the final cutoff
tolerance. Each resulting polynomial retains its exact value one at `x`. -/
theorem exists_neighbourhood_cutoffs [TopologicalSpace X]
    (e : X → σ → ℂ) (he : Continuous e) (K : Set X) (x : X)
    (hx : x ∉ polynomialHullOf e K) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ Disjoint K V ∧
      ∀ ε > 0, ∃ p : MvPolynomial σ ℂ,
        eval (e x) p = 1 ∧
        (∀ y ∈ K, ‖eval (e y) p‖ < ε) ∧
        (∀ y ∈ V, ‖eval (e y) p - 1‖ < ε) := by
  obtain ⟨q, hqx, hqK⟩ := exists_normalized_polynomial e K x hx (by norm_num : (0 : ℝ) < 1 / 8)
  let V : Set X := {y | ‖eval (e y) q - 1‖ < 1 / 8}
  have hV : IsOpen V := isOpen_lt (((MvPolynomial.continuous_eval q).comp he).sub
    continuous_const).norm continuous_const
  have hxV : x ∈ V := by simp [V, hqx]
  have hdisjoint : Disjoint K V := by
    apply Set.disjoint_left.mpr
    intro y hyK hyV
    have h1 := norm_add_le (eval (e y) q) (1 - eval (e y) q)
    have hq := hqK y hyK
    have hnear : ‖eval (e y) q - 1‖ < 1 / 8 := hyV
    have hnear' : ‖1 - eval (e y) q‖ < 1 / 8 := by rwa [norm_sub_rev]
    simp only [add_sub_cancel, norm_one] at h1
    linarith
  refine ⟨V, hV, hxV, hdisjoint, ?_⟩
  intro ε hε
  obtain ⟨p, hpK, hpV, _, hpone⟩ := PolynomialCutoff.exists_polynomial_cutoff
    (e '' K) (e '' V) q
    (by rintro _ ⟨y, hy, rfl⟩; exact (hqK y hy).le)
    (by rintro _ ⟨y, hy, rfl⟩; exact le_of_lt hy) hε
  exact ⟨p, hpone (e x) hqx,
    fun y hy => hpK (e y) ⟨y, hy, rfl⟩,
    fun y hy => hpV (e y) ⟨y, hy, rfl⟩⟩

/-- Application to the actual compact forbidden flag graph in its complete
complex coordinates. -/
theorem exists_neighbourhood_cutoffs_compactForbiddenGraph (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) (x : FlagPolynomialSeparation.Point n)
    (hx : x ∉ FlagTotalSpace.compactForbiddenGraph n R) :
    ∃ V : Set (FlagPolynomialSeparation.Point n), IsOpen V ∧ x ∈ V ∧
      Disjoint (FlagTotalSpace.compactForbiddenGraph n R) V ∧
      ∀ ε > 0, ∃ p : MvPolynomial (FlagPolynomialSeparation.Variables n) ℂ,
        eval (FlagPolynomialSeparation.coordinates x) p = 1 ∧
        (∀ y ∈ FlagTotalSpace.compactForbiddenGraph n R,
          ‖eval (FlagPolynomialSeparation.coordinates y) p‖ < ε) ∧
        (∀ y ∈ V, ‖eval (FlagPolynomialSeparation.coordinates y) p - 1‖ < ε) := by
  apply exists_neighbourhood_cutoffs FlagPolynomialSeparation.coordinates
    (FlagPolynomialSeparation.continuous_coordinates n)
  rwa [FlagPolynomialSeparation.isPolynomiallyConvex_compactForbiddenGraph n hR]

end AutomaticContinuity.PolynomialExteriorCutoff
