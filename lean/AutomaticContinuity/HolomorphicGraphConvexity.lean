import AutomaticContinuity.FlagPolynomialSeparation
import AutomaticContinuity.LocalPolydiscApproximation
import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-!
# Polynomial convexity of holomorphic section graphs over polydiscs

The graph is the actual compact image in all source and target coordinates.
Source polynomials separate points outside the base. Above the base, a target
linear functional and a polynomial approximation of its composition with the
section separate a point from the graph. No graph convexity is assumed.
-/

noncomputable section

namespace AutomaticContinuity.HolomorphicGraphConvexity

open Set MvPolynomial FlagPolynomialSeparation

def sectionGraph (n : ℕ) (R : ℝ) (h : FinitePoint n → ℂ × ℂ) : Set (Point n) :=
  (fun z => (z, h z)) '' polydisc n R

theorem isCompact_sectionGraph {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {h : FinitePoint n → ℂ × ℂ} (hh : ContinuousOn h (polydisc n R)) :
    IsCompact (sectionGraph n R h) :=
  (isCompact_polydisc n hR).image_of_continuousOn (continuousOn_id.prodMk hh)

@[simp] theorem eval_rename_source {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (y : Point n) : eval (coordinates y) (rename Sum.inl p) = eval y.1 p := by
  rw [eval_rename]
  rfl

theorem isPolynomiallyConvex_sectionGraph {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)} (hU : IsOpen U)
    (hKU : polydisc n R ⊆ U) (hhd : DifferentiableOn ℂ h U) :
    IsPolynomiallyConvexOf coordinates (sectionGraph n R h) := by
  apply (isPolynomiallyConvexOf_iff_separation coordinates _).mpr
  intro x hx
  by_cases hbase : x.1 ∈ polydisc n R
  · have hneq : x.2 ≠ h x.1 := by
      intro heq
      exact hx ⟨x.1, hbase, by cases x; simp_all⟩
    have hdpos : 0 < euclideanPairNorm (x.2 - h x.1) := by
      exact lt_of_le_of_ne (euclideanPairNorm_nonneg _) (fun heq =>
        hneq (sub_eq_zero.mp ((euclideanPairNorm_eq_zero_iff _).mp heq.symm)))
    obtain ⟨ℓ, _hℓbound, hℓeq⟩ := exists_pair_norming_functional (x.2 - h x.1) hdpos
    have hℓd : Differentiable ℂ ℓ := ℓ.toContinuousLinearMap.differentiable
    have hcomp : DifferentiableOn ℂ (fun z => ℓ (h z)) U := by
      intro z hz
      exact hℓd.differentiableAt.comp_differentiableWithinAt z (hhd z hz)
    obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc hR
      (fun z => ℓ (h z)) hU hKU hcomp (div_pos hdpos (by norm_num : (0 : ℝ) < 4))
    let q : Polynomial n := targetLinearPolynomial n ℓ - rename Sum.inl p
    have hq : ∀ y : Point n, eval (coordinates y) q = ℓ y.2 - eval y.1 p := by
      intro y
      simp only [q, map_sub, eval_rename_source]
      change evaluate y (targetLinearPolynomial n ℓ) - _ = _
      rw [evaluate_targetLinearPolynomial]
    refine ⟨q, euclideanPairNorm (x.2 - h x.1) / 4, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      rw [hq, norm_sub_rev]
      exact (hp z hz).le
    · rw [hq]
      have ht := norm_sub_le (ℓ x.2 - eval x.1 p) (ℓ (h x.1) - eval x.1 p)
      have heq : (ℓ x.2 - eval x.1 p) - (ℓ (h x.1) - eval x.1 p) =
          ℓ (x.2 - h x.1) := by rw [map_sub]; ring
      rw [heq, hℓeq, norm_sub_rev (ℓ (h x.1))] at ht
      linarith [hp x.1 hbase]
  · obtain ⟨p, C, hp, hxsep⟩ :=
      (isPolynomiallyConvexOf_iff_separation (fun z : FinitePoint n => z)
        (polydisc n R)).mp (isPolynomiallyConvex_polydisc n R) x.1 hbase
    refine ⟨rename Sum.inl p, C, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      simpa only [eval_rename_source] using hp z hz
    · simpa only [eval_rename_source] using hxsep

end AutomaticContinuity.HolomorphicGraphConvexity
