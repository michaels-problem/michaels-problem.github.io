import AutomaticContinuity.EuclideanBallGeometry
import AutomaticContinuity.FiniteHolomorphicRegularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Ring.Units

/-!
# An actual local spray with an entire parameter

An entire map `φ : ℂ² → ℂ²` through `p` whose range avoids a larger closed
Euclidean ball gives the explicit spray `S(y,t) = φ(t) + y - p`. It is jointly
entire and avoids the smaller ball for every parameter `t` whenever the base
point `y` lies in the stated neighborhood of `p`. An invertible derivative of
`φ` gives actual local biholomorphic charts for each parameter fiber.

This construction is local in the base point. It asserts neither a uniform
spray over an arbitrary compact section nor an approximation theorem.
-/

noncomputable section

namespace AutomaticContinuity.LocalEntireSpray

open Set Filter Metric
open scoped Topology

abbrev Pair := ℂ × ℂ

/-- The Euclidean ball complement spray with its entire parameter. -/
def spray (φ : Pair → Pair) (p : Pair) (yt : Pair × Pair) : Pair :=
  φ yt.2 + (yt.1 - p)

theorem differentiable_spray {φ : Pair → Pair} (hφ : Differentiable ℂ φ) (p : Pair) :
    Differentiable ℂ (spray φ p) :=
  (hφ.comp differentiable_snd).add (differentiable_fst.sub_const p)

@[simp] theorem spray_zero {φ : Pair → Pair} {p : Pair} (hφ0 : φ 0 = p) (y : Pair) :
    spray φ p (y, 0) = y := by
  simp only [spray, hφ0]
  abel

theorem euclideanPairNorm_neg (v : Pair) : euclideanPairNorm (-v) = euclideanPairNorm v := by
  simp [euclideanPairNorm]

/-- Avoidance holds for every parameter, with an explicit neighborhood in the
base variable determined by the difference between the two ball radii. -/
theorem spray_avoids {φ : Pair → Pair} {p : Pair} {R r : ℝ}
    (hφR : ∀ t, R < euclideanPairNorm (φ t))
    {y : Pair} (hy : euclideanPairNorm (y - p) < R - r) (t : Pair) :
    r < euclideanPairNorm (spray φ p (y, t)) := by
  have heq : φ t = spray φ p (y, t) + -(y - p) := by
    dsimp [spray]
    abel
  have htriangle := euclideanPairNorm_add_le (spray φ p (y, t)) (-(y - p))
  rw [← heq, euclideanPairNorm_neg] at htriangle
  linarith [hφR t]

theorem isOpen_baseNeighborhood (p : Pair) (R r : ℝ) :
    IsOpen {y : Pair | euclideanPairNorm (y - p) < R - r} :=
  isOpen_lt (continuous_euclideanPairNorm.comp (continuous_id.sub continuous_const)) continuous_const

theorem center_mem_baseNeighborhood (p : Pair) {R r : ℝ} (hrR : r < R) :
    p ∈ {y : Pair | euclideanPairNorm (y - p) < R - r} := by
  simpa only [mem_ofPred_eq, sub_self, euclideanPairNorm_zero] using sub_pos.mpr hrR

/-- The derivative in the entire parameter is unchanged by the base translation. -/
theorem hasFDerivAt_fiber {φ : Pair → Pair} {p : Pair}
    {A : Pair →L[ℂ] Pair} (hφ : HasFDerivAt φ A 0) (y : Pair) :
    HasFDerivAt (fun t => spray φ p (y, t)) A 0 := hφ.add_const (y - p)

/-- An injective entire map supplies an injective entire parameter fiber for
every base point, since changing the base adds a constant translation. -/
theorem injective_fiber {φ : Pair → Pair} {p : Pair}
    (hφ : Function.Injective φ) (y : Pair) :
    Function.Injective (fun t => spray φ p (y, t)) := by
  intro t u htu
  exact hφ (add_right_cancel htu)

/-- For an entire map with an invertible derivative at zero, the inverse
function chart may be restricted so its inverse is holomorphic on its whole
target. The forward function is unchanged globally. -/
theorem exists_biholomorphic_chart (f : Pair → Pair) (hf : Differentiable ℂ f)
    (A : Pair ≃L[ℂ] Pair) (hA : HasFDerivAt f (A : Pair →L[ℂ] Pair) 0) :
    ∃ e : OpenPartialHomeomorph Pair Pair,
      (e : Pair → Pair) = f ∧ (0 : Pair) ∈ e.source ∧ f 0 ∈ e.target ∧
      DifferentiableOn ℂ e.symm e.target := by
  have hs := FiniteHolomorphicRegularity.hasStrictFDerivAt isOpen_univ
    hf.differentiableOn (mem_univ (0 : Pair))
  rw [hA.fderiv] at hs
  let e := hs.toOpenPartialHomeomorph f
  have hunit0 : IsUnit (fderiv ℂ f 0) := by
    rw [hA.fderiv]
    exact A.toUnit.isUnit
  have hcont := FiniteHolomorphicRegularity.continuousAt_fderiv isOpen_univ
    hf.differentiableOn (mem_univ (0 : Pair))
  have hunit : {x : Pair | IsUnit (fderiv ℂ f x)} ∈ 𝓝 (0 : Pair) :=
    hcont (Units.isOpen.mem_nhds hunit0)
  obtain ⟨δ, hδ, hδunit⟩ := Metric.mem_nhds_iff.mp hunit
  let e' := e.restrOpen (ball 0 δ) isOpen_ball
  have hzero : (0 : Pair) ∈ e'.source :=
    ⟨hs.mem_toOpenPartialHomeomorph_source, mem_ball_self hδ⟩
  refine ⟨e', rfl, hzero, e'.map_source hzero, ?_⟩
  intro y hy
  have hx := e'.map_target hy
  obtain ⟨u, hu⟩ := hδunit hx.2
  have hueq : ((ContinuousLinearEquiv.ofUnit u) : Pair →L[ℂ] Pair) =
      fderiv ℂ f (e'.symm y) := by
    apply ContinuousLinearMap.ext
    intro v
    change (u : Pair →L[ℂ] Pair) v = (fderiv ℂ f (e'.symm y)) v
    rw [hu]
  have hdf := (hf (e'.symm y)).hasFDerivAt
  rw [← hueq] at hdf
  exact (e'.hasFDerivAt_symm hy hdf).differentiableAt.differentiableWithinAt

/-- Every fiber of the actual spray is locally biholomorphic at its zero
parameter whenever the supplied entire map has an invertible derivative there. -/
theorem exists_fiber_biholomorphic_chart {φ : Pair → Pair} {p : Pair}
    (hφ : Differentiable ℂ φ) (hφ0 : φ 0 = p)
    (A : Pair ≃L[ℂ] Pair) (hA : HasFDerivAt φ (A : Pair →L[ℂ] Pair) 0) (y : Pair) :
    ∃ e : OpenPartialHomeomorph Pair Pair,
      (e : Pair → Pair) = (fun t => spray φ p (y, t)) ∧
      (0 : Pair) ∈ e.source ∧ y ∈ e.target ∧ DifferentiableOn ℂ e.symm e.target := by
  obtain ⟨e, he, hs, ht, hInv⟩ := exists_biholomorphic_chart
    (fun t => spray φ p (y, t)) (hφ.add_const (y - p)) A (hasFDerivAt_fiber hA y)
  exact ⟨e, he, hs, by simpa only [spray_zero hφ0] using ht, hInv⟩

end AutomaticContinuity.LocalEntireSpray
