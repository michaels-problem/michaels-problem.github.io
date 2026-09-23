import AutomaticContinuity.LocalFlagInterpolation
import AutomaticContinuity.EuclideanBallGeometry

/-!
# Entire approximation through one global target chart

A map whose compact image lies in a single biholomorphic copy of `ℂ²` can be
approximated on a polydisc by entire maps into that same copy. This is a genuine
restricted approximation theorem; it does not glue different target charts.
-/

noncomputable section

namespace AutomaticContinuity.OneChartApproximation

open Set Metric

/-- Polynomial approximation of the lifted map followed by an entire map.
The displayed error is measured in the manuscript's Euclidean pair norm. -/
theorem exists_polynomial_composition_approx {n : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (φ : (ℂ × ℂ) → ℂ × ℂ) (hφ : Differentiable ℂ φ)
    (u : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hu : DifferentiableOn ℂ u U) :
    ∃ p q : MvPolynomial (Fin n) ℂ,
      ∀ z ∈ polydisc n R,
        euclideanPairNorm (φ (MvPolynomial.eval z p, MvPolynomial.eval z q) - φ (u z)) < ε := by
  have hcompact : IsCompact (u '' polydisc n R) :=
    (isCompact_polydisc n hR).image_of_continuousOn (hu.continuousOn.mono hKU)
  have hε2 : 0 < ε / 2 := by positivity
  have huc := hcompact.uniformContinuousAt_of_continuousAt φ
    (fun _ _ => hφ.continuous.continuousAt) (dist_mem_uniformity hε2)
  obtain ⟨δ, hδ, hδφ⟩ := mem_uniformity_dist.mp huc
  obtain ⟨p, hp⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc
    hR (fun z => (u z).1) hU hKU hu.fst hδ
  obtain ⟨q, hq⟩ := FiniteCauchy.exists_polynomial_approx_on_polydisc
    hR (fun z => (u z).2) hU hKU hu.snd hδ
  refine ⟨p, q, fun z hz => ?_⟩
  have hclose : dist (u z) (MvPolynomial.eval z p, MvPolynomial.eval z q) < δ := by
    rw [dist_comm, dist_eq_norm, Prod.norm_def]
    exact max_lt (hp z hz) (hq z hz)
  have hout : dist (φ (u z)) (φ (MvPolynomial.eval z p, MvPolynomial.eval z q)) < ε / 2 :=
    hδφ hclose ⟨z, hz, rfl⟩
  have hnorm : ‖φ (MvPolynomial.eval z p, MvPolynomial.eval z q) - φ (u z)‖ < ε / 2 := by
    rwa [dist_comm, dist_eq_norm] at hout
  exact (euclideanPairNorm_le_two_mul_norm _).trans_lt (by linarith)

/-- The entire approximant retains every global range restriction of `φ`. -/
theorem exists_entire_composition_approx {n : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (φ : (ℂ × ℂ) → ℂ × ℂ) (hφ : Differentiable ℂ φ)
    (u : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hu : DifferentiableOn ℂ u U) :
    ∃ f : FinitePoint n → ℂ × ℂ, Differentiable ℂ f ∧
      (∀ z, f z ∈ range φ) ∧
      ∀ z ∈ polydisc n R, euclideanPairNorm (f z - φ (u z)) < ε := by
  obtain ⟨p, q, hpq⟩ := exists_polynomial_composition_approx hR hε φ hφ u hU hKU hu
  refine ⟨fun z => φ (MvPolynomial.eval z p, MvPolynomial.eval z q), ?_, ?_, hpq⟩
  · exact hφ.comp ((differentiable_polynomial_eval p).prodMk (differentiable_polynomial_eval q))
  · intro z
    exact mem_range_self _

/-- A compact-image condition in one actual Fatou--Bieberbach chart suffices
for global entire approximation into that chart. The input map only needs to
be holomorphic near the polydisc; its image away from that compact is unrestricted. -/
theorem exists_entire_approx_in_one_chart {n : ℕ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (H : Ω ≃ₜ (ℂ × ℂ))
    (h : (ℂ × ℂ) → ℂ × ℂ) (hh : DifferentiableOn ℂ h Ω)
    (hH : ∀ x : Ω, H x = h x)
    (hInv : Differentiable ℂ (fun y : ℂ × ℂ => (H.symm y : ℂ × ℂ)))
    (f : FinitePoint n → ℂ × ℂ) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hfΩ : MapsTo f (polydisc n R) Ω) :
    ∃ g : FinitePoint n → ℂ × ℂ, Differentiable ℂ g ∧
      (∀ z, g z ∈ Ω) ∧
      ∀ z ∈ polydisc n R, euclideanPairNorm (g z - f z) < ε := by
  let V := U ∩ f ⁻¹' Ω
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU hΩ
  have hKV : polydisc n R ⊆ V := fun z hz => ⟨hKU hz, hfΩ hz⟩
  have hlift : DifferentiableOn ℂ (h ∘ f) V :=
    hh.comp (hf.mono inter_subset_left) (fun _ hz => hz.2)
  obtain ⟨g, hg, hgrange, hgapprox⟩ := exists_entire_composition_approx hR hε
    (fun y : ℂ × ℂ => (H.symm y : ℂ × ℂ)) hInv (h ∘ f) hV hKV hlift
  refine ⟨g, hg, ?_, ?_⟩
  · intro z
    obtain ⟨y, hy⟩ := hgrange z
    rw [← hy]
    exact (H.symm y).property
  · intro z hz
    have heq : (H.symm (h (f z)) : ℂ × ℂ) = f z := by
      rw [← hH ⟨f z, hfΩ hz⟩]
      simp
    simpa only [Function.comp_apply, heq] using hgapprox z hz

end AutomaticContinuity.OneChartApproximation
