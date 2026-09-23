import AutomaticContinuity.CompactBaseFlagMargin
import AutomaticContinuity.CompactConvexPolynomialConvexity
import AutomaticContinuity.ConvexPolynomialApproximation
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

/-! # An entire-fibre family on an actual neighbourhood of a convex compact

Both former scalar premises are discharged: compact convex sets are
polynomially convex, and their holomorphic functions admit polynomial
approximation. A compact thickening permits an open family base containing
the entire original compact, with a fixed positive additive margin.
-/

noncomputable section

namespace AutomaticContinuity.CompactBaseFlagFamily

open Set Metric FlagTotalSpace

theorem approximableOn_of_convex {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (h : FinitePoint n → Pair) (hh : DifferentiableOn ℂ h U) : ApproximableOn h K := by
  intro b ε hε
  cases b
  · simpa using PolynomialFunctionAlgebra.exists_polynomial_approx_on_convex
      hK hconv hU hKU (fun z => (h z).1) hh.fst hε
  · simpa using PolynomialFunctionAlgebra.exists_polynomial_approx_on_convex
      hK hconv hU hKU (fun z => (h z).2) hh.snd hε

theorem exists_neighbourhood_strong_margin_family {n : ℕ} {K U : Set (FinitePoint n)}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hKU : K ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ K, (z, h z) ∈ totalSet n) :
    ∃ (B : Set (FinitePoint n)) (l : ℝ) (Ω : Set (FinitePoint n × Pair))
      (f g : FinitePoint n × Pair → Pair),
      IsOpen B ∧ K ⊆ B ∧ B ⊆ U ∧
      1 < l ∧ IsOpen Ω ∧ Ω ⊆ B ×ˢ univ ∧ Ω ⊆ totalSet n ∧
      (∀ p ∈ B, (p, h p) ∈ Ω) ∧
      DifferentiableOn ℂ f Ω ∧ DifferentiableOn ℂ g (B ×ˢ univ) ∧
      (∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0) ∧
      (∀ z ∈ Ω, g (z.1, f z) = z.2) ∧
      (∀ p ∈ B, ∀ w : Pair, (p, g (p, w)) ∈ Ω ∧ f (p, g (p, w)) = w) ∧
      ∀ p ∈ B, ∀ w e : Pair, euclideanPairNorm e ≤ l - 1 →
        (p, g (p, w) + e) ∈ totalSet n := by
  let O := U ∩ (fun z => (z, h z)) ⁻¹' totalSet n
  have hO : IsOpen O :=
    (continuousOn_id.prodMk hh.continuousOn).isOpen_inter_preimage hU (isOpen_totalSet n)
  have hKO : K ⊆ O := fun z hz => ⟨hKU hz, hadm z hz⟩
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let L := cthickening δ K
  let B := thickening δ K
  have hLc : IsCompact L := hK.cthickening
  have hLconv : Convex ℝ L := hconv.cthickening δ
  have hLU : L ⊆ U := fun z hz => (hδO hz).1
  have hBL : B ⊆ L := thickening_subset_cthickening δ K
  obtain ⟨l, Ω, f, g, hl, hΩ, hΩB, hΩadm, hgraph, hf, hg, hzero, hGF, hFG, hmargin⟩ :=
    exists_strong_margin_open_image_family hLc
      (isPolynomiallyConvexOf_compact_convex hLc hLconv) h hU hLU hh
      (fun z hz => (hδO hz).2)
      (approximableOn_of_convex hLc hLconv hU hLU h hh) isOpen_thickening hBL
  exact ⟨B, l, Ω, f, g, isOpen_thickening, self_subset_thickening hδ K,
    hBL.trans hLU, hl, hΩ, hΩB, hΩadm, hgraph, hf, hg, hzero, hGF, hFG, hmargin⟩

end AutomaticContinuity.CompactBaseFlagFamily
