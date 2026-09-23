import AutomaticContinuity.FlagScalingBuffer
import AutomaticContinuity.FlagDominatingFamily

set_option autoImplicit false

/-!
# Entire-fibre families with a uniform additive flag margin

Scale the given section slightly inward on a compact neighbourhood, use the
proved actual compact-base family, and scale its target values outward.
Every fibre value then permits the same positive additive perturbation.
The tolerance is independent of the entire fibre parameter. All statements
remain local in the source variable, on an open neighbourhood of the polydisc.
-/

noncomputable section

namespace AutomaticContinuity.FlagStrongMarginFamily

open Set FlagTotalSpace

abbrev Pair := ℂ × ℂ

/-- The actual family has a uniform additive margin, injective entire fibres,
a normalized differentiable left inverse, and invertible vertical derivative.
Only admissibility on the original compact polydisc is required. -/
theorem exists_neighbourhood_family {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ totalSet n) :
    ∃ (l : ℝ) (B : Set (FinitePoint n)) (f g : FinitePoint n × Pair → Pair),
      1 < l ∧ IsOpen B ∧ polydisc n R ⊆ B ∧ B ⊆ U ∧
      DifferentiableOn ℂ g (B ×ˢ univ) ∧
      ∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0 ∧
        DifferentiableAt ℂ f (p, h p) ∧
        (∀ w : Pair, f (p, g (p, w)) = w) ∧
        Function.Injective (fun w : Pair => g (p, w)) ∧
        (∀ w e : Pair, euclideanPairNorm e ≤ l - 1 →
          (p, g (p, w) + e) ∈ totalSet n) ∧
        ∃ A : Pair ≃L[ℂ] Pair,
          HasFDerivAt (fun w => g (p, w)) (A : Pair →L[ℂ] Pair) 0 := by
  obtain ⟨l, V, hl, hV, hKV, hVU, hscaled⟩ :=
    FlagScalingBuffer.exists_scaling_neighbourhood (isCompact_polydisc n hR)
      hU hKU h hh.continuousOn hadm
  have hlne : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  have hh' : DifferentiableOn ℂ (fun p => l⁻¹ • h p) V :=
    (hh.mono hVU).const_smul l⁻¹
  obtain ⟨B, F, G, hB, hKB, hBV, hG, hproperties⟩ :=
    FlagCompactBasin.exists_neighbourhood_family hR (fun p => l⁻¹ • h p)
      hV hKV hh' hscaled
  let f : FinitePoint n × Pair → Pair := fun z => F (z.1, l⁻¹ • z.2)
  let g : FinitePoint n × Pair → Pair := fun z => l • G z
  have hg : DifferentiableOn ℂ g (B ×ˢ univ) := hG.const_smul l
  refine ⟨l, B, f, g, hl, hB, hKB, hBV.trans hVU, hg, ?_⟩
  intro p hp
  obtain ⟨hG0, hF0, hF, hleft, hinj, havoid⟩ := hproperties p hp
  have hg0 : g (p, 0) = h p := by
    change l • G (p, 0) = h p
    rw [hG0, smul_smul, mul_inv_cancel₀ hlne, one_smul]
  have hf0 : f (p, h p) = 0 := hF0
  have hf : DifferentiableAt ℂ f (p, h p) := by
    have hpre : DifferentiableAt ℂ
        (fun z : FinitePoint n × Pair => (z.1, l⁻¹ • z.2)) (p, h p) :=
      (differentiable_fst.prodMk (differentiable_snd.const_smul l⁻¹)).differentiableAt
    have hcomp := hF.comp (p, h p) hpre
    exact hcomp
  have hfg : ∀ w : Pair, f (p, g (p, w)) = w := by
    intro w
    change F (p, l⁻¹ • (l • G (p, w))) = w
    rw [smul_smul, inv_mul_cancel₀ hlne, one_smul, hleft]
  have hginj : Function.Injective (fun w : Pair => g (p, w)) := by
    intro w v hwv
    have heq := congrArg (fun y => f (p, y)) hwv
    simpa only [hfg] using heq
  refine ⟨hg0, hf0, hf, hfg, hginj, ?_, ?_⟩
  · intro w e he
    exact FlagScalingBuffer.admissible_smul_add hl (havoid w) he
  · exact FlagDominatingFamily.vertical_derivative_equiv f g hB hg hp
      (hg0.symm ▸ hf) hfg

end AutomaticContinuity.FlagStrongMarginFamily
