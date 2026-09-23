import AutomaticContinuity.CompactBaseFlagInverse
import AutomaticContinuity.FlagScalingBuffer

set_option autoImplicit false

/-!
# A uniform-margin compact-base family with its genuine open inverse domain

Both the scaling factor and the family are constructed. The approximation
premise is stable under the constant inward scaling and only concerns the
two scalar coordinates of the original section on the specified compact.
-/

noncomputable section

namespace AutomaticContinuity.CompactBaseFlagFamily

open Set FlagTotalSpace

theorem ApproximableOn.real_smul {n : ℕ} {h : FinitePoint n → Pair}
    {L : Set (FinitePoint n)} (hh : ApproximableOn h L) (c : ℝ) :
    ApproximableOn (fun z => c • h z) L := by
  intro b ε hε
  by_cases hc : c = 0
  · subst c
    refine ⟨0, ?_⟩
    intro z _hz
    simpa using hε
  · have hcnorm : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast hc)
    obtain ⟨p, hp⟩ := hh b (ε / ‖(c : ℂ)‖) (div_pos hε hcnorm)
    refine ⟨MvPolynomial.C (c : ℂ) * p, ?_⟩
    intro z hz
    have heq : MvPolynomial.eval z (MvPolynomial.C (c : ℂ) * p) -
        (if b then (c • h z).2 else (c • h z).1) =
        (c : ℂ) * (MvPolynomial.eval z p - (if b then (h z).2 else (h z).1)) := by
      cases b <;> simp [Complex.real_smul, mul_sub]
    rw [heq, norm_mul]
    calc
      ‖(c : ℂ)‖ * ‖MvPolynomial.eval z p - (if b then (h z).2 else (h z).1)‖ <
          ‖(c : ℂ)‖ * (ε / ‖(c : ℂ)‖) := mul_lt_mul_of_pos_left (hp z hz) hcnorm
      _ = ε := by field_simp

/-- A concrete entire-fibre family has a fixed positive additive margin and
an actual open image with holomorphic inverse. `B` is the supplied open part
of the compact base; no whole-source extension is asserted. -/
theorem exists_strong_margin_open_image_family {n : ℕ} {L U B : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf id L)
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hLU : L ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ L, (z, h z) ∈ totalSet n)
    (happrox : ApproximableOn h L) (hB : IsOpen B) (hBL : B ⊆ L) :
    ∃ (l : ℝ) (Ω : Set (FinitePoint n × Pair)) (f g : FinitePoint n × Pair → Pair),
      1 < l ∧ IsOpen Ω ∧ Ω ⊆ B ×ˢ univ ∧ Ω ⊆ totalSet n ∧
      (∀ p ∈ B, (p, h p) ∈ Ω) ∧
      DifferentiableOn ℂ f Ω ∧ DifferentiableOn ℂ g (B ×ˢ univ) ∧
      (∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0) ∧
      (∀ z ∈ Ω, g (z.1, f z) = z.2) ∧
      (∀ p ∈ B, ∀ w : Pair, (p, g (p, w)) ∈ Ω ∧ f (p, g (p, w)) = w) ∧
      ∀ p ∈ B, ∀ w e : Pair, euclideanPairNorm e ≤ l - 1 →
        (p, g (p, w) + e) ∈ totalSet n := by
  obtain ⟨l, V, hl, hV, hLV, hVU, hscaled⟩ :=
    FlagScalingBuffer.exists_scaling_neighbourhood hLc hU hLU h hh.continuousOn hadm
  have hlne : l ≠ 0 := ne_of_gt (lt_trans zero_lt_one hl)
  obtain ⟨O, F, G, hO, hOB, hOadm, hOgraph, hF, hG, hnorm, hGF, hFG⟩ :=
    exists_open_image_family hLc hL (fun z => l⁻¹ • h z) hV hLV
      ((hh.mono hVU).const_smul l⁻¹) (fun z hz => hscaled z (hLV hz))
      (happrox.real_smul l⁻¹) hB hBL
  let scale : FinitePoint n × Pair → FinitePoint n × Pair := fun z => (z.1, l⁻¹ • z.2)
  let Ω : Set (FinitePoint n × Pair) := scale ⁻¹' O
  let f : FinitePoint n × Pair → Pair := fun z => F (scale z)
  let g : FinitePoint n × Pair → Pair := fun z => l • G z
  have hscale : Differentiable ℂ scale :=
    differentiable_fst.prodMk (differentiable_snd.const_smul l⁻¹)
  have hΩ : IsOpen Ω := hO.preimage hscale.continuous
  have hΩB : Ω ⊆ B ×ˢ univ := fun z hz => ⟨(hOB hz).1, mem_univ _⟩
  have hf : DifferentiableOn ℂ f Ω :=
    hF.comp hscale.differentiableOn (fun _ hz => hz)
  have hg : DifferentiableOn ℂ g (B ×ˢ univ) := hG.const_smul l
  have hscaleg (p : FinitePoint n) (w : Pair) : scale (p, g (p, w)) = (p, G (p, w)) := by
    change (p, l⁻¹ • (l • G (p, w))) = (p, G (p, w))
    rw [smul_smul, inv_mul_cancel₀ hlne, one_smul]
  have hmargin : ∀ p ∈ B, ∀ w e : Pair, euclideanPairNorm e ≤ l - 1 →
      (p, g (p, w) + e) ∈ totalSet n := by
    intro p hp w e he
    exact FlagScalingBuffer.admissible_smul_add hl (hOadm (hFG p hp w).1) he
  refine ⟨l, Ω, f, g, hl, hΩ, hΩB, ?_, ?_, hf, hg, ?_, ?_, ?_, hmargin⟩
  · intro z hz
    have hgood := FlagScalingBuffer.admissible_smul_add hl (hOadm hz)
      (show euclideanPairNorm (0 : Pair) ≤ l - 1 by
        rw [euclideanPairNorm_zero]
        exact (sub_pos.mpr hl).le)
    change (z.1, l • (l⁻¹ • z.2) + 0) ∈ totalSet n at hgood
    simpa only [smul_smul, mul_inv_cancel₀ hlne, one_smul, add_zero] using hgood
  · intro p hp
    exact hOgraph p hp
  · intro p hp
    constructor
    · change l • G (p, 0) = h p
      rw [(hnorm p hp).1, smul_smul, mul_inv_cancel₀ hlne, one_smul]
    · exact (hnorm p hp).2
  · intro z hz
    have hinv := hGF (scale z) hz
    change G (z.1, F (scale z)) = l⁻¹ • z.2 at hinv
    change l • G (z.1, F (scale z)) = z.2
    rw [hinv, smul_smul, mul_inv_cancel₀ hlne, one_smul]
  · intro p hp w
    constructor
    · change scale (p, g (p, w)) ∈ O
      rw [hscaleg]
      exact (hFG p hp w).1
    · change F (scale (p, g (p, w))) = w
      rw [hscaleg]
      exact (hFG p hp w).2

end AutomaticContinuity.CompactBaseFlagFamily
