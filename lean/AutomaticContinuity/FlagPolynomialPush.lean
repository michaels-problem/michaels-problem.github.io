import AutomaticContinuity.FlagCenteredSeparator
import AutomaticContinuity.RadialPolynomialPush

set_option autoImplicit false

/-!
# An actual radial push from a flag section-graph separator

The input separator is a particular polynomial in the original flag
coordinates. The resulting maps are actual fibre homeomorphisms with both
directions jointly holomorphic on the given base domain. Uncentering fixes
the original section and retains both protected approximation estimates.
-/

noncomputable section

namespace AutomaticContinuity.FlagPolynomialPush

open Set FlagPolynomialSeparation FlagCenteredSeparator CenteredPolynomialFamily
open FlagTotalSpace

abbrev Pair := ℂ × ℂ

/-- The actual centered push, with a radius obtained from the original
polynomial separator before choosing any cutoff amplification. -/
theorem exists_centered_push {n : ℕ} (q : Polynomial n) (h : FinitePoint n → Pair)
    {L U : Set (FinitePoint n)} {K : Set (Point n)} {c ε : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ) (hh : DifferentiableOn ℂ h U)
    (hgraph : ∀ p ∈ L, ‖evaluate (p, h p) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖evaluate z q - 1‖ ≤ 1 / 32)
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : FinitePoint n → Pair ≃ₜ Pair,
      (∀ p, Φ p 0 = 0) ∧
      DifferentiableOn ℂ (fun z : Point n => Φ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : Point n => (Φ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ z ∈ L ×ˢ closedEuclideanBall a,
        euclideanPairNorm (Φ z.1 z.2 - z.2) < ε ∧
        euclideanPairNorm ((Φ z.1).symm z.2 - z.2) < ε) ∧
      (∀ z ∈ centeredObstacle h K,
        euclideanPairNorm (Φ z.1 z.2 - (1 + c) • z.2) < ε) := by
  obtain ⟨a, ha, hKc, hKbase, hzero, hone, _⟩ :=
    exists_separator_data q h hL hK hU hLU hKL hh.continuousOn hgraph hobstacle
  obtain ⟨Φ, hΦ⟩ := RadialPolynomialPush.exists_compact_push (polynomial q h) q.totalDegree
    hL hKc hU hLU hKbase hc hε (holomorphicCoefficientsOn_polynomial q h hh)
    (fun p _ => totalDegree_polynomial_le q h p) hzero
    (fun z hz => (hone z hz).trans (by norm_num))
  exact ⟨a, ha, Φ, hΦ⟩

section Uncentering

variable {P : Type*}

def uncenter (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) (p : P) : Pair ≃ₜ Pair where
  toFun w := Φ p (w - h p) + h p
  invFun w := (Φ p).symm (w - h p) + h p
  left_inv w := by simp
  right_inv w := by simp
  continuous_toFun := ((Φ p).continuous.comp (continuous_id.sub continuous_const)).add continuous_const
  continuous_invFun := ((Φ p).symm.continuous.comp
    (continuous_id.sub continuous_const)).add continuous_const

@[simp] theorem uncenter_apply (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) (p : P) (w : Pair) :
    uncenter h Φ p w = Φ p (w - h p) + h p := rfl

@[simp] theorem uncenter_symm_apply (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) (p : P) (w : Pair) :
    (uncenter h Φ p).symm w = (Φ p).symm (w - h p) + h p := rfl

theorem uncenter_fixes_section (h : P → Pair) (Φ : P → Pair ≃ₜ Pair)
    (hΦ : ∀ p, Φ p 0 = 0) (p : P) : uncenter h Φ p (h p) = h p := by simp [hΦ]

theorem uncenter_error (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) (p : P) (w : Pair) :
    uncenter h Φ p w - w = Φ p (w - h p) - (w - h p) := by
  rw [uncenter_apply]
  abel

theorem uncenter_inverse_error (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) (p : P) (w : Pair) :
    (uncenter h Φ p).symm w - w = (Φ p).symm (w - h p) - (w - h p) := by
  rw [uncenter_symm_apply]
  abel

theorem uncenter_radial_error (h : P → Pair) (Φ : P → Pair ≃ₜ Pair)
    (p : P) (w : Pair) (r : ℝ) :
    uncenter h Φ p w - (h p + r • (w - h p)) =
      Φ p (w - h p) - r • (w - h p) := by
  rw [uncenter_apply]
  abel

variable [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem differentiableOn_uncenter (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) {U : Set P}
    (hh : DifferentiableOn ℂ h U)
    (hΦ : DifferentiableOn ℂ (fun z : P × Pair => Φ z.1 z.2) (U ×ˢ univ)) :
    DifferentiableOn ℂ (fun z : P × Pair => uncenter h Φ z.1 z.2) (U ×ˢ univ) := by
  have hb : DifferentiableOn ℂ (fun z : P × Pair => h z.1) (U ×ˢ univ) :=
    hh.comp differentiable_fst.differentiableOn (fun _ hz => hz.1)
  exact (hΦ.comp (differentiable_fst.differentiableOn.prodMk
    (differentiable_snd.differentiableOn.sub hb))
      (fun _ hz => ⟨hz.1, mem_univ _⟩)).add hb

theorem differentiableOn_uncenter_symm (h : P → Pair) (Φ : P → Pair ≃ₜ Pair) {U : Set P}
    (hh : DifferentiableOn ℂ h U)
    (hΦ : DifferentiableOn ℂ (fun z : P × Pair => (Φ z.1).symm z.2) (U ×ˢ univ)) :
    DifferentiableOn ℂ (fun z : P × Pair => (uncenter h Φ z.1).symm z.2) (U ×ˢ univ) := by
  have hb : DifferentiableOn ℂ (fun z : P × Pair => h z.1) (U ×ˢ univ) :=
    hh.comp differentiable_fst.differentiableOn (fun _ hz => hz.1)
  exact (hΦ.comp (differentiable_fst.differentiableOn.prodMk
    (differentiable_snd.differentiableOn.sub hb))
      (fun _ hz => ⟨hz.1, mem_univ _⟩)).add hb

end Uncentering

/-- In the original coordinates the actual automorphism fixes the section,
is close to the identity in both directions on one uniform tube around it,
and approximates radial motion of the original compact obstacle about the
section. Every norm in the conclusion is explicitly Euclidean. -/
theorem exists_section_radial_push {n : ℕ} (q : Polynomial n) (h : FinitePoint n → Pair)
    {L U : Set (FinitePoint n)} {K : Set (Point n)} {c ε : ℝ}
    (hL : IsCompact L) (hK : IsCompact K) (hU : IsOpen U)
    (hLU : L ⊆ U) (hKL : K ⊆ L ×ˢ univ) (hh : DifferentiableOn ℂ h U)
    (hgraph : ∀ p ∈ L, ‖evaluate (p, h p) q‖ ≤ 1 / 32)
    (hobstacle : ∀ z ∈ K, ‖evaluate z q - 1‖ ≤ 1 / 32)
    (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ Ψ : FinitePoint n → Pair ≃ₜ Pair,
      (∀ p, Ψ p (h p) = h p) ∧
      DifferentiableOn ℂ (fun z : Point n => Ψ z.1 z.2) (U ×ˢ univ) ∧
      DifferentiableOn ℂ (fun z : Point n => (Ψ z.1).symm z.2) (U ×ˢ univ) ∧
      (∀ p ∈ L, ∀ w : Pair, euclideanPairNorm (w - h p) ≤ a →
        euclideanPairNorm (Ψ p w - w) < ε ∧ euclideanPairNorm ((Ψ p).symm w - w) < ε) ∧
      (∀ z ∈ K,
        euclideanPairNorm (Ψ z.1 z.2 - (h z.1 + (1 + c) • (z.2 - h z.1))) < ε) := by
  obtain ⟨a, ha, Φ, hfix, hhol, hholi, hprotected, hpush⟩ :=
    exists_centered_push q h hL hK hU hLU hKL hh hgraph hobstacle hc hε
  refine ⟨a, ha, uncenter h Φ, uncenter_fixes_section h Φ hfix,
    differentiableOn_uncenter h Φ hh hhol, differentiableOn_uncenter_symm h Φ hh hholi,
    ?_, ?_⟩
  · intro p hp w hw
    simpa only [uncenter_error, uncenter_inverse_error] using
      hprotected (p, w - h p) ⟨hp, hw⟩
  · intro z hz
    have hm : centerMap h z ∈ centeredObstacle h K := ⟨z, hz, rfl⟩
    simpa only [uncenter_radial_error, centerMap] using hpush (centerMap h z) hm

end AutomaticContinuity.FlagPolynomialPush
