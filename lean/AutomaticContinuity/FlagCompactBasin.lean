import AutomaticContinuity.FlagInitialRadialState
import AutomaticContinuity.FixedBaseRadialBasin

set_option autoImplicit false

/-!
# An actual entire-fibre family avoiding the forbidden flags over a compact base

The initial separator state and the convergent radial basin are both supplied
by proved theorems. Uncentering gives the prescribed section at fibre zero.
The resulting family is jointly holomorphic over the chosen open base set,
has injective entire fibres, and satisfies the actual finite-flag avoidance
conditions there. No conclusion is asserted over the entire source space.
-/

noncomputable section

namespace AutomaticContinuity.FlagCompactBasin

open Set FlagTotalSpace CenteredPolynomialFamily

abbrev Pair := ℂ × ℂ

/-- A holomorphic family of injective entire fibre maps through the actual
section, together with a normalized left inverse on its image. -/
theorem exists_family {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U B : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ polydisc n R, (z, h z) ∈ totalSet n)
    (hB : IsOpen B) (hBK : B ⊆ polydisc n R) :
    ∃ f g : FinitePoint n × Pair → Pair,
      DifferentiableOn ℂ g (B ×ˢ univ) ∧
      ∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0 ∧
        DifferentiableAt ℂ f (p, h p) ∧
        (∀ w : Pair, f (p, g (p, w)) = w) ∧
        Function.Injective (fun w : Pair => g (p, w)) ∧
        (∀ w : Pair, (p, g (p, w)) ∈ totalSet n) := by
  obtain ⟨S, hS⟩ := FlagInitialRadialState.exists_initial_state hR h hU hKU hh hadm
  obtain ⟨Ω, F, G, hΩ, _, hdis, hΩzero, hFhol, hGhol, _, hGbase, hnorm, H, hH, hHinv⟩ :=
    FixedBaseRadialBasin.exists_biholomorphic_domain
      (isCompact_polydisc n hR) hU hKU hB hBK S
  let f : FinitePoint n × Pair → Pair := fun z => (F (z.1, z.2 - h z.1)).2
  let g : FinitePoint n × Pair → Pair := fun z => (G z).2 + h z.1
  have hf : ∀ p ∈ B, DifferentiableAt ℂ f (p, h p) := by
    intro p hp
    have hshift : DifferentiableOn ℂ
        (fun z : FinitePoint n × Pair => (z.1, z.2 - h z.1)) (U ×ˢ univ) :=
      differentiable_fst.differentiableOn.prodMk
        (differentiable_snd.differentiableOn.sub
          (hh.comp differentiable_fst.differentiableOn (fun z hz => hz.1)))
    have hs := hshift.differentiableAt
      ((hU.prod isOpen_univ).mem_nhds
        (show (p, h p) ∈ U ×ˢ (univ : Set Pair) from ⟨hKU (hBK hp), mem_univ (h p)⟩))
    have hF := (hFhol.differentiableAt (hΩ.mem_nhds (hΩzero p hp))).snd
    have hF' : DifferentiableAt ℂ (fun z => (F z).2)
        ((fun z : FinitePoint n × Pair => (z.1, z.2 - h z.1)) (p, h p)) := by
      simpa only [sub_self] using hF
    have hcomp := hF'.comp (p, h p) hs
    exact hcomp
  have hleft : ∀ p ∈ B, ∀ w : Pair, f (p, g (p, w)) = w := by
    intro p hp w
    let y : B ×ˢ (univ : Set Pair) := ⟨(p, w), hp, mem_univ _⟩
    have hFG := congrArg Subtype.val (H.apply_symm_apply y)
    rw [hH, hHinv] at hFG
    have hpair : (p, (G (p, w)).2) = G (p, w) :=
      Prod.ext (hGbase (p, w)).symm rfl
    change (F (p, (G (p, w)).2 + h p - h p)).2 = w
    rw [add_sub_cancel_right, hpair]
    exact congrArg Prod.snd hFG
  have havoid : ∀ p ∈ B, ∀ w : Pair, (p, g (p, w)) ∉ compactForbiddenGraph n R := by
    intro p hp w hbad
    let y : B ×ˢ (univ : Set Pair) := ⟨(p, w), hp, mem_univ _⟩
    have hmem : G (p, w) ∈ Ω := by
      rw [← hHinv y]
      exact (H.symm y).property
    have hcenter : centerMap h (p, g (p, w)) = G (p, w) := by
      apply Prod.ext
      · exact (hGbase (p, w)).symm
      · change (G (p, w)).2 + h p - h p = (G (p, w)).2
        exact add_sub_cancel_right _ _
    have hobs : G (p, w) ∈ S.obstacle := by
      rw [hS]
      exact ⟨(p, g (p, w)), hbad, hcenter⟩
    exact Set.disjoint_left.mp hdis hmem hobs
  have hg : DifferentiableOn ℂ g (B ×ˢ univ) :=
    hGhol.snd.add (hh.comp differentiable_fst.differentiableOn
      (fun z hz => hKU (hBK hz.1)))
  refine ⟨f, g, hg, ?_⟩
  intro p hp
  refine ⟨?_, ?_, hf p hp, hleft p hp, ?_, ?_⟩
  · change (G (p, 0)).2 + h p = h p
    rw [(hnorm p hp).2]
    simp
  · change (F (p, h p - h p)).2 = 0
    rw [sub_self, (hnorm p hp).1]
  · intro w v hwv
    have heq := congrArg (fun x => f (p, x)) hwv
    simpa only [hleft p hp] using heq
  · intro w hbad
    exact havoid p hp w ⟨hbad, hBK hp, mem_univ _⟩

/-- If the section is admissible on the given neighbourhood, the family is
defined over an open neighbourhood of the original closed polydisc, rather
than merely over its interior. All finite-flag constraints hold for every
fibre point throughout this new neighbourhood. -/
theorem exists_neighbourhood_family {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (h : FinitePoint n → Pair) {U : Set (FinitePoint n)}
    (hU : IsOpen U) (hKU : polydisc n R ⊆ U) (hh : DifferentiableOn ℂ h U)
    (hadm : ∀ z ∈ U, (z, h z) ∈ totalSet n) :
    ∃ (B : Set (FinitePoint n)) (f g : FinitePoint n × Pair → Pair),
      IsOpen B ∧ polydisc n R ⊆ B ∧ B ⊆ U ∧
      DifferentiableOn ℂ g (B ×ˢ univ) ∧
      ∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0 ∧
        DifferentiableAt ℂ f (p, h p) ∧
        (∀ w : Pair, f (p, g (p, w)) = w) ∧
        Function.Injective (fun w : Pair => g (p, w)) ∧
        (∀ w : Pair, (p, g (p, w)) ∈ totalSet n) := by
  obtain ⟨R', hRR', hR'U⟩ := FiniteCauchy.exists_larger_polydisc_subset hR hU hKU
  have hR' : 0 ≤ R' := hR.trans hRR'.le
  let B : Set (FinitePoint n) := Metric.ball 0 R'
  have hBK : B ⊆ polydisc n R' := by
    rw [polydisc_eq_closedBall n hR']
    exact Metric.ball_subset_closedBall
  have hKB : polydisc n R ⊆ B := by
    rw [polydisc_eq_closedBall n hR]
    exact Metric.closedBall_subset_ball hRR'
  obtain ⟨f, g, hg, hproperties⟩ := exists_family hR' h hU hR'U hh
    (fun p hp => hadm p (hR'U hp)) Metric.isOpen_ball hBK
  exact ⟨B, f, g, Metric.isOpen_ball, hKB, hBK.trans hR'U, hg, hproperties⟩

end AutomaticContinuity.FlagCompactBasin
