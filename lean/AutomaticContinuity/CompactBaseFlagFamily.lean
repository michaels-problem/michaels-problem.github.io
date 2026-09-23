import AutomaticContinuity.CompactBaseFlagGeometry
import AutomaticContinuity.FlagCenteredSeparator
import AutomaticContinuity.FixedBaseRadialBasin
import AutomaticContinuity.FlagDominatingFamily

set_option autoImplicit false

/-!
# Actual entire-fibre families over general compact polynomially convex bases

The polynomial approximation premise concerns only the two coordinates of
the supplied section on the specified compact base. It is not an assumed
flag approximation or entire-family theorem. The actual forbidden graph,
cutoff, radial iteration, inverse limits, and normalization are constructed.
The family is jointly holomorphic on each specified open subset of the base.
-/

noncomputable section

namespace AutomaticContinuity.CompactBaseFlagFamily

open Set FlagTotalSpace FlagPolynomialSeparation FlagCenteredSeparator
open CenteredPolynomialFamily

abbrev Pair := ℂ × ℂ

def ApproximableOn {n : ℕ} (h : FinitePoint n → Pair) (L : Set (FinitePoint n)) : Prop :=
  ∀ b : Bool, ∀ ε : ℝ, 0 < ε → ∃ p : MvPolynomial (Fin n) ℂ,
    ∀ z ∈ L, ‖MvPolynomial.eval z p - (if b then (h z).2 else (h z).1)‖ < ε

theorem exists_initial_state {n : ℕ} {L U : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf id L)
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hLU : L ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ L, (z, h z) ∈ totalSet n)
    (happrox : ApproximableOn h L) :
    ∃ S : RadialPushIteration.State L U,
      S.obstacle = centeredObstacle h (CompactBaseFlagGeometry.forbiddenGraph n L) := by
  obtain ⟨q, hqgraph, hqobstacle⟩ := CompactBaseFlagGeometry.exists_forbidden_graph_separator
    hLc hL h (hh.continuousOn.mono hLU) hadm happrox (by norm_num : (0 : ℝ) < 1 / 32)
  have hbase : CompactBaseFlagGeometry.forbiddenGraph n L ⊆ L ×ˢ univ :=
    fun _ hz => hz.2
  obtain ⟨a, ha, hKc, hKbase, hzero, hone, _⟩ := exists_separator_data q h
    hLc (CompactBaseFlagGeometry.isCompact_forbiddenGraph hLc) hU hLU hbase
    hh.continuousOn (fun p hp => (hqgraph p hp).le) (fun z hz => (hqobstacle z hz).le)
  refine ⟨{
    radius := a
    radius_pos := ha
    degree := q.totalDegree
    obstacle := centeredObstacle h (CompactBaseFlagGeometry.forbiddenGraph n L)
    compact_obstacle := hKc
    obstacle_base := hKbase
    polynomial := polynomial q h
    holomorphic_coefficients := holomorphicCoefficientsOn_polynomial q h hh
    degree_bound := fun p _ => totalDegree_polynomial_le q h p
    small_on_cylinder := hzero
    near_one_on_obstacle := fun z hz => (hone z hz).trans (by norm_num)
  }, rfl⟩

/-- Every open part of a compact base with polynomially approximable section
has an actual normalized injective entire-fibre family satisfying all flags. -/
theorem exists_family {n : ℕ} {L U B : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf id L)
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hLU : L ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ L, (z, h z) ∈ totalSet n)
    (happrox : ApproximableOn h L) (hB : IsOpen B) (hBL : B ⊆ L) :
    ∃ f g : FinitePoint n × Pair → Pair,
      DifferentiableOn ℂ g (B ×ˢ univ) ∧
      ∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0 ∧
        DifferentiableAt ℂ f (p, h p) ∧
        (∀ w : Pair, f (p, g (p, w)) = w) ∧
        Function.Injective (fun w : Pair => g (p, w)) ∧
        (∀ w : Pair, (p, g (p, w)) ∈ totalSet n) ∧
        ∃ A : Pair ≃L[ℂ] Pair,
          HasFDerivAt (fun w => g (p, w)) (A : Pair →L[ℂ] Pair) 0 := by
  obtain ⟨S, hS⟩ := exists_initial_state hLc hL h hU hLU hh hadm happrox
  obtain ⟨Ω, F, G, hΩ, _, hdis, hΩzero, hFhol, hGhol, _, hGbase, hnorm, H, hH, hHinv⟩ :=
    FixedBaseRadialBasin.exists_biholomorphic_domain hLc hU hLU hB hBL S
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
        (show (p, h p) ∈ U ×ˢ (univ : Set Pair) from ⟨hLU (hBL hp), mem_univ (h p)⟩))
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
  have havoid : ∀ p ∈ B, ∀ w : Pair,
      (p, g (p, w)) ∉ CompactBaseFlagGeometry.forbiddenGraph n L := by
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
      (fun z hz => hLU (hBL hz.1)))
  refine ⟨f, g, hg, ?_⟩
  intro p hp
  have hg0 : g (p, 0) = h p := by
    change (G (p, 0)).2 + h p = h p
    rw [(hnorm p hp).2]
    simp
  refine ⟨hg0, ?_, hf p hp, hleft p hp, ?_, ?_, ?_⟩
  · change (F (p, h p - h p)).2 = 0
    rw [sub_self, (hnorm p hp).1]
  · intro w v hwv
    have heq := congrArg (fun x => f (p, x)) hwv
    simpa only [hleft p hp] using heq
  · intro w hbad
    exact havoid p hp w ⟨hbad, hBL hp, mem_univ _⟩
  · exact FlagDominatingFamily.vertical_derivative_equiv f g hB hg hp
      (hg0.symm ▸ hf p hp) (hleft p hp)

end AutomaticContinuity.CompactBaseFlagFamily
