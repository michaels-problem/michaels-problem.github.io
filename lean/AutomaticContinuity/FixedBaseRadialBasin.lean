import AutomaticContinuity.RadialAdaptiveIteration
import AutomaticContinuity.RadialIterationBudgets
import AutomaticContinuity.NonautonomousInverseLimit
import AutomaticContinuity.NonautonomousBiholomorphism

set_option autoImplicit false

/-!
# An actual holomorphic basin avoiding the compact obstacle

Starting with one polynomial separator state, adaptive radial pushes produce
an open domain over any open subset of the fixed compact base. The domain
contains the zero section, avoids the original obstacle, and is biholomorphic
to the full fibre product. Both maps are limits of actual inverse pairs.
There is no infinite-construction, convergence or domain-inclusion premise.
This is a fixed-base result, not a global finite-flag extension theorem.
-/

noncomputable section

namespace AutomaticContinuity.FixedBaseRadialBasin

open Set Filter RadialPushIteration ParameterFibreComposition
open scoped Topology

abbrev Pair := ℂ × ℂ

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [ProperSpace P]

theorem exists_biholomorphic_domain {L U B : Set P}
    (hL : IsCompact L) (hU : IsOpen U) (hLU : L ⊆ U)
    (hB : IsOpen B) (hBL : B ⊆ L) (S₀ : State L U) :
    ∃ (Ω : Set (P × Pair)) (F G : P × Pair → P × Pair),
      IsOpen Ω ∧ Ω ⊆ B ×ˢ univ ∧ Disjoint Ω S₀.obstacle ∧
      (∀ p ∈ B, (p, 0) ∈ Ω) ∧
      DifferentiableOn ℂ F Ω ∧ DifferentiableOn ℂ G (B ×ˢ univ) ∧
      (∀ z, (F z).1 = z.1) ∧ (∀ z, (G z).1 = z.1) ∧
      (∀ p ∈ B, F (p, 0) = (p, 0) ∧ G (p, 0) = (p, 0)) ∧
      ∃ H : Ω ≃ₜ (B ×ˢ (univ : Set Pair)),
        (∀ x : Ω, (H x : P × Pair) = F x.val) ∧
        (∀ y : B ×ˢ (univ : Set Pair), (H.symm y : P × Pair) = G y.val) := by
  let a := RadialIterationBudgets.radius S₀.radius
  let r := RadialIterationBudgets.entryRadius S₀.radius
  let b := RadialIterationBudgets.budget S₀.radius
  have ha : Monotone a := RadialIterationBudgets.radius_monotone S₀.radius_pos.le
  have hbp : ∀ n, 0 < b n := RadialIterationBudgets.budget_pos S₀.radius_pos
  have hbh : ∀ n, b (n + 1) ≤ b n / 2 := fun n =>
    (RadialIterationBudgets.budget_half S₀.radius n).le
  obtain ⟨I⟩ := RadialAdaptiveIteration.exists_adaptive_iteration hL hU hLU S₀ b hbp
  let e := I.toIteration.map
  have hprod (n : ℕ) : product e n = (I.history n).cumulative := I.cumulative_eq n
  have hrad (n : ℕ) : (I.history n).state.radius = a n := I.toIteration.radius n
  have he (n : ℕ) : DifferentiableOn ℂ (fun z : P × Pair => e n z.1 z.2) (B ×ˢ univ) :=
    (I.step n).holomorphic.mono (fun z hz => ⟨hLU (hBL hz.1), hz.2⟩)
  have hei (n : ℕ) : DifferentiableOn ℂ (fun z : P × Pair => (e n z.1).symm z.2) (B ×ˢ univ) :=
    (I.step n).inverse_holomorphic.mono (fun z hz => ⟨hLU (hBL hz.1), hz.2⟩)
  have herr (n : ℕ) (p : P) (hp : p ∈ B) (w : Pair) (hw : euclideanPairNorm w ≤ a n) :
      euclideanPairNorm (e n p w - w) ≤ b n / 4 ∧
      euclideanPairNorm ((e n p).symm w - w) ≤ b n / 4 := by
    have hz : (p, w) ∈ RadialAdaptiveIteration.cylinder (I.history n) := by
      change p ∈ L ∧ euclideanPairNorm w ≤ (I.history n).state.radius
      exact ⟨hBL hp, (hrad n).symm ▸ hw⟩
    have hh := RadialAdaptiveIteration.factor_errors hL hU hLU b hbp I n hz
    exact ⟨hh.1.le, hh.2.le⟩
  have hinc (n : ℕ) (z : P × Pair) (hz : z ∈ NonautonomousInverseLimit.cylinder L (a n)) :
      euclideanPairNorm ((product e (n + 1) z.1).symm z.2 -
        (product e n z.1).symm z.2) ≤ b n / 4 := by
    rw [hprod (n + 1), hprod n]
    exact (RadialAdaptiveIteration.inverse_increment_on_geometric_cylinder
      hL hU hLU b hbp I n hz).le
  obtain ⟨G, _, hG, _, _⟩ := NonautonomousInverseLimit.exists_holomorphic_inverse_limit
    (product e) hB hBL hLU a b ha
    (RadialIterationBudgets.radius_exhaustive S₀.radius_pos) hbp hbh
    (fun n => I.toIteration.cumulative_inverse_holomorphic n) hinc
  have hGzero (p : P) (hp : p ∈ B) : G (p, 0) = 0 := by
    have hl := hG.tendsto_at (show (p, (0 : Pair)) ∈ B ×ˢ univ from ⟨hp, mem_univ _⟩)
    have hzero (n : ℕ) : (product e n p).symm 0 = 0 :=
      product_symm_origin e n p (fun i _ => (I.step i).fixes_zero p)
    have hconst : Tendsto (fun n => (product e n p).symm 0) atTop (𝓝 (0 : Pair)) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Pair)) atTop (𝓝 0))
    exact tendsto_nhds_unique hl hconst
  obtain ⟨F, hFhol, hGhol, H, hH, hHinv⟩ :=
    NonautonomousBiholomorphism.exists_biholomorphism_of_inverse_convergence e hB he hei r a b
      (RadialIterationBudgets.entryRadius_le_radius S₀.radius_pos.le) ha
      (RadialIterationBudgets.entry_gap S₀.radius_pos.le) hbp hbh
      (RadialIterationBudgets.exists_entry_margin S₀.radius_pos)
      (fun n p hp w hw => (herr n p hp w hw).1)
      (fun n p hp w hw => (herr n p hp w hw).2) G hG
  have hFzero (p : P) (hp : p ∈ B) : F (p, 0) = 0 := by
    let y : B ×ˢ (univ : Set Pair) := ⟨(p, 0), hp, mem_univ _⟩
    have hh := congrArg Subtype.val (H.apply_symm_apply y)
    rw [hH, hHinv] at hh
    simpa only [y, hGzero p hp] using congrArg Prod.snd hh
  refine ⟨NonautonomousEntryDomains.domain e B r,
    (fun z => (z.1, F z)), (fun z => (z.1, G z)),
    NonautonomousEntryDomains.isOpen_domain e hB r (fun n => (he n).continuousOn),
    NonautonomousEntryDomains.domain_subset_base e B r, ?_, ?_,
    hFhol, hGhol, (fun _ => rfl), (fun _ => rfl), ?_, H, hH, hHinv⟩
  · apply NonautonomousEntryDomains.disjoint_domain_of_escape
    intro n z hz
    exact (RadialIterationBudgets.entryRadius_le_radius S₀.radius_pos.le n).trans
      (I.toIteration.cumulative_obstacle_escapes n hz).le
  · intro p hp
    apply NonautonomousEntryDomains.entry_subset_domain e B r 0
    apply NonautonomousEntryDomains.zero_mem_entry e B r 0 hp
    · exact RadialIterationBudgets.entryRadius_pos S₀.radius_pos 0
    · intro i hi
      omega
  · intro p hp
    exact ⟨Prod.ext rfl (hFzero p hp), Prod.ext rfl (hGzero p hp)⟩

end AutomaticContinuity.FixedBaseRadialBasin
