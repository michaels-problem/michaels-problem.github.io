import AutomaticContinuity.CompactBaseFlagFamily

set_option autoImplicit false

/-!
# The actual open image and holomorphic inverse of the compact-base family

The inverse is holomorphic throughout the open image, not only at the zero
section. This supplies honest inverse coordinates for nearby sections on a
compact overlap. No inverse chart or inverse identity is an extra hypothesis.
-/

noncomputable section

namespace AutomaticContinuity.CompactBaseFlagFamily

open Set FlagTotalSpace CenteredPolynomialFamily

theorem exists_open_image_family {n : ℕ} {L U B : Set (FinitePoint n)}
    (hLc : IsCompact L) (hL : IsPolynomiallyConvexOf id L)
    (h : FinitePoint n → Pair) (hU : IsOpen U) (hLU : L ⊆ U)
    (hh : DifferentiableOn ℂ h U) (hadm : ∀ z ∈ L, (z, h z) ∈ totalSet n)
    (happrox : ApproximableOn h L) (hB : IsOpen B) (hBL : B ⊆ L) :
    ∃ (Ω : Set (FinitePoint n × Pair)) (f g : FinitePoint n × Pair → Pair),
      IsOpen Ω ∧ Ω ⊆ B ×ˢ univ ∧ Ω ⊆ totalSet n ∧
      (∀ p ∈ B, (p, h p) ∈ Ω) ∧
      DifferentiableOn ℂ f Ω ∧ DifferentiableOn ℂ g (B ×ˢ univ) ∧
      (∀ p ∈ B, g (p, 0) = h p ∧ f (p, h p) = 0) ∧
      (∀ z ∈ Ω, g (z.1, f z) = z.2) ∧
      ∀ p ∈ B, ∀ w : Pair, (p, g (p, w)) ∈ Ω ∧ f (p, g (p, w)) = w := by
  obtain ⟨S, hS⟩ := exists_initial_state hLc hL h hU hLU hh hadm happrox
  obtain ⟨O, F, G, hO, hOB, hdis, hOzero, hFhol, hGhol,
      hFbase, hGbase, hnorm, H, hH, hHinv⟩ :=
    FixedBaseRadialBasin.exists_biholomorphic_domain hLc hU hLU hB hBL S
  let shift : FinitePoint n × Pair → FinitePoint n × Pair :=
    fun z => (z.1, z.2 - h z.1)
  let Ω : Set (FinitePoint n × Pair) := (B ×ˢ univ) ∩ shift ⁻¹' O
  let f : FinitePoint n × Pair → Pair := fun z => (F (shift z)).2
  let g : FinitePoint n × Pair → Pair := fun z => (G z).2 + h z.1
  have hshift : DifferentiableOn ℂ shift (B ×ˢ univ) :=
    differentiable_fst.differentiableOn.prodMk
      (differentiable_snd.differentiableOn.sub
        (hh.comp differentiable_fst.differentiableOn (fun z hz => hLU (hBL hz.1))))
  have hΩ : IsOpen Ω :=
    hshift.continuousOn.isOpen_inter_preimage (hB.prod isOpen_univ) hO
  have hΩB : Ω ⊆ B ×ˢ univ := inter_subset_left
  have hf : DifferentiableOn ℂ f Ω :=
    (hFhol.comp (hshift.mono hΩB) (fun _ hz => hz.2)).snd
  have hg : DifferentiableOn ℂ g (B ×ˢ univ) :=
    hGhol.snd.add (hh.comp differentiable_fst.differentiableOn
      (fun z hz => hLU (hBL hz.1)))
  have hFG : ∀ y ∈ B ×ˢ (univ : Set Pair), F (G y) = y := by
    intro y hy
    have heq := congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩)
    rw [hH, hHinv] at heq
    exact heq
  have hGF : ∀ x ∈ O, G (F x) = x := by
    intro x hx
    have heq := congrArg Subtype.val (H.symm_apply_apply ⟨x, hx⟩)
    rw [hHinv, hH] at heq
    exact heq
  have hGmem : ∀ y ∈ B ×ˢ (univ : Set Pair), G y ∈ O := by
    intro y hy
    rw [← hHinv ⟨y, hy⟩]
    exact (H.symm ⟨y, hy⟩).property
  have hshiftG (p : FinitePoint n) (w : Pair) : shift (p, g (p, w)) = G (p, w) := by
    apply Prod.ext
    · exact (hGbase (p, w)).symm
    · change (G (p, w)).2 + h p - h p = (G (p, w)).2
      exact add_sub_cancel_right _ _
  refine ⟨Ω, f, g, hΩ, hΩB, ?_, ?_, hf, hg, ?_, ?_, ?_⟩
  · intro z hz hbad
    have hobs : shift z ∈ S.obstacle := by
      rw [hS]
      exact ⟨z, ⟨hbad, hBL hz.1.1, mem_univ _⟩, rfl⟩
    exact Set.disjoint_left.mp hdis hz.2 hobs
  · intro p hp
    refine ⟨⟨hp, mem_univ _⟩, ?_⟩
    change (p, h p - h p) ∈ O
    rw [sub_self]
    exact hOzero p hp
  · intro p hp
    constructor
    · change (G (p, 0)).2 + h p = h p
      rw [(hnorm p hp).2]
      simp
    · change (F (p, h p - h p)).2 = 0
      rw [sub_self, (hnorm p hp).1]
  · intro z hz
    have heq : (z.1, (F (shift z)).2) = F (shift z) := by
      apply Prod.ext
      · exact (hFbase (shift z)).symm
      · rfl
    change (G (z.1, (F (shift z)).2)).2 + h z.1 = z.2
    rw [heq, hGF (shift z) hz.2]
    exact sub_add_cancel _ _
  · intro p hp w
    constructor
    · refine ⟨⟨hp, mem_univ _⟩, ?_⟩
      change shift (p, g (p, w)) ∈ O
      rw [hshiftG]
      exact hGmem _ ⟨hp, mem_univ _⟩
    · change (F (shift (p, g (p, w)))).2 = w
      rw [hshiftG, hFG (p, w) ⟨hp, mem_univ _⟩]

end AutomaticContinuity.CompactBaseFlagFamily
