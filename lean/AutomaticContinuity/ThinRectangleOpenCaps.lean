import AutomaticContinuity.ThinRectangleProduct

set_option autoImplicit false

/-!
# Open cap buffers retaining overlap and contour gaps

The compact cap geometry is enlarged to actual open domains suitable for
holomorphic gluing. A separate compact transverse buffer bounds corrections
throughout the chosen open transverse domain.
-/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Metric

theorem exists_open_caps {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {A B VA VB W : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hW : IsOpen W)
    (hAVA : A ⊆ VA) (hBVB : B ⊆ VB) (hABW : A ∩ B ⊆ W) :
    ∃ A' B' : Set X, IsOpen A' ∧ IsOpen B' ∧ A ⊆ A' ∧ B ⊆ B' ∧
      A' ⊆ VA ∧ B' ⊆ VB ∧ A' ∩ B' ⊆ W := by
  have hdis : Disjoint (A \ W) B := Set.disjoint_left.mpr (by
    intro x hx hxB
    exact hx.2 (hABW ⟨hx.1, hxB⟩))
  obtain ⟨Oa, Ob, hOa, hOb, hAOa, hBOb, hdisO⟩ :=
    normal_separation (hA.diff hW).isClosed hB.isClosed hdis
  refine ⟨(Oa ∪ W) ∩ VA, Ob ∩ VB, (hOa.union hW).inter hVA, hOb.inter hVB,
    ?_, fun x hx => ⟨hBOb hx, hBVB hx⟩, inter_subset_right, inter_subset_right, ?_⟩
  · intro x hx
    refine ⟨?_, hAVA hx⟩
    by_cases hxW : x ∈ W
    · exact Or.inr hxW
    · exact Or.inl (hAOa ⟨hx, hxW⟩)
  · intro x hx
    rcases hx.1.1 with hxOa | hxW
    · exact (Set.disjoint_left.mp hdisO hxOa hx.2.1).elim
    · exact hxW

theorem gap_on_thickening {A T : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ z ∈ A, ∀ ζ ∈ T, δ ≤ ‖ζ-z‖) :
    ∀ z ∈ thickening (δ/4) A, ∀ ζ ∈ T, δ/2 ≤ ‖ζ-z‖ := by
  intro z hz ζ hζ
  obtain ⟨a, ha, hza⟩ := mem_thickening_iff.mp hz
  have hg := hgap a ha ζ hζ
  have ht := dist_triangle ζ z a
  rw [dist_eq_norm ζ a, dist_eq_norm ζ z] at ht
  linarith

theorem exists_open_caps_with_gaps {A B VA VB W TA TB : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B)
    (hVA : IsOpen VA) (hVB : IsOpen VB) (hW : IsOpen W)
    (hAVA : A ⊆ VA) (hBVB : B ⊆ VB) (hABW : A ∩ B ⊆ W)
    {δ : ℝ} (hδ : 0 < δ)
    (hgapA : ∀ z ∈ A, ∀ ζ ∈ TA, δ ≤ ‖ζ-z‖)
    (hgapB : ∀ z ∈ B, ∀ ζ ∈ TB, δ ≤ ‖ζ-z‖) :
    ∃ A' B' : Set ℂ, IsOpen A' ∧ IsOpen B' ∧ A ⊆ A' ∧ B ⊆ B' ∧
      A' ⊆ VA ∧ B' ⊆ VB ∧ A' ∩ B' ⊆ W ∧
      (∀ z ∈ A', ∀ ζ ∈ TA, δ/2 ≤ ‖ζ-z‖) ∧
      (∀ z ∈ B', ∀ ζ ∈ TB, δ/2 ≤ ‖ζ-z‖) := by
  obtain ⟨A', B', hA', hB', hAA', hBB', hsubA, hsubB, hmeet⟩ :=
    exists_open_caps hA hB (hVA.inter isOpen_thickening) (hVB.inter isOpen_thickening)
      hW (subset_inter hAVA (self_subset_thickening (by positivity : 0 < δ/4) A))
      (subset_inter hBVB (self_subset_thickening (by positivity : 0 < δ/4) B)) hABW
  exact ⟨A', B', hA', hB', hAA', hBB', hsubA.trans inter_subset_left,
    hsubB.trans inter_subset_left, hmeet,
    fun z hz => gap_on_thickening hδ hgapA z (hsubA hz).2,
    fun z hz => gap_on_thickening hδ hgapB z (hsubB hz).2⟩

theorem exists_transverse_compact_buffer {P : Type*} [TopologicalSpace P]
    [LocallyCompactSpace P] [RegularSpace P] {D O : Set P}
    (hD : IsCompact D) (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (D' V : Set P), IsCompact D' ∧ IsOpen V ∧ D ⊆ V ∧ V ⊆ D' ∧ D' ⊆ O := by
  obtain ⟨D', hD', _, hDD', hD'O⟩ := exists_compact_closed_between hD hO hDO
  exact ⟨D', interior D', hD', isOpen_interior, hDD', interior_subset, hD'O⟩

end AutomaticContinuity.ThinRectangleGeometry
