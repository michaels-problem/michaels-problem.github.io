import AutomaticContinuity.ThinRectangleOpenCaps

set_option autoImplicit false

/-! # A convex compact transverse buffer inside a prescribed open set -/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Metric

theorem exists_convex_transverse_compact_buffer {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [LocallyCompactSpace P]
    {D O : Set P} (hD : IsCompact D) (hDconv : Convex ℝ D)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (D' V : Set P), IsCompact D' ∧ Convex ℝ D' ∧
      IsOpen V ∧ Convex ℝ V ∧ D ⊆ V ∧ V ⊆ D' ∧ D' ⊆ O := by
  obtain ⟨ε, hε, hcompact⟩ := hD.exists_isCompact_cthickening
  obtain ⟨δ, hδ, hδO⟩ := hD.exists_cthickening_subset_open hO hDO
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  refine ⟨cthickening r D, thickening r D, ?_, hDconv.cthickening r,
    isOpen_thickening, hDconv.thickening r, self_subset_thickening hr D,
    thickening_subset_cthickening r D, (cthickening_mono (min_le_right ε δ) D).trans hδO⟩
  exact hcompact.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_left ε δ) D)

theorem exists_transverse_compact_convex_buffer {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [LocallyCompactSpace P]
    {D O : Set P} (hD : IsCompact D) (hDconv : Convex ℝ D)
    (hO : IsOpen O) (hDO : D ⊆ O) :
    ∃ (D' V : Set P), IsCompact D' ∧ Convex ℝ D' ∧
      IsOpen V ∧ D ⊆ V ∧ V ⊆ D' ∧ D' ⊆ O := by
  obtain ⟨D', V, hD', hD'conv, hV, _, hDV, hVD', hD'O⟩ :=
    exists_convex_transverse_compact_buffer hD hDconv hO hDO
  exact ⟨D', V, hD', hD'conv, hV, hDV, hVD', hD'O⟩

end AutomaticContinuity.ThinRectangleGeometry
