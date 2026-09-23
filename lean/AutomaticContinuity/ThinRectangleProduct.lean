import AutomaticContinuity.ThinRectangleCaps

set_option autoImplicit false

/-!
# Uniform thin rectangles over a compact parameter set

The generalized tube lemma supplies one base neighbourhood and one planar
buffer before the rectangle is chosen. Thus the same contour works for all
parameters in an actual open neighbourhood of the compact parameter set.
-/

noncomputable section

namespace AutomaticContinuity.ThinRectangleGeometry

open Set Complex RectangleCauchy

theorem zeroSlice_nonempty_of_crossing {C : Set ℂ} (hC : Convex ℝ C)
    {v w : ℂ} (hv : v ∈ C) (hw : w ∈ C) (hvr : v.re ≤ 0) (hwr : 0 ≤ w.re) :
    (zeroSlice C).Nonempty := by
  have hzero : (0 : ℝ) ∈ reLm '' C :=
    (hC.linear_image reLm).ordConnected.out ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ ⟨hvr, hwr⟩
  obtain ⟨z, hz, hzr⟩ := hzero
  exact ⟨z, hz, hzr⟩

/-- If the cutting line misses a convex set, no genuine two-sided enlargement
is needed: the old cap is empty or is the whole set. -/
theorem empty_slice_dichotomy {C : Set ℂ} (hC : Convex ℝ C)
    (hzero : zeroSlice C = ∅) :
    C ∩ {z | z.re ≤ 0} = ∅ ∨ C ⊆ {z | z.re ≤ 0} := by
  classical
  by_cases he : (C ∩ {z | z.re ≤ 0}).Nonempty
  · right
    obtain ⟨v, hv, hvr⟩ := he
    intro w hw
    by_contra hwr
    have hne := zeroSlice_nonempty_of_crossing hC hv hw hvr (le_of_not_ge hwr)
    simp [hzero] at hne
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp he)

theorem exists_buffered_product_caps {P : Type*} [TopologicalSpace P]
    {D : Set P} {C : Set ℂ} {U : Set (P × ℂ)}
    (hD : IsCompact D) (hC : IsCompact C) (hCv : Convex ℝ C)
    (hne : (zeroSlice C).Nonempty) (hU : IsOpen U)
    (hcapU : D ×ˢ (C ∩ {z | z.re ≤ 0}) ⊆ U) :
    ∃ (O : Set P) (η b t δ : ℝ), IsOpen O ∧ D ⊆ O ∧
      0 < η ∧ b < t ∧ 0 < δ ∧
      O ×ˢ closedRectangle (η/2) (5*η/2) b t ⊆ U ∧
      Disjoint (C ∩ {z | z.re ≤ 0}) (closedRectangle (η/2) (5*η/2) b t) ∧
      O ×ˢ leftCap C η ⊆ U ∧ leftCap C η ∪ rightCap C η = C ∧
      leftCap C η ∩ rightCap C η ⊆ openRectangle (η/2) (5*η/2) b t ∧
      (∀ z ∈ leftCap C η, ∀ ζ ∈ rightContour (η/2) (5*η/2) b t, δ ≤ ‖ζ-z‖) ∧
      (∀ z ∈ rightCap C η, ∀ ζ ∈ leftContour (η/2) b t, δ ≤ ‖ζ-z‖) := by
  have hcap : IsCompact (C ∩ {z | z.re ≤ 0}) :=
    hC.inter_right (isClosed_le continuous_re continuous_const)
  obtain ⟨O, V, hO, hV, hDO, hcapV, hOVU⟩ := generalized_tube_lemma hD hcap hU hcapU
  obtain ⟨η, b, t, δ, hη, hbt, hδ, hrect, hdis, hleft, hcover, hoverlap, hgapA, hgapB⟩ :=
    exists_buffered_caps hC hCv hne hV hcapV
  exact ⟨O, η, b, t, δ, hO, hDO, hη, hbt, hδ,
    (prod_mono Subset.rfl hrect).trans hOVU, hdis,
    (prod_mono Subset.rfl hleft).trans hOVU, hcover, hoverlap, hgapA, hgapB⟩

end AutomaticContinuity.ThinRectangleGeometry
