import AutomaticContinuity.CoordinateProductChart
import AutomaticContinuity.FlagHalfCutTrivialCases
import AutomaticContinuity.FiniteFlagCutReduction
import AutomaticContinuity.ThinRectangleProduct

set_option autoImplicit false

/-! # Exhaustive half-cut assembly from the nontrivial product stability result

The zero-coefficient and noncrossing cases are proved directly. The only
displayed input is the concrete nontrivial-cut local stability theorem; its
analytic implementation is supplied separately by the product gluing proof.
-/

noncomputable section

namespace AutomaticContinuity

open Set FlagTotalSpace FlagSectionApproximation FiniteHalfspaceExhaustion

theorem halfCut_of_product_stability
    (hstable : ∀ (n : ℕ) (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b : ℝ)
      (D : Set (CoordinateCutChart.Remaining j)) (C : Set ℂ),
      IsCompact D → Convex ℝ D → IsCompact C → Convex ℝ C →
      (ThinRectangleGeometry.zeroSlice C).Nonempty →
      let e := CoordinateCutChart.homeomorph j a ha b
      let L := e ⁻¹' (D ×ˢ C)
      let K := e ⁻¹' (D ×ˢ (C ∩ {w : ℂ | w.re ≤ 0}))
      ∀ g : FinitePoint n → ℂ × ℂ, HolomorphicNear K g →
        (∀ z ∈ K, (z,g z) ∈ totalSet n) → Approximable K L g →
        ∃ δ : ℝ, 0 < δ ∧ ∀ u : FinitePoint n → ℂ × ℂ,
          HolomorphicNear K u →
          (∀ z ∈ K, euclideanPairNorm (u z-g z) ≤ δ) → Approximable K L u) :
    FiniteFlagHalfCutApproximationStatement := by
  intro n L hL q h U hU hKU hh hadm
  have hempty (he : L ∩ q.halfspace = ∅) : Approximable (L ∩ q.halfspace) L h := by
    rw [he]
    exact approximable_empty L h
  have hself (he : L ∩ q.halfspace = L) : Approximable (L ∩ q.halfspace) L h := by
    rw [he] at hKU hadm ⊢
    exact approximable_self_of_holomorphicNear h ⟨U,hU,hKU,hh⟩ hadm
  by_cases ha : q.coefficient = 0
  · by_cases hb : 0 ≤ q.bound
    · apply hself
      ext z
      simp [CoordinateCut.halfspace, CoordinateCut.value, ha, hb]
    · apply hempty
      ext z
      simp [CoordinateCut.halfspace, CoordinateCut.value, ha, hb]
  obtain ⟨D,C,hD,hDconv,hC,hCconv,hChart⟩ :=
    CoordinateCutChart.exists_product_chart hL q.coordinate q.coefficient ha q.bound
  have hKChart := CoordinateCutChart.halfspace_preimage q ha hChart
  by_cases hslice : (ThinRectangleGeometry.zeroSlice C).Nonempty
  · have hKc : IsCompact (L ∩ q.halfspace) := hL.isCompact.inter_right q.isClosed_halfspace
    have hKconv : Convex ℝ (L ∩ q.halfspace) := hL.convex.inter q.convex_halfspace
    apply approximable_of_convex_local_stability hKc hKconv ?_ h ⟨U,hU,hKU,hh⟩ hadm
    have hs := hstable n q.coordinate q.coefficient ha q.bound D C
      hD hDconv hC hCconv hslice
    dsimp only at hs
    rwa [← hKChart, ← hChart] at hs
  · rcases ThinRectangleGeometry.empty_slice_dichotomy hCconv
      (Set.not_nonempty_iff_eq_empty.mp hslice) with he | hside
    · apply hempty
      rw [hKChart, he]
      simp
    · apply hself
      have he : C ∩ {w : ℂ | w.re ≤ 0} = C := inter_eq_left.mpr hside
      rw [hKChart, he, ← hChart]

end AutomaticContinuity
