import AutomaticContinuity.CoordinateRectangleTransfer
import AutomaticContinuity.ThinRectangleTransferDomains
import AutomaticContinuity.ConvexNeighbourhoodFlagFamily
import AutomaticContinuity.FixedExtendingSection

set_option autoImplicit false

/-!
# Unconditional local stability of approximation for one product half-cut

Every analytic and geometric object is constructed from the actual compact
convex product, its coordinate cut, and an already approximable section.
There are no supplied family, inverse, Runge, splitting, or gluing premises.
-/

noncomputable section

namespace AutomaticContinuity.ProductHalfcutOpenness

open Set FlagTotalSpace FlagSectionApproximation ThinRectangleGeometry

variable {n : ℕ} (j : Fin n) (a : ℂ) (ha : a ≠ 0) (b₀ : ℝ)
variable (D : Set (CoordinateCutChart.Remaining j)) (C : Set ℂ)

local notation "e" => CoordinateCutChart.homeomorph j a ha b₀
local notation "L" => (e) ⁻¹' (Set.prod D C)
local notation "K" => (e) ⁻¹' (Set.prod D (C ∩ (fun z : ℂ => Complex.re z ≤ 0)))

theorem exists_local_stability
    (hD : IsCompact D) (hDconv : Convex ℝ D)
    (hC : IsCompact C) (hCconv : Convex ℝ C)
    (hslice : (zeroSlice C).Nonempty)
    (h : FinitePoint n → Pair) (hhol : HolomorphicNear K h)
    (hadm : ∀ z ∈ K, (z, h z) ∈ totalSet n) (happ : Approximable K L h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : FinitePoint n → Pair,
      HolomorphicNear K u →
      (∀ z ∈ K, euclideanPairNorm (u z - h z) ≤ δ) → Approximable K L u := by
  have hK : IsCompact K := (e).isCompact_preimage.mpr
    (hD.prod (hC.inter_right (isClosed_le Complex.continuous_re continuous_const)))
  have hL : IsCompact L := (e).isCompact_preimage.mpr (hD.prod hC)
  have hKconv : Convex ℝ K := CoordinateCutChart.convex_preimage j a ha b₀
    (hDconv.prod (hCconv.inter ((convex_Iic (0 : ℝ)).linear_preimage Complex.reLm)))
  have hKL : K ⊆ L := fun z hz => ⟨hz.1, hz.2.1⟩
  obtain ⟨Z, hZ, hKZ, hh⟩ := hhol
  have hhK : ContinuousOn h K := hh.continuousOn.mono hKZ
  obtain ⟨B, l, Ω, F, G, hB, hKB, _hBZ, hl, hΩ, hΩB, _hΩadm, hgraph,
    hF, hG, hzero, hGF, _hFG, hmargin⟩ :=
    CompactBaseFlagFamily.exists_neighbourhood_strong_margin_family hK hKconv
      h hZ hKZ hh hadm
  obtain ⟨g, θ, U, V, δA, hU, hLU, hg, hδA, hmarginA, hV, hKV, hVU,
    hVB, hθ, hθeq⟩ := exists_fixed_extending_section hK hL hKL h hhK happ
      hΩ hΩB (fun z hz => hgraph z (hKB hz)) F G hF
      (fun z hz => (hzero z (hKB hz)).2) hGF
  obtain ⟨d⟩ := exists_product_transfer_data hD hDconv hC hCconv hslice
    (hU.preimage (e).symm.continuous) (hV.preimage (e).symm.continuous)
    (U := (e).symm ⁻¹' U) (V := (e).symm ⁻¹' V)
    (fun q hq => hLU (by
      change (e) ((e).symm q) ∈ Set.prod D C
      rw [(e).apply_symm_apply]
      exact hq))
    (fun q hq => hKV (by
      change (e) ((e).symm q) ∈ Set.prod D (C ∩ (fun z : ℂ => z.re ≤ 0))
      rw [(e).apply_symm_apply]
      exact hq))
  have hcompose : ApproximableCompositions K L G := by
    apply FlagApproximationTransfer.approximableCompositions_of_coordinate_rectangle
      j a ha b₀ hK hKconv _ d.base_open d.base_subset_buffer d.buffer_compact
      d.buffer_convex d.left_open d.right_open (half_pos d.eta_pos)
      (show d.eta / 2 ≤ 5 * d.eta / 2 by linarith [d.eta_pos])
      d.bottom_lt_top d.gap_pos d.overlap d.gap_left d.gap_right
      (fun z hz => d.product_cover hz) (fun z hz => d.old_product_subset hz)
      _ _ _ hV hV hVU Subset.rfl _ g θ G hg
      (hG.mono (prod_mono hVB Subset.rfl)) hθ hθeq hδA (sub_pos.mpr hl)
      hmarginA (fun z hz => hmargin z (hVB hz))
    · intro z hz
      have hzre : (e z).2.re ≤ 0 := hz.2.2
      change ((CoordinateCutChart.chart j a ha b₀ z).2).re ≤ 0 at hzre
      rw [CoordinateCutChart.second_re] at hzre
      linarith
    · intro z hz
      simpa using d.right_domain hz
    · intro z hz
      simpa using (d.left_domain hz).2
    · intro z hz
      simpa using (d.buffer_domain hz).2
    · intro q hq
      exact (d.buffer_domain ⟨d.base_subset_buffer hq.1, hq.2⟩).2
  exact exists_approximation_tolerance_of_open_image hK h hhK hΩ
    (fun z hz => hgraph z (hKB hz)) F G hF
    (fun z hz => (hzero z (hKB hz)).2) hGF hcompose

end AutomaticContinuity.ProductHalfcutOpenness
